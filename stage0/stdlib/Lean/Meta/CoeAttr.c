// Lean compiler output
// Module: Lean.Meta.CoeAttr
// Imports: public import Lean.Meta.FunInfo
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addImportedGlobals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coe_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coe_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coe_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coe_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coeFun_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coeFun_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coeFun_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coeFun_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coeSort_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coeSort_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coeSort_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coeSort_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_instInhabitedCoeFnType_default;
LEAN_EXPORT uint8_t l_Lean_Meta_instInhabitedCoeFnType;
static const lean_string_object l_Lean_Meta_instReprCoeFnType_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Meta.CoeFnType.coe"};
static const lean_object* l_Lean_Meta_instReprCoeFnType_repr___closed__0 = (const lean_object*)&l_Lean_Meta_instReprCoeFnType_repr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instReprCoeFnType_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCoeFnType_repr___closed__0_value)}};
static const lean_object* l_Lean_Meta_instReprCoeFnType_repr___closed__1 = (const lean_object*)&l_Lean_Meta_instReprCoeFnType_repr___closed__1_value;
static const lean_string_object l_Lean_Meta_instReprCoeFnType_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Meta.CoeFnType.coeFun"};
static const lean_object* l_Lean_Meta_instReprCoeFnType_repr___closed__2 = (const lean_object*)&l_Lean_Meta_instReprCoeFnType_repr___closed__2_value;
static const lean_ctor_object l_Lean_Meta_instReprCoeFnType_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCoeFnType_repr___closed__2_value)}};
static const lean_object* l_Lean_Meta_instReprCoeFnType_repr___closed__3 = (const lean_object*)&l_Lean_Meta_instReprCoeFnType_repr___closed__3_value;
static const lean_string_object l_Lean_Meta_instReprCoeFnType_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Meta.CoeFnType.coeSort"};
static const lean_object* l_Lean_Meta_instReprCoeFnType_repr___closed__4 = (const lean_object*)&l_Lean_Meta_instReprCoeFnType_repr___closed__4_value;
static const lean_ctor_object l_Lean_Meta_instReprCoeFnType_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCoeFnType_repr___closed__4_value)}};
static const lean_object* l_Lean_Meta_instReprCoeFnType_repr___closed__5 = (const lean_object*)&l_Lean_Meta_instReprCoeFnType_repr___closed__5_value;
static lean_once_cell_t l_Lean_Meta_instReprCoeFnType_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprCoeFnType_repr___closed__6;
static lean_once_cell_t l_Lean_Meta_instReprCoeFnType_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprCoeFnType_repr___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCoeFnType_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCoeFnType_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReprCoeFnType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReprCoeFnType_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReprCoeFnType___closed__0 = (const lean_object*)&l_Lean_Meta_instReprCoeFnType___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReprCoeFnType = (const lean_object*)&l_Lean_Meta_instReprCoeFnType___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_CoeFnType_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_instDecidableEqCoeFnType(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_instDecidableEqCoeFnType___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value;
static const lean_string_object l_Lean_Meta_instToExprCoeFnType___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "CoeFnType"};
static const lean_object* l_Lean_Meta_instToExprCoeFnType___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__2_value;
static const lean_string_object l_Lean_Meta_instToExprCoeFnType___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "coe"};
static const lean_object* l_Lean_Meta_instToExprCoeFnType___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Meta_instToExprCoeFnType___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_instToExprCoeFnType___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_instToExprCoeFnType___lam__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(245, 23, 148, 155, 249, 144, 10, 39)}};
static const lean_ctor_object l_Lean_Meta_instToExprCoeFnType___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(180, 95, 244, 188, 147, 48, 65, 174)}};
static const lean_object* l_Lean_Meta_instToExprCoeFnType___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5;
static const lean_string_object l_Lean_Meta_instToExprCoeFnType___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "coeFun"};
static const lean_object* l_Lean_Meta_instToExprCoeFnType___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_Meta_instToExprCoeFnType___lam__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_instToExprCoeFnType___lam__0___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_instToExprCoeFnType___lam__0___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(245, 23, 148, 155, 249, 144, 10, 39)}};
static const lean_ctor_object l_Lean_Meta_instToExprCoeFnType___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__7_value_aux_2),((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(246, 99, 158, 11, 104, 59, 147, 227)}};
static const lean_object* l_Lean_Meta_instToExprCoeFnType___lam__0___closed__7 = (const lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__7_value;
static lean_once_cell_t l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8;
static const lean_string_object l_Lean_Meta_instToExprCoeFnType___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "coeSort"};
static const lean_object* l_Lean_Meta_instToExprCoeFnType___lam__0___closed__9 = (const lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__9_value;
static const lean_ctor_object l_Lean_Meta_instToExprCoeFnType___lam__0___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_instToExprCoeFnType___lam__0___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_instToExprCoeFnType___lam__0___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(245, 23, 148, 155, 249, 144, 10, 39)}};
static const lean_ctor_object l_Lean_Meta_instToExprCoeFnType___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__10_value_aux_2),((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(232, 194, 10, 4, 128, 226, 10, 131)}};
static const lean_object* l_Lean_Meta_instToExprCoeFnType___lam__0___closed__10 = (const lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__10_value;
static lean_once_cell_t l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_instToExprCoeFnType___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_instToExprCoeFnType___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_instToExprCoeFnType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instToExprCoeFnType___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instToExprCoeFnType___closed__0 = (const lean_object*)&l_Lean_Meta_instToExprCoeFnType___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instToExprCoeFnType___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_instToExprCoeFnType___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instToExprCoeFnType___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_instToExprCoeFnType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instToExprCoeFnType___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(245, 23, 148, 155, 249, 144, 10, 39)}};
static const lean_object* l_Lean_Meta_instToExprCoeFnType___closed__1 = (const lean_object*)&l_Lean_Meta_instToExprCoeFnType___closed__1_value;
static lean_once_cell_t l_Lean_Meta_instToExprCoeFnType___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instToExprCoeFnType___closed__2;
static lean_once_cell_t l_Lean_Meta_instToExprCoeFnType___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instToExprCoeFnType___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_instToExprCoeFnType;
static const lean_ctor_object l_Lean_Meta_instInhabitedCoeFnInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_instInhabitedCoeFnInfo_default___closed__0 = (const lean_object*)&l_Lean_Meta_instInhabitedCoeFnInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedCoeFnInfo_default = (const lean_object*)&l_Lean_Meta_instInhabitedCoeFnInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedCoeFnInfo = (const lean_object*)&l_Lean_Meta_instInhabitedCoeFnInfo_default___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_instReprCoeFnInfo_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "numArgs"};
static const lean_object* l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__7;
static const lean_string_object l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__9_value;
static const lean_string_object l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "coercee"};
static const lean_object* l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__10_value)}};
static const lean_object* l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__11_value;
static const lean_string_object l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "type"};
static const lean_object* l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__12_value;
static const lean_ctor_object l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__12_value)}};
static const lean_object* l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__13_value;
static lean_once_cell_t l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__14;
static const lean_string_object l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__15_value;
static lean_once_cell_t l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__16;
static lean_once_cell_t l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__17;
static const lean_ctor_object l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__18 = (const lean_object*)&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__18_value;
static const lean_ctor_object l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__15_value)}};
static const lean_object* l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__19 = (const lean_object*)&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__19_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCoeFnInfo_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCoeFnInfo_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCoeFnInfo_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instReprCoeFnInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instReprCoeFnInfo_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instReprCoeFnInfo___closed__0 = (const lean_object*)&l_Lean_Meta_instReprCoeFnInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instReprCoeFnInfo = (const lean_object*)&l_Lean_Meta_instReprCoeFnInfo___closed__0_value;
static const lean_string_object l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "CoeFnInfo"};
static const lean_object* l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(85, 211, 223, 162, 210, 109, 181, 27)}};
static const lean_ctor_object l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(209, 173, 53, 122, 213, 70, 37, 45)}};
static const lean_object* l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_instToExprCoeFnInfo___lam__0(lean_object*);
static const lean_closure_object l_Lean_Meta_instToExprCoeFnInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instToExprCoeFnInfo___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instToExprCoeFnInfo___closed__0 = (const lean_object*)&l_Lean_Meta_instToExprCoeFnInfo___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instToExprCoeFnInfo___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_instToExprCoeFnInfo___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instToExprCoeFnInfo___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_instToExprCoeFnInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_instToExprCoeFnInfo___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(85, 211, 223, 162, 210, 109, 181, 27)}};
static const lean_object* l_Lean_Meta_instToExprCoeFnInfo___closed__1 = (const lean_object*)&l_Lean_Meta_instToExprCoeFnInfo___closed__1_value;
static lean_once_cell_t l_Lean_Meta_instToExprCoeFnInfo___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instToExprCoeFnInfo___closed__2;
static lean_once_cell_t l_Lean_Meta_instToExprCoeFnInfo___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instToExprCoeFnInfo___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_instToExprCoeFnInfo;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__3_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__3_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "coeExt"};
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 79, 158, 29, 159, 225, 112, 220)}};
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ScopedEnvExtension_addImportedGlobals___boxed, .m_arity = 9, .m_num_fixed = 6, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 8, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coeExt;
LEAN_EXPORT lean_object* l_Lean_Meta_getCoeFnInfo_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCoeFnInfo_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCoeFnInfo_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCoeFnInfo_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Meta_registerCoercion_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Meta_registerCoercion_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_registerCoercion_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_registerCoercion_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__4;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__5 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__5_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__6;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__7 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__7_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__8;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__9 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__9_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__10;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__11 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__11_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__12;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__13 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__13_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__14;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__16;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__17 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__17_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__18;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_registerCoercion___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_registerCoercion___closed__0;
static lean_once_cell_t l_Lean_Meta_registerCoercion___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_registerCoercion___closed__1;
static lean_once_cell_t l_Lean_Meta_registerCoercion___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_registerCoercion___closed__2;
static lean_once_cell_t l_Lean_Meta_registerCoercion___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_registerCoercion___closed__3;
static lean_once_cell_t l_Lean_Meta_registerCoercion___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_registerCoercion___closed__4;
static lean_once_cell_t l_Lean_Meta_registerCoercion___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_registerCoercion___closed__5;
static const lean_string_object l_Lean_Meta_registerCoercion___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = " has no explicit arguments"};
static const lean_object* l_Lean_Meta_registerCoercion___closed__6 = (const lean_object*)&l_Lean_Meta_registerCoercion___closed__6_value;
static lean_once_cell_t l_Lean_Meta_registerCoercion___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_registerCoercion___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_registerCoercion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_registerCoercion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Invalid attribute scope: Attribute `["};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "]` must be global, not `"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "global"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__4_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__5 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__5_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scoped"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__6 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CoeAttr"};
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(249, 40, 50, 44, 170, 71, 213, 72)}};
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(220, 223, 198, 95, 71, 43, 10, 230)}};
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 176, 35, 194, 129, 55, 168, 146)}};
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(21, 214, 201, 90, 143, 177, 215, 199)}};
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(60, 220, 254, 67, 198, 119, 37, 106)}};
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(53, 213, 132, 134, 15, 63, 153, 28)}};
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 171, 90, 220, 0, 49, 132, 175)}};
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(12, 81, 197, 78, 222, 140, 1, 234)}};
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 123, 148, 227, 200, 81, 222, 71)}};
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(242, 142, 190, 13, 107, 23, 245, 249)}};
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2____boxed, .m_arity = 9, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Adds a definition as a coercion"};
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lean_Meta_CoeFnType_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Meta_CoeFnType_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Lean_Meta_CoeFnType_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coe_elim___redArg(lean_object* v_coe_22_){
_start:
{
lean_inc(v_coe_22_);
return v_coe_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coe_elim___redArg___boxed(lean_object* v_coe_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Meta_CoeFnType_coe_elim___redArg(v_coe_23_);
lean_dec(v_coe_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coe_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_coe_28_){
_start:
{
lean_inc(v_coe_28_);
return v_coe_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coe_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_coe_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lean_Meta_CoeFnType_coe_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_coe_32_);
lean_dec(v_coe_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coeFun_elim___redArg(lean_object* v_coeFun_35_){
_start:
{
lean_inc(v_coeFun_35_);
return v_coeFun_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coeFun_elim___redArg___boxed(lean_object* v_coeFun_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Meta_CoeFnType_coeFun_elim___redArg(v_coeFun_36_);
lean_dec(v_coeFun_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coeFun_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_coeFun_41_){
_start:
{
lean_inc(v_coeFun_41_);
return v_coeFun_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coeFun_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_coeFun_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lean_Meta_CoeFnType_coeFun_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_coeFun_45_);
lean_dec(v_coeFun_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coeSort_elim___redArg(lean_object* v_coeSort_48_){
_start:
{
lean_inc(v_coeSort_48_);
return v_coeSort_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coeSort_elim___redArg___boxed(lean_object* v_coeSort_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Meta_CoeFnType_coeSort_elim___redArg(v_coeSort_49_);
lean_dec(v_coeSort_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coeSort_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_coeSort_54_){
_start:
{
lean_inc(v_coeSort_54_);
return v_coeSort_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coeSort_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_coeSort_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Lean_Meta_CoeFnType_coeSort_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_coeSort_58_);
lean_dec(v_coeSort_58_);
return v_res_60_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedCoeFnType_default(void){
_start:
{
uint8_t v___x_61_; 
v___x_61_ = 0;
return v___x_61_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedCoeFnType(void){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
static lean_object* _init_l_Lean_Meta_instReprCoeFnType_repr___closed__6(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lean_unsigned_to_nat(2u);
v___x_73_ = lean_nat_to_int(v___x_72_);
return v___x_73_;
}
}
static lean_object* _init_l_Lean_Meta_instReprCoeFnType_repr___closed__7(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_unsigned_to_nat(1u);
v___x_75_ = lean_nat_to_int(v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCoeFnType_repr(uint8_t v_x_76_, lean_object* v_prec_77_){
_start:
{
lean_object* v___y_79_; lean_object* v___y_86_; lean_object* v___y_93_; 
switch(v_x_76_)
{
case 0:
{
lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_99_ = lean_unsigned_to_nat(1024u);
v___x_100_ = lean_nat_dec_le(v___x_99_, v_prec_77_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; 
v___x_101_ = lean_obj_once(&l_Lean_Meta_instReprCoeFnType_repr___closed__6, &l_Lean_Meta_instReprCoeFnType_repr___closed__6_once, _init_l_Lean_Meta_instReprCoeFnType_repr___closed__6);
v___y_79_ = v___x_101_;
goto v___jp_78_;
}
else
{
lean_object* v___x_102_; 
v___x_102_ = lean_obj_once(&l_Lean_Meta_instReprCoeFnType_repr___closed__7, &l_Lean_Meta_instReprCoeFnType_repr___closed__7_once, _init_l_Lean_Meta_instReprCoeFnType_repr___closed__7);
v___y_79_ = v___x_102_;
goto v___jp_78_;
}
}
case 1:
{
lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_103_ = lean_unsigned_to_nat(1024u);
v___x_104_ = lean_nat_dec_le(v___x_103_, v_prec_77_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_once(&l_Lean_Meta_instReprCoeFnType_repr___closed__6, &l_Lean_Meta_instReprCoeFnType_repr___closed__6_once, _init_l_Lean_Meta_instReprCoeFnType_repr___closed__6);
v___y_86_ = v___x_105_;
goto v___jp_85_;
}
else
{
lean_object* v___x_106_; 
v___x_106_ = lean_obj_once(&l_Lean_Meta_instReprCoeFnType_repr___closed__7, &l_Lean_Meta_instReprCoeFnType_repr___closed__7_once, _init_l_Lean_Meta_instReprCoeFnType_repr___closed__7);
v___y_86_ = v___x_106_;
goto v___jp_85_;
}
}
default: 
{
lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_107_ = lean_unsigned_to_nat(1024u);
v___x_108_ = lean_nat_dec_le(v___x_107_, v_prec_77_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; 
v___x_109_ = lean_obj_once(&l_Lean_Meta_instReprCoeFnType_repr___closed__6, &l_Lean_Meta_instReprCoeFnType_repr___closed__6_once, _init_l_Lean_Meta_instReprCoeFnType_repr___closed__6);
v___y_93_ = v___x_109_;
goto v___jp_92_;
}
else
{
lean_object* v___x_110_; 
v___x_110_ = lean_obj_once(&l_Lean_Meta_instReprCoeFnType_repr___closed__7, &l_Lean_Meta_instReprCoeFnType_repr___closed__7_once, _init_l_Lean_Meta_instReprCoeFnType_repr___closed__7);
v___y_93_ = v___x_110_;
goto v___jp_92_;
}
}
}
v___jp_78_:
{
lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_80_ = ((lean_object*)(l_Lean_Meta_instReprCoeFnType_repr___closed__1));
lean_inc(v___y_79_);
v___x_81_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_81_, 0, v___y_79_);
lean_ctor_set(v___x_81_, 1, v___x_80_);
v___x_82_ = 0;
v___x_83_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_83_, 0, v___x_81_);
lean_ctor_set_uint8(v___x_83_, sizeof(void*)*1, v___x_82_);
v___x_84_ = l_Repr_addAppParen(v___x_83_, v_prec_77_);
return v___x_84_;
}
v___jp_85_:
{
lean_object* v___x_87_; lean_object* v___x_88_; uint8_t v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_87_ = ((lean_object*)(l_Lean_Meta_instReprCoeFnType_repr___closed__3));
lean_inc(v___y_86_);
v___x_88_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_88_, 0, v___y_86_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
v___x_89_ = 0;
v___x_90_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_90_, 0, v___x_88_);
lean_ctor_set_uint8(v___x_90_, sizeof(void*)*1, v___x_89_);
v___x_91_ = l_Repr_addAppParen(v___x_90_, v_prec_77_);
return v___x_91_;
}
v___jp_92_:
{
lean_object* v___x_94_; lean_object* v___x_95_; uint8_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_94_ = ((lean_object*)(l_Lean_Meta_instReprCoeFnType_repr___closed__5));
lean_inc(v___y_93_);
v___x_95_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_95_, 0, v___y_93_);
lean_ctor_set(v___x_95_, 1, v___x_94_);
v___x_96_ = 0;
v___x_97_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_97_, 0, v___x_95_);
lean_ctor_set_uint8(v___x_97_, sizeof(void*)*1, v___x_96_);
v___x_98_ = l_Repr_addAppParen(v___x_97_, v_prec_77_);
return v___x_98_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCoeFnType_repr___boxed(lean_object* v_x_111_, lean_object* v_prec_112_){
_start:
{
uint8_t v_x_171__boxed_113_; lean_object* v_res_114_; 
v_x_171__boxed_113_ = lean_unbox(v_x_111_);
v_res_114_ = l_Lean_Meta_instReprCoeFnType_repr(v_x_171__boxed_113_, v_prec_112_);
lean_dec(v_prec_112_);
return v_res_114_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_CoeFnType_ofNat(lean_object* v_n_117_){
_start:
{
lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = lean_unsigned_to_nat(0u);
v___x_119_ = lean_nat_dec_le(v_n_117_, v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_120_ = lean_unsigned_to_nat(1u);
v___x_121_ = lean_nat_dec_le(v_n_117_, v___x_120_);
if (v___x_121_ == 0)
{
uint8_t v___x_122_; 
v___x_122_ = 2;
return v___x_122_;
}
else
{
uint8_t v___x_123_; 
v___x_123_ = 1;
return v___x_123_;
}
}
else
{
uint8_t v___x_124_; 
v___x_124_ = 0;
return v___x_124_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_ofNat___boxed(lean_object* v_n_125_){
_start:
{
uint8_t v_res_126_; lean_object* v_r_127_; 
v_res_126_ = l_Lean_Meta_CoeFnType_ofNat(v_n_125_);
lean_dec(v_n_125_);
v_r_127_ = lean_box(v_res_126_);
return v_r_127_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instDecidableEqCoeFnType(uint8_t v_x_128_, uint8_t v_y_129_){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_130_ = lean_box(v_x_128_);
v___x_131_ = lean_obj_tag_nat(v___x_130_);
lean_dec(v___x_130_);
v___x_132_ = lean_box(v_y_129_);
v___x_133_ = lean_obj_tag_nat(v___x_132_);
lean_dec(v___x_132_);
v___x_134_ = lean_nat_dec_eq(v___x_131_, v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instDecidableEqCoeFnType___boxed(lean_object* v_x_135_, lean_object* v_y_136_){
_start:
{
uint8_t v_x_23__boxed_137_; uint8_t v_y_24__boxed_138_; uint8_t v_res_139_; lean_object* v_r_140_; 
v_x_23__boxed_137_ = lean_unbox(v_x_135_);
v_y_24__boxed_138_ = lean_unbox(v_y_136_);
v_res_139_ = l_Lean_Meta_instDecidableEqCoeFnType(v_x_23__boxed_137_, v_y_24__boxed_138_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
static lean_object* _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_150_ = lean_box(0);
v___x_151_ = ((lean_object*)(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__4));
v___x_152_ = l_Lean_mkConst(v___x_151_, v___x_150_);
return v___x_152_;
}
}
static lean_object* _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_159_ = lean_box(0);
v___x_160_ = ((lean_object*)(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__7));
v___x_161_ = l_Lean_mkConst(v___x_160_, v___x_159_);
return v___x_161_;
}
}
static lean_object* _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = lean_box(0);
v___x_169_ = ((lean_object*)(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__10));
v___x_170_ = l_Lean_mkConst(v___x_169_, v___x_168_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instToExprCoeFnType___lam__0(uint8_t v_x_171_){
_start:
{
switch(v_x_171_)
{
case 0:
{
lean_object* v___x_172_; 
v___x_172_ = lean_obj_once(&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5, &l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5_once, _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5);
return v___x_172_;
}
case 1:
{
lean_object* v___x_173_; 
v___x_173_ = lean_obj_once(&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8, &l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8_once, _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8);
return v___x_173_;
}
default: 
{
lean_object* v___x_174_; 
v___x_174_ = lean_obj_once(&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11, &l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11_once, _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11);
return v___x_174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instToExprCoeFnType___lam__0___boxed(lean_object* v_x_175_){
_start:
{
uint8_t v_x_156__boxed_176_; lean_object* v_res_177_; 
v_x_156__boxed_176_ = lean_unbox(v_x_175_);
v_res_177_ = l_Lean_Meta_instToExprCoeFnType___lam__0(v_x_156__boxed_176_);
return v_res_177_;
}
}
static lean_object* _init_l_Lean_Meta_instToExprCoeFnType___closed__2(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_183_ = lean_box(0);
v___x_184_ = ((lean_object*)(l_Lean_Meta_instToExprCoeFnType___closed__1));
v___x_185_ = l_Lean_mkConst(v___x_184_, v___x_183_);
return v___x_185_;
}
}
static lean_object* _init_l_Lean_Meta_instToExprCoeFnType___closed__3(void){
_start:
{
lean_object* v___x_186_; lean_object* v___f_187_; lean_object* v___x_188_; 
v___x_186_ = lean_obj_once(&l_Lean_Meta_instToExprCoeFnType___closed__2, &l_Lean_Meta_instToExprCoeFnType___closed__2_once, _init_l_Lean_Meta_instToExprCoeFnType___closed__2);
v___f_187_ = ((lean_object*)(l_Lean_Meta_instToExprCoeFnType___closed__0));
v___x_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_188_, 0, v___f_187_);
lean_ctor_set(v___x_188_, 1, v___x_186_);
return v___x_188_;
}
}
static lean_object* _init_l_Lean_Meta_instToExprCoeFnType(void){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = lean_obj_once(&l_Lean_Meta_instToExprCoeFnType___closed__3, &l_Lean_Meta_instToExprCoeFnType___closed__3_once, _init_l_Lean_Meta_instToExprCoeFnType___closed__3);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_instReprCoeFnInfo_repr_spec__0(lean_object* v_a_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = lean_nat_to_int(v_a_195_);
return v___x_196_;
}
}
static lean_object* _init_l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = lean_unsigned_to_nat(11u);
v___x_211_ = lean_nat_to_int(v___x_210_);
return v___x_211_;
}
}
static lean_object* _init_l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_unsigned_to_nat(8u);
v___x_222_ = lean_nat_to_int(v___x_221_);
return v___x_222_;
}
}
static lean_object* _init_l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = ((lean_object*)(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__0));
v___x_225_ = lean_string_length(v___x_224_);
return v___x_225_;
}
}
static lean_object* _init_l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_obj_once(&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__16, &l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__16_once, _init_l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__16);
v___x_227_ = lean_nat_to_int(v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCoeFnInfo_repr___redArg(lean_object* v_x_232_){
_start:
{
lean_object* v_numArgs_233_; lean_object* v_coercee_234_; uint8_t v_type_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v_numArgs_233_ = lean_ctor_get(v_x_232_, 0);
lean_inc(v_numArgs_233_);
v_coercee_234_ = lean_ctor_get(v_x_232_, 1);
lean_inc(v_coercee_234_);
v_type_235_ = lean_ctor_get_uint8(v_x_232_, sizeof(void*)*2);
lean_dec_ref(v_x_232_);
v___x_236_ = ((lean_object*)(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__5));
v___x_237_ = ((lean_object*)(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__6));
v___x_238_ = lean_obj_once(&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__7, &l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__7_once, _init_l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__7);
v___x_239_ = l_Nat_reprFast(v_numArgs_233_);
v___x_240_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
v___x_241_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_238_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
v___x_242_ = 0;
v___x_243_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_243_, 0, v___x_241_);
lean_ctor_set_uint8(v___x_243_, sizeof(void*)*1, v___x_242_);
v___x_244_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_237_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = ((lean_object*)(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__9));
v___x_246_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_244_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
v___x_247_ = lean_box(1);
v___x_248_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_246_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v___x_249_ = ((lean_object*)(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__11));
v___x_250_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_248_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
v___x_251_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set(v___x_251_, 1, v___x_236_);
v___x_252_ = l_Nat_reprFast(v_coercee_234_);
v___x_253_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
v___x_254_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_238_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set_uint8(v___x_255_, sizeof(void*)*1, v___x_242_);
v___x_256_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_251_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
lean_ctor_set(v___x_257_, 1, v___x_245_);
v___x_258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
lean_ctor_set(v___x_258_, 1, v___x_247_);
v___x_259_ = ((lean_object*)(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__13));
v___x_260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_258_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
v___x_261_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v___x_236_);
v___x_262_ = lean_obj_once(&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__14, &l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__14_once, _init_l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__14);
v___x_263_ = lean_unsigned_to_nat(0u);
v___x_264_ = l_Lean_Meta_instReprCoeFnType_repr(v_type_235_, v___x_263_);
v___x_265_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_262_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___x_266_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set_uint8(v___x_266_, sizeof(void*)*1, v___x_242_);
v___x_267_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_261_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
v___x_268_ = lean_obj_once(&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__17, &l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__17_once, _init_l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__17);
v___x_269_ = ((lean_object*)(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__18));
v___x_270_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set(v___x_270_, 1, v___x_267_);
v___x_271_ = ((lean_object*)(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__19));
v___x_272_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_270_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
v___x_273_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_268_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
v___x_274_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_274_, 0, v___x_273_);
lean_ctor_set_uint8(v___x_274_, sizeof(void*)*1, v___x_242_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCoeFnInfo_repr(lean_object* v_x_275_, lean_object* v_prec_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l_Lean_Meta_instReprCoeFnInfo_repr___redArg(v_x_275_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCoeFnInfo_repr___boxed(lean_object* v_x_278_, lean_object* v_prec_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Meta_instReprCoeFnInfo_repr(v_x_278_, v_prec_279_);
lean_dec(v_prec_279_);
return v_res_280_;
}
}
static lean_object* _init_l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__3(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_290_ = lean_box(0);
v___x_291_ = ((lean_object*)(l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__2));
v___x_292_ = l_Lean_mkConst(v___x_291_, v___x_290_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instToExprCoeFnInfo___lam__0(lean_object* v_x_293_){
_start:
{
lean_object* v_numArgs_294_; lean_object* v_coercee_295_; uint8_t v_type_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v_numArgs_294_ = lean_ctor_get(v_x_293_, 0);
lean_inc(v_numArgs_294_);
v_coercee_295_ = lean_ctor_get(v_x_293_, 1);
lean_inc(v_coercee_295_);
v_type_296_ = lean_ctor_get_uint8(v_x_293_, sizeof(void*)*2);
lean_dec_ref(v_x_293_);
v___x_297_ = lean_obj_once(&l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__3, &l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__3_once, _init_l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__3);
v___x_298_ = l_Lean_mkNatLit(v_numArgs_294_);
v___x_299_ = l_Lean_mkNatLit(v_coercee_295_);
switch(v_type_296_)
{
case 0:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = lean_obj_once(&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5, &l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5_once, _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5);
v___x_301_ = l_Lean_mkApp3(v___x_297_, v___x_298_, v___x_299_, v___x_300_);
return v___x_301_;
}
case 1:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_obj_once(&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8, &l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8_once, _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8);
v___x_303_ = l_Lean_mkApp3(v___x_297_, v___x_298_, v___x_299_, v___x_302_);
return v___x_303_;
}
default: 
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_obj_once(&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11, &l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11_once, _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11);
v___x_305_ = l_Lean_mkApp3(v___x_297_, v___x_298_, v___x_299_, v___x_304_);
return v___x_305_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_instToExprCoeFnInfo___closed__2(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = lean_box(0);
v___x_312_ = ((lean_object*)(l_Lean_Meta_instToExprCoeFnInfo___closed__1));
v___x_313_ = l_Lean_mkConst(v___x_312_, v___x_311_);
return v___x_313_;
}
}
static lean_object* _init_l_Lean_Meta_instToExprCoeFnInfo___closed__3(void){
_start:
{
lean_object* v___x_314_; lean_object* v___f_315_; lean_object* v___x_316_; 
v___x_314_ = lean_obj_once(&l_Lean_Meta_instToExprCoeFnInfo___closed__2, &l_Lean_Meta_instToExprCoeFnInfo___closed__2_once, _init_l_Lean_Meta_instToExprCoeFnInfo___closed__2);
v___f_315_ = ((lean_object*)(l_Lean_Meta_instToExprCoeFnInfo___closed__0));
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v___f_315_);
lean_ctor_set(v___x_316_, 1, v___x_314_);
return v___x_316_;
}
}
static lean_object* _init_l_Lean_Meta_instToExprCoeFnInfo(void){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = lean_obj_once(&l_Lean_Meta_instToExprCoeFnInfo___closed__3, &l_Lean_Meta_instToExprCoeFnInfo___closed__3_once, _init_l_Lean_Meta_instToExprCoeFnInfo___closed__3);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(lean_object* v___y_318_){
_start:
{
lean_inc(v___y_318_);
return v___y_318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed(lean_object* v___y_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(v___y_319_);
lean_dec(v___y_319_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(lean_object* v_x_321_, lean_object* v_a_322_, lean_object* v___y_323_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v_a_322_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed(lean_object* v_x_326_, lean_object* v_a_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(v_x_326_, v_a_327_, v___y_328_);
lean_dec_ref(v___y_328_);
lean_dec(v_x_326_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(lean_object* v_x_331_, lean_object* v_a_332_){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_333_, 0, v_a_332_);
lean_inc_ref_n(v___x_333_, 2);
v___x_334_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
lean_ctor_set(v___x_334_, 2, v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed(lean_object* v_x_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(v_x_335_, v_a_336_);
lean_dec_ref(v_x_335_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__3_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(lean_object* v_st_338_, lean_object* v_x_339_){
_start:
{
lean_object* v_fst_340_; lean_object* v_snd_341_; lean_object* v___x_342_; 
v_fst_340_ = lean_ctor_get(v_x_339_, 0);
lean_inc(v_fst_340_);
v_snd_341_ = lean_ctor_get(v_x_339_, 1);
lean_inc(v_snd_341_);
lean_dec_ref(v_x_339_);
v___x_342_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_340_, v_snd_341_, v_st_338_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(lean_object* v___x_343_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_345_, 0, v___x_343_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed(lean_object* v___x_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(v___x_346_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_));
v___x_375_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed(lean_object* v_a_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_();
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCoeFnInfo_x3f___redArg(lean_object* v_fn_378_, lean_object* v_a_379_){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v_env_383_; lean_object* v___x_384_; lean_object* v_ext_385_; lean_object* v_toEnvExtension_386_; lean_object* v_asyncMode_387_; uint8_t v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_381_ = lean_box(1);
v___x_382_ = lean_st_ref_get(v_a_379_);
v_env_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc_ref(v_env_383_);
lean_dec(v___x_382_);
v___x_384_ = l_Lean_Meta_coeExt;
v_ext_385_ = lean_ctor_get(v___x_384_, 1);
v_toEnvExtension_386_ = lean_ctor_get(v_ext_385_, 0);
v_asyncMode_387_ = lean_ctor_get(v_toEnvExtension_386_, 2);
v___x_388_ = 0;
v___x_389_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_381_, v___x_384_, v_env_383_, v_asyncMode_387_, v___x_388_);
v___x_390_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_389_, v_fn_378_);
lean_dec(v___x_389_);
v___x_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCoeFnInfo_x3f___redArg___boxed(lean_object* v_fn_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_Meta_getCoeFnInfo_x3f___redArg(v_fn_392_, v_a_393_);
lean_dec(v_a_393_);
lean_dec(v_fn_392_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCoeFnInfo_x3f(lean_object* v_fn_396_, lean_object* v_a_397_, lean_object* v_a_398_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_Meta_getCoeFnInfo_x3f___redArg(v_fn_396_, v_a_398_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCoeFnInfo_x3f___boxed(lean_object* v_fn_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_Meta_getCoeFnInfo_x3f(v_fn_401_, v_a_402_, v_a_403_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
lean_dec(v_fn_401_);
return v_res_405_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_406_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0_spec__0___redArg___closed__0);
v___x_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0_spec__0___redArg(){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0_spec__0___redArg___closed__1);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0_spec__0___redArg___boxed(lean_object* v___dummy_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0_spec__0___redArg();
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Meta_registerCoercion_spec__2(lean_object* v_as_413_, lean_object* v_j_414_){
_start:
{
lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_415_ = lean_array_get_size(v_as_413_);
v___x_416_ = lean_nat_dec_lt(v_j_414_, v___x_415_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; 
lean_dec(v_j_414_);
v___x_417_ = lean_box(0);
return v___x_417_;
}
else
{
lean_object* v___x_418_; uint8_t v_binderInfo_419_; uint8_t v___x_420_; 
v___x_418_ = lean_array_fget_borrowed(v_as_413_, v_j_414_);
v_binderInfo_419_ = lean_ctor_get_uint8(v___x_418_, sizeof(void*)*1);
v___x_420_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_419_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = lean_unsigned_to_nat(1u);
v___x_422_ = lean_nat_add(v_j_414_, v___x_421_);
lean_dec(v_j_414_);
v_j_414_ = v___x_422_;
goto _start;
}
else
{
lean_object* v___x_424_; 
v___x_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_424_, 0, v_j_414_);
return v___x_424_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Meta_registerCoercion_spec__2___boxed(lean_object* v_as_425_, lean_object* v_j_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Array_findIdx_x3f_loop___at___00Lean_Meta_registerCoercion_spec__2(v_as_425_, v_j_426_);
lean_dec_ref(v_as_425_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_registerCoercion_spec__3_spec__6(lean_object* v_msgData_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v___x_434_; lean_object* v_env_435_; uint8_t v___x_436_; lean_object* v_env_437_; lean_object* v___x_438_; lean_object* v_toCold_439_; lean_object* v_mctx_440_; lean_object* v_lctx_441_; lean_object* v_options_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_434_ = lean_st_ref_get(v___y_432_);
v_env_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc_ref(v_env_435_);
lean_dec(v___x_434_);
v___x_436_ = 0;
v_env_437_ = l_Lean_Environment_setRecordingDeps(v_env_435_, v___x_436_);
v___x_438_ = lean_st_ref_get(v___y_430_);
v_toCold_439_ = lean_ctor_get(v___y_431_, 0);
v_mctx_440_ = lean_ctor_get(v___x_438_, 0);
lean_inc_ref(v_mctx_440_);
lean_dec(v___x_438_);
v_lctx_441_ = lean_ctor_get(v___y_429_, 2);
v_options_442_ = lean_ctor_get(v_toCold_439_, 2);
lean_inc_ref(v_options_442_);
lean_inc_ref(v_lctx_441_);
v___x_443_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_443_, 0, v_env_437_);
lean_ctor_set(v___x_443_, 1, v_mctx_440_);
lean_ctor_set(v___x_443_, 2, v_lctx_441_);
lean_ctor_set(v___x_443_, 3, v_options_442_);
v___x_444_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v_msgData_428_);
v___x_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_registerCoercion_spec__3_spec__6___boxed(lean_object* v_msgData_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_registerCoercion_spec__3_spec__6(v_msgData_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__3___redArg(lean_object* v_msg_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_ref_459_; lean_object* v___x_460_; lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_469_; 
v_ref_459_ = lean_ctor_get(v___y_456_, 2);
v___x_460_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_registerCoercion_spec__3_spec__6(v_msg_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
v_a_461_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_469_ == 0)
{
v___x_463_ = v___x_460_;
v_isShared_464_ = v_isSharedCheck_469_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_460_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_469_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_465_; lean_object* v___x_467_; 
lean_inc(v_ref_459_);
v___x_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_465_, 0, v_ref_459_);
lean_ctor_set(v___x_465_, 1, v_a_461_);
if (v_isShared_464_ == 0)
{
lean_ctor_set_tag(v___x_463_, 1);
lean_ctor_set(v___x_463_, 0, v___x_465_);
v___x_467_ = v___x_463_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_465_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__3___redArg___boxed(lean_object* v_msg_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__3___redArg(v_msg_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__11___redArg(lean_object* v_ref_477_, lean_object* v_msg_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v_toCold_484_; lean_object* v_currRecDepth_485_; lean_object* v_ref_486_; uint16_t v_optionFlags_487_; uint8_t v_suppressElabErrors_488_; uint8_t v_checkDeprecated_489_; uint8_t v_isRecordingDeps_490_; lean_object* v_ref_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v_toCold_484_ = lean_ctor_get(v___y_481_, 0);
v_currRecDepth_485_ = lean_ctor_get(v___y_481_, 1);
v_ref_486_ = lean_ctor_get(v___y_481_, 2);
v_optionFlags_487_ = lean_ctor_get_uint16(v___y_481_, sizeof(void*)*3);
v_suppressElabErrors_488_ = lean_ctor_get_uint8(v___y_481_, sizeof(void*)*3 + 2);
v_checkDeprecated_489_ = lean_ctor_get_uint8(v___y_481_, sizeof(void*)*3 + 3);
v_isRecordingDeps_490_ = lean_ctor_get_uint8(v___y_481_, sizeof(void*)*3 + 4);
v_ref_491_ = l_Lean_replaceRef(v_ref_477_, v_ref_486_);
lean_inc(v_currRecDepth_485_);
lean_inc_ref(v_toCold_484_);
v___x_492_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_492_, 0, v_toCold_484_);
lean_ctor_set(v___x_492_, 1, v_currRecDepth_485_);
lean_ctor_set(v___x_492_, 2, v_ref_491_);
lean_ctor_set_uint16(v___x_492_, sizeof(void*)*3, v_optionFlags_487_);
lean_ctor_set_uint8(v___x_492_, sizeof(void*)*3 + 2, v_suppressElabErrors_488_);
lean_ctor_set_uint8(v___x_492_, sizeof(void*)*3 + 3, v_checkDeprecated_489_);
lean_ctor_set_uint8(v___x_492_, sizeof(void*)*3 + 4, v_isRecordingDeps_490_);
v___x_493_ = l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__3___redArg(v_msg_478_, v___y_479_, v___y_480_, v___x_492_, v___y_482_);
lean_dec_ref_known(v___x_492_, 3);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__11___redArg___boxed(lean_object* v_ref_494_, lean_object* v_msg_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__11___redArg(v_ref_494_, v_msg_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v_ref_494_);
return v_res_501_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0_spec__0___redArg___closed__0);
v___x_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__1(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_504_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__0);
v___x_505_ = lean_unsigned_to_nat(0u);
v___x_506_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
lean_ctor_set(v___x_506_, 2, v___x_505_);
lean_ctor_set(v___x_506_, 3, v___x_505_);
lean_ctor_set(v___x_506_, 4, v___x_504_);
lean_ctor_set(v___x_506_, 5, v___x_504_);
lean_ctor_set(v___x_506_, 6, v___x_504_);
lean_ctor_set(v___x_506_, 7, v___x_504_);
lean_ctor_set(v___x_506_, 8, v___x_504_);
lean_ctor_set(v___x_506_, 9, v___x_504_);
lean_ctor_set(v___x_506_, 10, v___x_504_);
return v___x_506_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_507_ = lean_unsigned_to_nat(32u);
v___x_508_ = lean_mk_empty_array_with_capacity(v___x_507_);
v___x_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
return v___x_509_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__3(void){
_start:
{
size_t v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_510_ = ((size_t)5ULL);
v___x_511_ = lean_unsigned_to_nat(0u);
v___x_512_ = lean_unsigned_to_nat(32u);
v___x_513_ = lean_mk_empty_array_with_capacity(v___x_512_);
v___x_514_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__2);
v___x_515_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_515_, 0, v___x_514_);
lean_ctor_set(v___x_515_, 1, v___x_513_);
lean_ctor_set(v___x_515_, 2, v___x_511_);
lean_ctor_set(v___x_515_, 3, v___x_511_);
lean_ctor_set_usize(v___x_515_, 4, v___x_510_);
return v___x_515_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__4(void){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_516_ = lean_box(1);
v___x_517_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__3);
v___x_518_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__0);
v___x_519_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
lean_ctor_set(v___x_519_, 1, v___x_517_);
lean_ctor_set(v___x_519_, 2, v___x_516_);
return v___x_519_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__6(void){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__5));
v___x_522_ = l_Lean_stringToMessageData(v___x_521_);
return v___x_522_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__8(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__7));
v___x_525_ = l_Lean_stringToMessageData(v___x_524_);
return v___x_525_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__10(void){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__9));
v___x_528_ = l_Lean_stringToMessageData(v___x_527_);
return v___x_528_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__12(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__11));
v___x_531_ = l_Lean_stringToMessageData(v___x_530_);
return v___x_531_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__14(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__13));
v___x_534_ = l_Lean_stringToMessageData(v___x_533_);
return v___x_534_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__16(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__15));
v___x_537_ = l_Lean_stringToMessageData(v___x_536_);
return v___x_537_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__18(void){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__17));
v___x_540_ = l_Lean_stringToMessageData(v___x_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg(lean_object* v_msg_541_, lean_object* v_declHint_542_, lean_object* v___y_543_){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v_env_547_; uint8_t v___x_548_; 
v___x_545_ = lean_box(0);
v___x_546_ = lean_st_ref_get(v___y_543_);
v_env_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc_ref(v_env_547_);
lean_dec(v___x_546_);
v___x_548_ = l_Lean_Name_isAnonymous(v_declHint_542_);
if (v___x_548_ == 0)
{
uint8_t v_isExporting_549_; 
v_isExporting_549_ = lean_ctor_get_uint8(v_env_547_, sizeof(void*)*13);
if (v_isExporting_549_ == 0)
{
lean_object* v___x_550_; 
lean_dec_ref(v_env_547_);
lean_dec(v_declHint_542_);
v___x_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_550_, 0, v_msg_541_);
return v___x_550_;
}
else
{
lean_object* v___x_551_; uint8_t v___x_552_; 
lean_inc_ref(v_env_547_);
v___x_551_ = l_Lean_Environment_setExporting(v_env_547_, v___x_548_);
lean_inc(v_declHint_542_);
lean_inc_ref(v___x_551_);
v___x_552_ = l_Lean_Environment_contains(v___x_551_, v_declHint_542_, v_isExporting_549_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; 
lean_dec_ref(v___x_551_);
lean_dec_ref(v_env_547_);
lean_dec(v_declHint_542_);
v___x_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_553_, 0, v_msg_541_);
return v___x_553_;
}
else
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v_c_559_; lean_object* v___x_560_; 
v___x_554_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__1);
v___x_555_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__4);
v___x_556_ = l_Lean_Options_empty;
lean_inc_ref(v___x_551_);
v___x_557_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_557_, 0, v___x_551_);
lean_ctor_set(v___x_557_, 1, v___x_554_);
lean_ctor_set(v___x_557_, 2, v___x_555_);
lean_ctor_set(v___x_557_, 3, v___x_556_);
lean_inc(v_declHint_542_);
v___x_558_ = l_Lean_MessageData_ofConstName(v_declHint_542_, v___x_548_);
v_c_559_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_559_, 0, v___x_557_);
lean_ctor_set(v_c_559_, 1, v___x_558_);
v___x_560_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_551_, v_declHint_542_);
lean_dec_ref(v___x_551_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
lean_dec_ref(v_env_547_);
lean_dec(v_declHint_542_);
v___x_561_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__6);
v___x_562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
lean_ctor_set(v___x_562_, 1, v_c_559_);
v___x_563_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__8);
v___x_564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_562_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
v___x_565_ = l_Lean_MessageData_note(v___x_564_);
v___x_566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_566_, 0, v_msg_541_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
v___x_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
return v___x_567_;
}
else
{
lean_object* v_val_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_602_; 
v_val_568_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_602_ == 0)
{
v___x_570_ = v___x_560_;
v_isShared_571_ = v_isSharedCheck_602_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_val_568_);
lean_dec(v___x_560_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_602_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v_moduleNames_573_; lean_object* v_mod_574_; uint8_t v___x_575_; 
v___x_572_ = l_Lean_Environment_header(v_env_547_);
lean_dec_ref(v_env_547_);
v_moduleNames_573_ = lean_ctor_get(v___x_572_, 4);
lean_inc_ref(v_moduleNames_573_);
lean_dec_ref(v___x_572_);
v_mod_574_ = lean_array_get(v___x_545_, v_moduleNames_573_, v_val_568_);
lean_dec(v_val_568_);
lean_dec_ref(v_moduleNames_573_);
v___x_575_ = l_Lean_isPrivateName(v_declHint_542_);
lean_dec(v_declHint_542_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_587_; 
v___x_576_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__10);
v___x_577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v_c_559_);
v___x_578_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__12);
v___x_579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_577_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v___x_580_ = l_Lean_MessageData_ofName(v_mod_574_);
v___x_581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_579_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__14);
v___x_583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_581_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
v___x_584_ = l_Lean_MessageData_note(v___x_583_);
v___x_585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_585_, 0, v_msg_541_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
if (v_isShared_571_ == 0)
{
lean_ctor_set_tag(v___x_570_, 0);
lean_ctor_set(v___x_570_, 0, v___x_585_);
v___x_587_ = v___x_570_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_585_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
else
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_589_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__6);
v___x_590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
lean_ctor_set(v___x_590_, 1, v_c_559_);
v___x_591_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__16);
v___x_592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_590_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
v___x_593_ = l_Lean_MessageData_ofName(v_mod_574_);
v___x_594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_592_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
v___x_595_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__18);
v___x_596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_594_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = l_Lean_MessageData_note(v___x_596_);
v___x_598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_598_, 0, v_msg_541_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
if (v_isShared_571_ == 0)
{
lean_ctor_set_tag(v___x_570_, 0);
lean_ctor_set(v___x_570_, 0, v___x_598_);
v___x_600_ = v___x_570_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_598_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_603_; 
lean_dec_ref(v_env_547_);
lean_dec(v_declHint_542_);
v___x_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_603_, 0, v_msg_541_);
return v___x_603_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___boxed(lean_object* v_msg_604_, lean_object* v_declHint_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg(v_msg_604_, v_declHint_605_, v___y_606_);
lean_dec(v___y_606_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10(lean_object* v_msg_609_, lean_object* v_declHint_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v___x_616_; lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_626_; 
v___x_616_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg(v_msg_609_, v_declHint_610_, v___y_614_);
v_a_617_ = lean_ctor_get(v___x_616_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_626_ == 0)
{
v___x_619_ = v___x_616_;
v_isShared_620_ = v_isSharedCheck_626_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_616_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_626_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_621_ = l_Lean_unknownIdentifierMessageTag;
v___x_622_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
lean_ctor_set(v___x_622_, 1, v_a_617_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v___x_622_);
v___x_624_ = v___x_619_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10___boxed(lean_object* v_msg_627_, lean_object* v_declHint_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10(v_msg_627_, v_declHint_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9___redArg(lean_object* v_ref_635_, lean_object* v_msg_636_, lean_object* v_declHint_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v___x_643_; lean_object* v_a_644_; lean_object* v___x_645_; 
v___x_643_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10(v_msg_636_, v_declHint_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
v_a_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_a_644_);
lean_dec_ref(v___x_643_);
v___x_645_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__11___redArg(v_ref_635_, v_a_644_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9___redArg___boxed(lean_object* v_ref_646_, lean_object* v_msg_647_, lean_object* v_declHint_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9___redArg(v_ref_646_, v_msg_647_, v_declHint_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v_ref_646_);
return v_res_654_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7___redArg___closed__0));
v___x_657_ = l_Lean_stringToMessageData(v___x_656_);
return v___x_657_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7___redArg___closed__2));
v___x_660_ = l_Lean_stringToMessageData(v___x_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7___redArg(lean_object* v_ref_661_, lean_object* v_constName_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v___x_668_; uint8_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_668_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7___redArg___closed__1);
v___x_669_ = 0;
lean_inc(v_constName_662_);
v___x_670_ = l_Lean_MessageData_ofConstName(v_constName_662_, v___x_669_);
v___x_671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_668_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7___redArg___closed__3);
v___x_673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_671_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9___redArg(v_ref_661_, v___x_673_, v_constName_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7___redArg___boxed(lean_object* v_ref_675_, lean_object* v_constName_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7___redArg(v_ref_675_, v_constName_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v_ref_675_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3___redArg(lean_object* v_constName_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_ref_689_; lean_object* v___x_690_; 
v_ref_689_ = lean_ctor_get(v___y_686_, 2);
v___x_690_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7___redArg(v_ref_689_, v_constName_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_constName_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3___redArg(v_constName_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2(lean_object* v_constName_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v___x_704_; lean_object* v_env_705_; uint8_t v___x_706_; lean_object* v___x_707_; 
v___x_704_ = lean_st_ref_get(v___y_702_);
v_env_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc_ref(v_env_705_);
lean_dec(v___x_704_);
v___x_706_ = 0;
lean_inc(v_constName_698_);
v___x_707_ = l_Lean_Environment_findConstVal_x3f(v_env_705_, v_constName_698_, v___x_706_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v___x_708_; 
v___x_708_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3___redArg(v_constName_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
return v___x_708_;
}
else
{
lean_object* v_val_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_dec(v_constName_698_);
v_val_709_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_707_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_val_709_);
lean_dec(v___x_707_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
lean_ctor_set_tag(v___x_711_, 0);
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_val_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2___boxed(lean_object* v_constName_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2(v_constName_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__3(lean_object* v_a_724_, lean_object* v_a_725_){
_start:
{
if (lean_obj_tag(v_a_724_) == 0)
{
lean_object* v___x_726_; 
v___x_726_ = l_List_reverse___redArg(v_a_725_);
return v___x_726_;
}
else
{
lean_object* v_head_727_; lean_object* v_tail_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_737_; 
v_head_727_ = lean_ctor_get(v_a_724_, 0);
v_tail_728_ = lean_ctor_get(v_a_724_, 1);
v_isSharedCheck_737_ = !lean_is_exclusive(v_a_724_);
if (v_isSharedCheck_737_ == 0)
{
v___x_730_ = v_a_724_;
v_isShared_731_ = v_isSharedCheck_737_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_tail_728_);
lean_inc(v_head_727_);
lean_dec(v_a_724_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_737_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; lean_object* v___x_734_; 
v___x_732_ = l_Lean_mkLevelParam(v_head_727_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 1, v_a_725_);
lean_ctor_set(v___x_730_, 0, v___x_732_);
v___x_734_ = v___x_730_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_732_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v_a_725_);
v___x_734_ = v_reuseFailAlloc_736_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
v_a_724_ = v_tail_728_;
v_a_725_ = v___x_734_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1(lean_object* v_constName_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v___x_744_; 
lean_inc(v_constName_738_);
v___x_744_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2(v_constName_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_756_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_756_ == 0)
{
v___x_747_ = v___x_744_;
v_isShared_748_ = v_isSharedCheck_756_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_744_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_756_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v_levelParams_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_754_; 
v_levelParams_749_ = lean_ctor_get(v_a_745_, 1);
lean_inc(v_levelParams_749_);
lean_dec(v_a_745_);
v___x_750_ = lean_box(0);
v___x_751_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__3(v_levelParams_749_, v___x_750_);
v___x_752_ = l_Lean_mkConst(v_constName_738_, v___x_751_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 0, v___x_752_);
v___x_754_ = v___x_747_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_752_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
else
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
lean_dec(v_constName_738_);
v_a_757_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___x_744_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_744_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_a_757_);
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
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1___boxed(lean_object* v_constName_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1(v_constName_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
return v_res_771_;
}
}
static lean_object* _init_l_Lean_Meta_registerCoercion___closed__0(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0_spec__0___redArg___closed__0);
v___x_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
return v___x_773_;
}
}
static lean_object* _init_l_Lean_Meta_registerCoercion___closed__1(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = lean_obj_once(&l_Lean_Meta_registerCoercion___closed__0, &l_Lean_Meta_registerCoercion___closed__0_once, _init_l_Lean_Meta_registerCoercion___closed__0);
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
return v___x_775_;
}
}
static lean_object* _init_l_Lean_Meta_registerCoercion___closed__2(void){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0_spec__0___redArg();
return v___x_776_;
}
}
static lean_object* _init_l_Lean_Meta_registerCoercion___closed__3(void){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = lean_obj_once(&l_Lean_Meta_registerCoercion___closed__0, &l_Lean_Meta_registerCoercion___closed__0_once, _init_l_Lean_Meta_registerCoercion___closed__0);
v___x_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
return v___x_778_;
}
}
static lean_object* _init_l_Lean_Meta_registerCoercion___closed__4(void){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_779_ = lean_unsigned_to_nat(0u);
v___x_780_ = lean_obj_once(&l_Lean_Meta_registerCoercion___closed__0, &l_Lean_Meta_registerCoercion___closed__0_once, _init_l_Lean_Meta_registerCoercion___closed__0);
v___x_781_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
lean_ctor_set(v___x_781_, 2, v___x_779_);
return v___x_781_;
}
}
static lean_object* _init_l_Lean_Meta_registerCoercion___closed__5(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_782_ = lean_obj_once(&l_Lean_Meta_registerCoercion___closed__4, &l_Lean_Meta_registerCoercion___closed__4_once, _init_l_Lean_Meta_registerCoercion___closed__4);
v___x_783_ = lean_obj_once(&l_Lean_Meta_registerCoercion___closed__3, &l_Lean_Meta_registerCoercion___closed__3_once, _init_l_Lean_Meta_registerCoercion___closed__3);
v___x_784_ = lean_obj_once(&l_Lean_Meta_registerCoercion___closed__0, &l_Lean_Meta_registerCoercion___closed__0_once, _init_l_Lean_Meta_registerCoercion___closed__0);
v___x_785_ = lean_obj_once(&l_Lean_Meta_registerCoercion___closed__2, &l_Lean_Meta_registerCoercion___closed__2_once, _init_l_Lean_Meta_registerCoercion___closed__2);
v___x_786_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
lean_ctor_set(v___x_786_, 1, v___x_784_);
lean_ctor_set(v___x_786_, 2, v___x_783_);
lean_ctor_set(v___x_786_, 3, v___x_784_);
lean_ctor_set(v___x_786_, 4, v___x_784_);
lean_ctor_set(v___x_786_, 5, v___x_784_);
lean_ctor_set(v___x_786_, 6, v___x_784_);
lean_ctor_set(v___x_786_, 7, v___x_782_);
return v___x_786_;
}
}
static lean_object* _init_l_Lean_Meta_registerCoercion___closed__7(void){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = ((lean_object*)(l_Lean_Meta_registerCoercion___closed__6));
v___x_789_ = l_Lean_stringToMessageData(v___x_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerCoercion(lean_object* v_name_790_, lean_object* v_info_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_){
_start:
{
lean_object* v_info_798_; lean_object* v___y_799_; lean_object* v___y_800_; 
if (lean_obj_tag(v_info_791_) == 0)
{
lean_object* v___x_841_; 
lean_inc(v_name_790_);
v___x_841_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1(v_name_790_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_a_842_);
lean_dec_ref_known(v___x_841_, 1);
v___x_843_ = lean_box(0);
v___x_844_ = l_Lean_Meta_getFunInfo(v_a_842_, v___x_843_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v_paramInfo_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_871_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_a_845_);
lean_dec_ref_known(v___x_844_, 1);
v_paramInfo_846_ = lean_ctor_get(v_a_845_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v_a_845_);
if (v_isSharedCheck_871_ == 0)
{
lean_object* v_unused_872_; 
v_unused_872_ = lean_ctor_get(v_a_845_, 1);
lean_dec(v_unused_872_);
v___x_848_ = v_a_845_;
v_isShared_849_ = v_isSharedCheck_871_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_paramInfo_846_);
lean_dec(v_a_845_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_871_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = lean_unsigned_to_nat(0u);
v___x_851_ = l_Array_findIdx_x3f_loop___at___00Lean_Meta_registerCoercion_spec__2(v_paramInfo_846_, v___x_850_);
lean_dec_ref(v_paramInfo_846_);
if (lean_obj_tag(v___x_851_) == 1)
{
lean_object* v_val_852_; lean_object* v___x_853_; lean_object* v___x_854_; uint8_t v___x_855_; lean_object* v___x_856_; 
lean_del_object(v___x_848_);
v_val_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_val_852_);
lean_dec_ref_known(v___x_851_, 1);
v___x_853_ = lean_unsigned_to_nat(1u);
v___x_854_ = lean_nat_add(v_val_852_, v___x_853_);
v___x_855_ = 0;
v___x_856_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_856_, 0, v___x_854_);
lean_ctor_set(v___x_856_, 1, v_val_852_);
lean_ctor_set_uint8(v___x_856_, sizeof(void*)*2, v___x_855_);
v_info_798_ = v___x_856_;
v___y_799_ = v_a_793_;
v___y_800_ = v_a_795_;
goto v___jp_797_;
}
else
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_860_; 
lean_dec(v___x_851_);
v___x_857_ = l_Lean_MessageData_ofName(v_name_790_);
v___x_858_ = lean_obj_once(&l_Lean_Meta_registerCoercion___closed__7, &l_Lean_Meta_registerCoercion___closed__7_once, _init_l_Lean_Meta_registerCoercion___closed__7);
if (v_isShared_849_ == 0)
{
lean_ctor_set_tag(v___x_848_, 7);
lean_ctor_set(v___x_848_, 1, v___x_858_);
lean_ctor_set(v___x_848_, 0, v___x_857_);
v___x_860_ = v___x_848_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v___x_858_);
v___x_860_ = v_reuseFailAlloc_870_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_861_; lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
v___x_861_ = l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__3___redArg(v___x_860_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
v_a_862_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_861_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_861_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
lean_dec(v_name_790_);
v_a_873_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_844_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_844_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
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
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
lean_dec(v_name_790_);
v_a_881_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_841_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_841_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
else
{
lean_object* v_val_889_; 
v_val_889_ = lean_ctor_get(v_info_791_, 0);
lean_inc(v_val_889_);
lean_dec_ref_known(v_info_791_, 1);
v_info_798_ = v_val_889_;
v___y_799_ = v_a_793_;
v___y_800_ = v_a_795_;
goto v___jp_797_;
}
v___jp_797_:
{
lean_object* v___x_801_; lean_object* v_env_802_; lean_object* v_nextMacroScope_803_; lean_object* v_ngen_804_; lean_object* v_auxDeclNGen_805_; lean_object* v_traceState_806_; lean_object* v_recordedDeps_807_; lean_object* v_messages_808_; lean_object* v_infoState_809_; lean_object* v_snapshotTasks_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_839_; 
v___x_801_ = lean_st_ref_take(v___y_800_);
v_env_802_ = lean_ctor_get(v___x_801_, 0);
v_nextMacroScope_803_ = lean_ctor_get(v___x_801_, 1);
v_ngen_804_ = lean_ctor_get(v___x_801_, 2);
v_auxDeclNGen_805_ = lean_ctor_get(v___x_801_, 3);
v_traceState_806_ = lean_ctor_get(v___x_801_, 4);
v_recordedDeps_807_ = lean_ctor_get(v___x_801_, 6);
v_messages_808_ = lean_ctor_get(v___x_801_, 7);
v_infoState_809_ = lean_ctor_get(v___x_801_, 8);
v_snapshotTasks_810_ = lean_ctor_get(v___x_801_, 9);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_839_ == 0)
{
lean_object* v_unused_840_; 
v_unused_840_ = lean_ctor_get(v___x_801_, 5);
lean_dec(v_unused_840_);
v___x_812_ = v___x_801_;
v_isShared_813_ = v_isSharedCheck_839_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_snapshotTasks_810_);
lean_inc(v_infoState_809_);
lean_inc(v_messages_808_);
lean_inc(v_recordedDeps_807_);
lean_inc(v_traceState_806_);
lean_inc(v_auxDeclNGen_805_);
lean_inc(v_ngen_804_);
lean_inc(v_nextMacroScope_803_);
lean_inc(v_env_802_);
lean_dec(v___x_801_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_839_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_819_; 
v___x_814_ = l_Lean_Meta_coeExt;
v___x_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_815_, 0, v_name_790_);
lean_ctor_set(v___x_815_, 1, v_info_798_);
v___x_816_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v___x_814_, v_env_802_, v___x_815_);
v___x_817_ = lean_obj_once(&l_Lean_Meta_registerCoercion___closed__1, &l_Lean_Meta_registerCoercion___closed__1_once, _init_l_Lean_Meta_registerCoercion___closed__1);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 5, v___x_817_);
lean_ctor_set(v___x_812_, 0, v___x_816_);
v___x_819_ = v___x_812_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v_nextMacroScope_803_);
lean_ctor_set(v_reuseFailAlloc_838_, 2, v_ngen_804_);
lean_ctor_set(v_reuseFailAlloc_838_, 3, v_auxDeclNGen_805_);
lean_ctor_set(v_reuseFailAlloc_838_, 4, v_traceState_806_);
lean_ctor_set(v_reuseFailAlloc_838_, 5, v___x_817_);
lean_ctor_set(v_reuseFailAlloc_838_, 6, v_recordedDeps_807_);
lean_ctor_set(v_reuseFailAlloc_838_, 7, v_messages_808_);
lean_ctor_set(v_reuseFailAlloc_838_, 8, v_infoState_809_);
lean_ctor_set(v_reuseFailAlloc_838_, 9, v_snapshotTasks_810_);
v___x_819_ = v_reuseFailAlloc_838_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v_mctx_822_; lean_object* v_zetaDeltaFVarIds_823_; lean_object* v_postponed_824_; lean_object* v_diag_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_836_; 
v___x_820_ = lean_st_ref_put(v___y_800_, v___x_819_);
v___x_821_ = lean_st_ref_take(v___y_799_);
v_mctx_822_ = lean_ctor_get(v___x_821_, 0);
v_zetaDeltaFVarIds_823_ = lean_ctor_get(v___x_821_, 2);
v_postponed_824_ = lean_ctor_get(v___x_821_, 3);
v_diag_825_ = lean_ctor_get(v___x_821_, 4);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_836_ == 0)
{
lean_object* v_unused_837_; 
v_unused_837_ = lean_ctor_get(v___x_821_, 1);
lean_dec(v_unused_837_);
v___x_827_ = v___x_821_;
v_isShared_828_ = v_isSharedCheck_836_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_diag_825_);
lean_inc(v_postponed_824_);
lean_inc(v_zetaDeltaFVarIds_823_);
lean_inc(v_mctx_822_);
lean_dec(v___x_821_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_836_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_832_; 
v___x_829_ = lean_box(0);
v___x_830_ = lean_obj_once(&l_Lean_Meta_registerCoercion___closed__5, &l_Lean_Meta_registerCoercion___closed__5_once, _init_l_Lean_Meta_registerCoercion___closed__5);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 1, v___x_830_);
v___x_832_ = v___x_827_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_mctx_822_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v___x_830_);
lean_ctor_set(v_reuseFailAlloc_835_, 2, v_zetaDeltaFVarIds_823_);
lean_ctor_set(v_reuseFailAlloc_835_, 3, v_postponed_824_);
lean_ctor_set(v_reuseFailAlloc_835_, 4, v_diag_825_);
v___x_832_ = v_reuseFailAlloc_835_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = lean_st_ref_put(v___y_799_, v___x_832_);
v___x_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_829_);
return v___x_834_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerCoercion___boxed(lean_object* v_name_890_, lean_object* v_info_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Lean_Meta_registerCoercion(v_name_890_, v_info_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0_spec__0(lean_object* v_00_u03b2_898_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = lean_obj_once(&l_Lean_Meta_registerCoercion___closed__2, &l_Lean_Meta_registerCoercion___closed__2_once, _init_l_Lean_Meta_registerCoercion___closed__2);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0___redArg(){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = lean_obj_once(&l_Lean_Meta_registerCoercion___closed__2, &l_Lean_Meta_registerCoercion___closed__2_once, _init_l_Lean_Meta_registerCoercion___closed__2);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0___redArg___boxed(lean_object* v___dummy_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0___redArg();
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0(lean_object* v_00_u03b2_904_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = lean_obj_once(&l_Lean_Meta_registerCoercion___closed__2, &l_Lean_Meta_registerCoercion___closed__2_once, _init_l_Lean_Meta_registerCoercion___closed__2);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__3(lean_object* v_00_u03b1_906_, lean_object* v_msg_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__3___redArg(v_msg_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__3___boxed(lean_object* v_00_u03b1_914_, lean_object* v_msg_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__3(v_00_u03b1_914_, v_msg_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_922_, lean_object* v_constName_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3___redArg(v_constName_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_930_, lean_object* v_constName_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3(v_00_u03b1_930_, v_constName_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7(lean_object* v_00_u03b1_938_, lean_object* v_ref_939_, lean_object* v_constName_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7___redArg(v_ref_939_, v_constName_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7___boxed(lean_object* v_00_u03b1_947_, lean_object* v_ref_948_, lean_object* v_constName_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7(v_00_u03b1_947_, v_ref_948_, v_constName_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v_ref_948_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9(lean_object* v_00_u03b1_956_, lean_object* v_ref_957_, lean_object* v_msg_958_, lean_object* v_declHint_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9___redArg(v_ref_957_, v_msg_958_, v_declHint_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9___boxed(lean_object* v_00_u03b1_966_, lean_object* v_ref_967_, lean_object* v_msg_968_, lean_object* v_declHint_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9(v_00_u03b1_966_, v_ref_967_, v_msg_968_, v_declHint_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v_ref_967_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11(lean_object* v_msg_976_, lean_object* v_declHint_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg(v_msg_976_, v_declHint_977_, v___y_981_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___boxed(lean_object* v_msg_984_, lean_object* v_declHint_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11(v_msg_984_, v_declHint_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__11(lean_object* v_00_u03b1_992_, lean_object* v_ref_993_, lean_object* v_msg_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__11___redArg(v_ref_993_, v_msg_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__11___boxed(lean_object* v_00_u03b1_1001_, lean_object* v_ref_1002_, lean_object* v_msg_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__11(v_00_u03b1_1001_, v_ref_1002_, v_msg_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v_ref_1002_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(lean_object* v_decl_1010_, lean_object* v_____r_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = lean_box(0);
v___x_1018_ = l_Lean_Meta_registerCoercion(v_decl_1010_, v___x_1017_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2____boxed(lean_object* v_decl_1019_, lean_object* v_____r_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(v_decl_1019_, v_____r_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
return v_res_1026_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__0));
v___x_1029_ = l_Lean_stringToMessageData(v___x_1028_);
return v___x_1029_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__2));
v___x_1032_ = l_Lean_stringToMessageData(v___x_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg(lean_object* v_name_1036_, uint8_t v_kind_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___y_1049_; 
v___x_1043_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__1);
v___x_1044_ = l_Lean_MessageData_ofName(v_name_1036_);
v___x_1045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1043_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v___x_1046_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__3);
v___x_1047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1045_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
switch(v_kind_1037_)
{
case 0:
{
lean_object* v___x_1056_; 
v___x_1056_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__4));
v___y_1049_ = v___x_1056_;
goto v___jp_1048_;
}
case 1:
{
lean_object* v___x_1057_; 
v___x_1057_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__5));
v___y_1049_ = v___x_1057_;
goto v___jp_1048_;
}
default: 
{
lean_object* v___x_1058_; 
v___x_1058_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__6));
v___y_1049_ = v___x_1058_;
goto v___jp_1048_;
}
}
v___jp_1048_:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
lean_inc_ref(v___y_1049_);
v___x_1050_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1050_, 0, v___y_1049_);
v___x_1051_ = l_Lean_MessageData_ofFormat(v___x_1050_);
v___x_1052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1047_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7___redArg___closed__3);
v___x_1054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__3___redArg(v___x_1054_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
return v___x_1055_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_name_1059_, lean_object* v_kind_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
uint8_t v_kind_boxed_1066_; lean_object* v_res_1067_; 
v_kind_boxed_1066_ = lean_unbox(v_kind_1060_);
v_res_1067_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg(v_name_1059_, v_kind_boxed_1066_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
return v_res_1067_;
}
}
static uint64_t _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1074_; uint64_t v___x_1075_; 
v___x_1074_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_));
v___x_1075_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1074_);
return v___x_1075_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1076_ = lean_uint64_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1077_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_));
v___x_1078_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
lean_ctor_set_uint64(v___x_1078_, sizeof(void*)*1, v___x_1076_);
return v___x_1078_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_registerCoercion_spec__0_spec__0___redArg___closed__0);
v___x_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
return v___x_1080_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
return v___x_1082_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1084_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
lean_ctor_set(v___x_1084_, 2, v___x_1083_);
lean_ctor_set(v___x_1084_, 3, v___x_1083_);
lean_ctor_set(v___x_1084_, 4, v___x_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(lean_object* v___x_1085_, lean_object* v___x_1086_, lean_object* v___x_1087_, lean_object* v_decl_1088_, lean_object* v___stx_1089_, uint8_t v_kind_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
uint8_t v___x_1094_; uint8_t v___x_1095_; uint8_t v___x_1096_; uint8_t v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; size_t v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___y_1119_; 
v___x_1094_ = 0;
v___x_1095_ = l_Lean_instBEqAttributeKind_beq(v_kind_1090_, v___x_1094_);
v___x_1096_ = 1;
v___x_1097_ = 0;
v___x_1098_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1099_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1100_ = lean_unsigned_to_nat(32u);
v___x_1101_ = lean_mk_empty_array_with_capacity(v___x_1100_);
v___x_1102_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__2);
v___x_1103_ = ((size_t)5ULL);
lean_inc_n(v___x_1085_, 7);
v___x_1104_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1104_, 0, v___x_1102_);
lean_ctor_set(v___x_1104_, 1, v___x_1101_);
lean_ctor_set(v___x_1104_, 2, v___x_1085_);
lean_ctor_set(v___x_1104_, 3, v___x_1085_);
lean_ctor_set_usize(v___x_1104_, 4, v___x_1103_);
v___x_1105_ = lean_box(1);
lean_inc_ref(v___x_1104_);
v___x_1106_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1099_);
lean_ctor_set(v___x_1106_, 1, v___x_1104_);
lean_ctor_set(v___x_1106_, 2, v___x_1105_);
v___x_1107_ = lean_mk_empty_array_with_capacity(v___x_1085_);
v___x_1108_ = lean_box(0);
lean_inc(v___x_1086_);
v___x_1109_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1109_, 0, v___x_1098_);
lean_ctor_set(v___x_1109_, 1, v___x_1086_);
lean_ctor_set(v___x_1109_, 2, v___x_1106_);
lean_ctor_set(v___x_1109_, 3, v___x_1107_);
lean_ctor_set(v___x_1109_, 4, v___x_1108_);
lean_ctor_set(v___x_1109_, 5, v___x_1085_);
lean_ctor_set(v___x_1109_, 6, v___x_1108_);
lean_ctor_set_uint8(v___x_1109_, sizeof(void*)*7, v___x_1097_);
lean_ctor_set_uint8(v___x_1109_, sizeof(void*)*7 + 1, v___x_1097_);
lean_ctor_set_uint8(v___x_1109_, sizeof(void*)*7 + 2, v___x_1097_);
lean_ctor_set_uint8(v___x_1109_, sizeof(void*)*7 + 3, v___x_1096_);
v___x_1110_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1085_);
lean_ctor_set(v___x_1110_, 1, v___x_1085_);
lean_ctor_set(v___x_1110_, 2, v___x_1085_);
lean_ctor_set(v___x_1110_, 3, v___x_1085_);
lean_ctor_set(v___x_1110_, 4, v___x_1099_);
lean_ctor_set(v___x_1110_, 5, v___x_1099_);
lean_ctor_set(v___x_1110_, 6, v___x_1099_);
lean_ctor_set(v___x_1110_, 7, v___x_1099_);
lean_ctor_set(v___x_1110_, 8, v___x_1099_);
lean_ctor_set(v___x_1110_, 9, v___x_1099_);
lean_ctor_set(v___x_1110_, 10, v___x_1099_);
v___x_1111_ = lean_obj_once(&l_Lean_Meta_registerCoercion___closed__2, &l_Lean_Meta_registerCoercion___closed__2_once, _init_l_Lean_Meta_registerCoercion___closed__2);
v___x_1112_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1113_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1099_);
lean_ctor_set(v___x_1113_, 1, v___x_1099_);
lean_ctor_set(v___x_1113_, 2, v___x_1085_);
v___x_1114_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1111_);
lean_ctor_set(v___x_1114_, 1, v___x_1099_);
lean_ctor_set(v___x_1114_, 2, v___x_1112_);
lean_ctor_set(v___x_1114_, 3, v___x_1099_);
lean_ctor_set(v___x_1114_, 4, v___x_1099_);
lean_ctor_set(v___x_1114_, 5, v___x_1099_);
lean_ctor_set(v___x_1114_, 6, v___x_1099_);
lean_ctor_set(v___x_1114_, 7, v___x_1113_);
v___x_1115_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1110_);
lean_ctor_set(v___x_1116_, 1, v___x_1114_);
lean_ctor_set(v___x_1116_, 2, v___x_1086_);
lean_ctor_set(v___x_1116_, 3, v___x_1104_);
lean_ctor_set(v___x_1116_, 4, v___x_1115_);
v___x_1117_ = lean_st_mk_ref(v___x_1116_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1129_; 
lean_dec(v_decl_1088_);
v___x_1129_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg(v___x_1087_, v_kind_1090_, v___x_1109_, v___x_1117_, v___y_1091_, v___y_1092_);
lean_dec(v___x_1117_);
lean_dec_ref_known(v___x_1109_, 7);
return v___x_1129_;
}
else
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
lean_dec(v___x_1087_);
v___x_1130_ = lean_box(0);
v___x_1131_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(v_decl_1088_, v___x_1130_, v___x_1109_, v___x_1117_, v___y_1091_, v___y_1092_);
lean_dec_ref_known(v___x_1109_, 7);
v___y_1119_ = v___x_1131_;
goto v___jp_1118_;
}
v___jp_1118_:
{
if (lean_obj_tag(v___y_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1128_; 
v_a_1120_ = lean_ctor_get(v___y_1119_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___y_1119_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1122_ = v___y_1119_;
v_isShared_1123_ = v_isSharedCheck_1128_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___y_1119_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1128_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1124_; lean_object* v___x_1126_; 
v___x_1124_ = lean_st_ref_get(v___x_1117_);
lean_dec(v___x_1117_);
lean_dec(v___x_1124_);
if (v_isShared_1123_ == 0)
{
v___x_1126_ = v___x_1122_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1120_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
else
{
lean_dec(v___x_1117_);
return v___y_1119_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2____boxed(lean_object* v___x_1132_, lean_object* v___x_1133_, lean_object* v___x_1134_, lean_object* v_decl_1135_, lean_object* v___stx_1136_, lean_object* v_kind_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
uint8_t v_kind_boxed_1141_; lean_object* v_res_1142_; 
v_kind_boxed_1141_ = lean_unbox(v_kind_1137_);
v_res_1142_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(v___x_1132_, v___x_1133_, v___x_1134_, v_decl_1135_, v___stx_1136_, v_kind_boxed_1141_, v___y_1138_, v___y_1139_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v___stx_1136_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v___x_1147_; lean_object* v_toCold_1148_; lean_object* v_env_1149_; lean_object* v_options_1150_; uint8_t v___x_1151_; lean_object* v_env_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1147_ = lean_st_ref_get(v___y_1145_);
v_toCold_1148_ = lean_ctor_get(v___y_1144_, 0);
v_env_1149_ = lean_ctor_get(v___x_1147_, 0);
lean_inc_ref(v_env_1149_);
lean_dec(v___x_1147_);
v_options_1150_ = lean_ctor_get(v_toCold_1148_, 2);
v___x_1151_ = 0;
v_env_1152_ = l_Lean_Environment_setRecordingDeps(v_env_1149_, v___x_1151_);
v___x_1153_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__1);
v___x_1154_ = lean_unsigned_to_nat(32u);
v___x_1155_ = lean_mk_empty_array_with_capacity(v___x_1154_);
lean_dec_ref(v___x_1155_);
v___x_1156_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__1_spec__2_spec__3_spec__7_spec__9_spec__10_spec__11___redArg___closed__4);
lean_inc_ref(v_options_1150_);
v___x_1157_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1157_, 0, v_env_1152_);
lean_ctor_set(v___x_1157_, 1, v___x_1153_);
lean_ctor_set(v___x_1157_, 2, v___x_1156_);
lean_ctor_set(v___x_1157_, 3, v_options_1150_);
v___x_1158_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
lean_ctor_set(v___x_1158_, 1, v_msgData_1143_);
v___x_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0_spec__0(v_msgData_1160_, v___y_1161_, v___y_1162_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v_ref_1169_; lean_object* v___x_1170_; lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1179_; 
v_ref_1169_ = lean_ctor_get(v___y_1166_, 2);
v___x_1170_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0_spec__0(v_msg_1165_, v___y_1166_, v___y_1167_);
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1173_ = v___x_1170_;
v_isShared_1174_ = v_isSharedCheck_1179_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1170_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1179_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1175_; lean_object* v___x_1177_; 
lean_inc(v_ref_1169_);
v___x_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1175_, 0, v_ref_1169_);
lean_ctor_set(v___x_1175_, 1, v_a_1171_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set_tag(v___x_1173_, 1);
lean_ctor_set(v___x_1173_, 0, v___x_1175_);
v___x_1177_ = v___x_1173_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1175_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0___redArg(v_msg_1180_, v___y_1181_, v___y_1182_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
return v_res_1184_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_));
v___x_1187_ = l_Lean_stringToMessageData(v___x_1186_);
return v___x_1187_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_));
v___x_1190_ = l_Lean_stringToMessageData(v___x_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(lean_object* v___x_1191_, lean_object* v_decl_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1196_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1197_ = l_Lean_MessageData_ofName(v___x_1191_);
v___x_1198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1196_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
v___x_1199_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1198_);
lean_ctor_set(v___x_1200_, 1, v___x_1199_);
v___x_1201_ = l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0___redArg(v___x_1200_, v___y_1193_, v___y_1194_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2____boxed(lean_object* v___x_1202_, lean_object* v_decl_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(v___x_1202_, v_decl_1203_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v_decl_1203_);
return v_res_1207_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1248_ = lean_unsigned_to_nat(3842861879u);
v___x_1249_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_));
v___x_1250_ = l_Lean_Name_num___override(v___x_1249_, v___x_1248_);
return v___x_1250_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1252_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_));
v___x_1253_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1254_ = l_Lean_Name_str___override(v___x_1253_, v___x_1252_);
return v___x_1254_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1256_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_));
v___x_1257_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1258_ = l_Lean_Name_str___override(v___x_1257_, v___x_1256_);
return v___x_1258_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1259_ = lean_unsigned_to_nat(2u);
v___x_1260_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1261_ = l_Lean_Name_num___override(v___x_1260_, v___x_1259_);
return v___x_1261_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1271_ = 0;
v___x_1272_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_));
v___x_1273_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_));
v___x_1274_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1275_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1275_, 0, v___x_1274_);
lean_ctor_set(v___x_1275_, 1, v___x_1273_);
lean_ctor_set(v___x_1275_, 2, v___x_1272_);
lean_ctor_set_uint8(v___x_1275_, sizeof(void*)*3, v___x_1271_);
return v___x_1275_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1276_; lean_object* v___f_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___f_1276_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_));
v___f_1277_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_));
v___x_1278_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1279_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
lean_ctor_set(v___x_1279_, 1, v___f_1277_);
lean_ctor_set(v___x_1279_, 2, v___f_1276_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1282_ = l_Lean_registerBuiltinAttribute(v___x_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2____boxed(lean_object* v_a_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_();
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1285_, lean_object* v_msg_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0___redArg(v_msg_1286_, v___y_1287_, v___y_1288_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1291_, lean_object* v_msg_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0(v_00_u03b1_1291_, v_msg_1292_, v___y_1293_, v___y_1294_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b1_1297_, lean_object* v_name_1298_, uint8_t v_kind_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg(v_name_1298_, v_kind_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b1_1306_, lean_object* v_name_1307_, lean_object* v_kind_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
uint8_t v_kind_boxed_1314_; lean_object* v_res_1315_; 
v_kind_boxed_1314_ = lean_unbox(v_kind_1308_);
v_res_1315_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1(v_00_u03b1_1306_, v_name_1307_, v_kind_boxed_1314_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
return v_res_1315_;
}
}
lean_object* runtime_initialize_Lean_Meta_FunInfo(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_CoeAttr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_FunInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_instInhabitedCoeFnType_default = _init_l_Lean_Meta_instInhabitedCoeFnType_default();
l_Lean_Meta_instInhabitedCoeFnType = _init_l_Lean_Meta_instInhabitedCoeFnType();
l_Lean_Meta_instToExprCoeFnType = _init_l_Lean_Meta_instToExprCoeFnType();
lean_mark_persistent(l_Lean_Meta_instToExprCoeFnType);
l_Lean_Meta_instToExprCoeFnInfo = _init_l_Lean_Meta_instToExprCoeFnInfo();
lean_mark_persistent(l_Lean_Meta_instToExprCoeFnInfo);
res = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_coeExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_coeExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_CoeAttr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_FunInfo(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_CoeAttr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_FunInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CoeAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_CoeAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_CoeAttr(builtin);
}
#ifdef __cplusplus
}
#endif

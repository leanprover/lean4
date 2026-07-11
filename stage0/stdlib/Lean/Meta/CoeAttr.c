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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t lean_bool_not(uint8_t);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "coeExt"};
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 79, 158, 29, 159, 225, 112, 220)}};
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_coeExt;
LEAN_EXPORT lean_object* l_Lean_Meta_getCoeFnInfo_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCoeFnInfo_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCoeFnInfo_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCoeFnInfo_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Meta_registerCoercion_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Meta_registerCoercion_spec__1___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_registerCoercion___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_registerCoercion___closed__0;
static lean_once_cell_t l_Lean_Meta_registerCoercion___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_registerCoercion___closed__1;
static lean_once_cell_t l_Lean_Meta_registerCoercion___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_registerCoercion___closed__2;
static lean_once_cell_t l_Lean_Meta_registerCoercion___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_registerCoercion___closed__3;
static const lean_string_object l_Lean_Meta_registerCoercion___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = " has no explicit arguments"};
static const lean_object* l_Lean_Meta_registerCoercion___closed__4 = (const lean_object*)&l_Lean_Meta_registerCoercion___closed__4_value;
static lean_once_cell_t l_Lean_Meta_registerCoercion___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_registerCoercion___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_registerCoercion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_registerCoercion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Meta_CoeFnType_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_toCtorIdx(uint8_t v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Meta_CoeFnType_ctorIdx(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_toCtorIdx___boxed(lean_object* v_x_10_){
_start:
{
uint8_t v_x_4__boxed_11_; lean_object* v_res_12_; 
v_x_4__boxed_11_ = lean_unbox(v_x_10_);
v_res_12_ = l_Lean_Meta_CoeFnType_toCtorIdx(v_x_4__boxed_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_ctorElim___redArg(lean_object* v_k_13_){
_start:
{
lean_inc(v_k_13_);
return v_k_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_ctorElim___redArg___boxed(lean_object* v_k_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_Meta_CoeFnType_ctorElim___redArg(v_k_14_);
lean_dec(v_k_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, uint8_t v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_inc(v_k_20_);
return v_k_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
uint8_t v_t_boxed_26_; lean_object* v_res_27_; 
v_t_boxed_26_ = lean_unbox(v_t_23_);
v_res_27_ = l_Lean_Meta_CoeFnType_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_boxed_26_, v_h_24_, v_k_25_);
lean_dec(v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coe_elim___redArg(lean_object* v_coe_28_){
_start:
{
lean_inc(v_coe_28_);
return v_coe_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coe_elim___redArg___boxed(lean_object* v_coe_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Meta_CoeFnType_coe_elim___redArg(v_coe_29_);
lean_dec(v_coe_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coe_elim(lean_object* v_motive_31_, uint8_t v_t_32_, lean_object* v_h_33_, lean_object* v_coe_34_){
_start:
{
lean_inc(v_coe_34_);
return v_coe_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coe_elim___boxed(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_coe_38_){
_start:
{
uint8_t v_t_boxed_39_; lean_object* v_res_40_; 
v_t_boxed_39_ = lean_unbox(v_t_36_);
v_res_40_ = l_Lean_Meta_CoeFnType_coe_elim(v_motive_35_, v_t_boxed_39_, v_h_37_, v_coe_38_);
lean_dec(v_coe_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coeFun_elim___redArg(lean_object* v_coeFun_41_){
_start:
{
lean_inc(v_coeFun_41_);
return v_coeFun_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coeFun_elim___redArg___boxed(lean_object* v_coeFun_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Meta_CoeFnType_coeFun_elim___redArg(v_coeFun_42_);
lean_dec(v_coeFun_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coeFun_elim(lean_object* v_motive_44_, uint8_t v_t_45_, lean_object* v_h_46_, lean_object* v_coeFun_47_){
_start:
{
lean_inc(v_coeFun_47_);
return v_coeFun_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coeFun_elim___boxed(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_coeFun_51_){
_start:
{
uint8_t v_t_boxed_52_; lean_object* v_res_53_; 
v_t_boxed_52_ = lean_unbox(v_t_49_);
v_res_53_ = l_Lean_Meta_CoeFnType_coeFun_elim(v_motive_48_, v_t_boxed_52_, v_h_50_, v_coeFun_51_);
lean_dec(v_coeFun_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coeSort_elim___redArg(lean_object* v_coeSort_54_){
_start:
{
lean_inc(v_coeSort_54_);
return v_coeSort_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coeSort_elim___redArg___boxed(lean_object* v_coeSort_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Meta_CoeFnType_coeSort_elim___redArg(v_coeSort_55_);
lean_dec(v_coeSort_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coeSort_elim(lean_object* v_motive_57_, uint8_t v_t_58_, lean_object* v_h_59_, lean_object* v_coeSort_60_){
_start:
{
lean_inc(v_coeSort_60_);
return v_coeSort_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_coeSort_elim___boxed(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_coeSort_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = l_Lean_Meta_CoeFnType_coeSort_elim(v_motive_61_, v_t_boxed_65_, v_h_63_, v_coeSort_64_);
lean_dec(v_coeSort_64_);
return v_res_66_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedCoeFnType_default(void){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedCoeFnType(void){
_start:
{
uint8_t v___x_68_; 
v___x_68_ = 0;
return v___x_68_;
}
}
static lean_object* _init_l_Lean_Meta_instReprCoeFnType_repr___closed__6(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = lean_unsigned_to_nat(2u);
v___x_79_ = lean_nat_to_int(v___x_78_);
return v___x_79_;
}
}
static lean_object* _init_l_Lean_Meta_instReprCoeFnType_repr___closed__7(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_unsigned_to_nat(1u);
v___x_81_ = lean_nat_to_int(v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCoeFnType_repr(uint8_t v_x_82_, lean_object* v_prec_83_){
_start:
{
lean_object* v___y_85_; lean_object* v___y_92_; lean_object* v___y_99_; 
switch(v_x_82_)
{
case 0:
{
lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_105_ = lean_unsigned_to_nat(1024u);
v___x_106_ = lean_nat_dec_le(v___x_105_, v_prec_83_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; 
v___x_107_ = lean_obj_once(&l_Lean_Meta_instReprCoeFnType_repr___closed__6, &l_Lean_Meta_instReprCoeFnType_repr___closed__6_once, _init_l_Lean_Meta_instReprCoeFnType_repr___closed__6);
v___y_85_ = v___x_107_;
goto v___jp_84_;
}
else
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l_Lean_Meta_instReprCoeFnType_repr___closed__7, &l_Lean_Meta_instReprCoeFnType_repr___closed__7_once, _init_l_Lean_Meta_instReprCoeFnType_repr___closed__7);
v___y_85_ = v___x_108_;
goto v___jp_84_;
}
}
case 1:
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = lean_unsigned_to_nat(1024u);
v___x_110_ = lean_nat_dec_le(v___x_109_, v_prec_83_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; 
v___x_111_ = lean_obj_once(&l_Lean_Meta_instReprCoeFnType_repr___closed__6, &l_Lean_Meta_instReprCoeFnType_repr___closed__6_once, _init_l_Lean_Meta_instReprCoeFnType_repr___closed__6);
v___y_92_ = v___x_111_;
goto v___jp_91_;
}
else
{
lean_object* v___x_112_; 
v___x_112_ = lean_obj_once(&l_Lean_Meta_instReprCoeFnType_repr___closed__7, &l_Lean_Meta_instReprCoeFnType_repr___closed__7_once, _init_l_Lean_Meta_instReprCoeFnType_repr___closed__7);
v___y_92_ = v___x_112_;
goto v___jp_91_;
}
}
default: 
{
lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_113_ = lean_unsigned_to_nat(1024u);
v___x_114_ = lean_nat_dec_le(v___x_113_, v_prec_83_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; 
v___x_115_ = lean_obj_once(&l_Lean_Meta_instReprCoeFnType_repr___closed__6, &l_Lean_Meta_instReprCoeFnType_repr___closed__6_once, _init_l_Lean_Meta_instReprCoeFnType_repr___closed__6);
v___y_99_ = v___x_115_;
goto v___jp_98_;
}
else
{
lean_object* v___x_116_; 
v___x_116_ = lean_obj_once(&l_Lean_Meta_instReprCoeFnType_repr___closed__7, &l_Lean_Meta_instReprCoeFnType_repr___closed__7_once, _init_l_Lean_Meta_instReprCoeFnType_repr___closed__7);
v___y_99_ = v___x_116_;
goto v___jp_98_;
}
}
}
v___jp_84_:
{
lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_86_ = ((lean_object*)(l_Lean_Meta_instReprCoeFnType_repr___closed__1));
lean_inc(v___y_85_);
v___x_87_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_87_, 0, v___y_85_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
v___x_88_ = 0;
v___x_89_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_89_, 0, v___x_87_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*1, v___x_88_);
v___x_90_ = l_Repr_addAppParen(v___x_89_, v_prec_83_);
return v___x_90_;
}
v___jp_91_:
{
lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_93_ = ((lean_object*)(l_Lean_Meta_instReprCoeFnType_repr___closed__3));
lean_inc(v___y_92_);
v___x_94_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_94_, 0, v___y_92_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
v___x_95_ = 0;
v___x_96_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_96_, 0, v___x_94_);
lean_ctor_set_uint8(v___x_96_, sizeof(void*)*1, v___x_95_);
v___x_97_ = l_Repr_addAppParen(v___x_96_, v_prec_83_);
return v___x_97_;
}
v___jp_98_:
{
lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_100_ = ((lean_object*)(l_Lean_Meta_instReprCoeFnType_repr___closed__5));
lean_inc(v___y_99_);
v___x_101_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_101_, 0, v___y_99_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
v___x_102_ = 0;
v___x_103_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_103_, 0, v___x_101_);
lean_ctor_set_uint8(v___x_103_, sizeof(void*)*1, v___x_102_);
v___x_104_ = l_Repr_addAppParen(v___x_103_, v_prec_83_);
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCoeFnType_repr___boxed(lean_object* v_x_117_, lean_object* v_prec_118_){
_start:
{
uint8_t v_x_177__boxed_119_; lean_object* v_res_120_; 
v_x_177__boxed_119_ = lean_unbox(v_x_117_);
v_res_120_ = l_Lean_Meta_instReprCoeFnType_repr(v_x_177__boxed_119_, v_prec_118_);
lean_dec(v_prec_118_);
return v_res_120_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_CoeFnType_ofNat(lean_object* v_n_123_){
_start:
{
lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(0u);
v___x_125_ = lean_nat_dec_le(v_n_123_, v___x_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = lean_unsigned_to_nat(1u);
v___x_127_ = lean_nat_dec_le(v_n_123_, v___x_126_);
if (v___x_127_ == 0)
{
uint8_t v___x_128_; 
v___x_128_ = 2;
return v___x_128_;
}
else
{
uint8_t v___x_129_; 
v___x_129_ = 1;
return v___x_129_;
}
}
else
{
uint8_t v___x_130_; 
v___x_130_ = 0;
return v___x_130_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CoeFnType_ofNat___boxed(lean_object* v_n_131_){
_start:
{
uint8_t v_res_132_; lean_object* v_r_133_; 
v_res_132_ = l_Lean_Meta_CoeFnType_ofNat(v_n_131_);
lean_dec(v_n_131_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instDecidableEqCoeFnType(uint8_t v_x_134_, uint8_t v_y_135_){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_136_ = l_Lean_Meta_CoeFnType_ctorIdx(v_x_134_);
v___x_137_ = l_Lean_Meta_CoeFnType_ctorIdx(v_y_135_);
v___x_138_ = lean_nat_dec_eq(v___x_136_, v___x_137_);
lean_dec(v___x_137_);
lean_dec(v___x_136_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instDecidableEqCoeFnType___boxed(lean_object* v_x_139_, lean_object* v_y_140_){
_start:
{
uint8_t v_x_13__boxed_141_; uint8_t v_y_14__boxed_142_; uint8_t v_res_143_; lean_object* v_r_144_; 
v_x_13__boxed_141_ = lean_unbox(v_x_139_);
v_y_14__boxed_142_ = lean_unbox(v_y_140_);
v_res_143_ = l_Lean_Meta_instDecidableEqCoeFnType(v_x_13__boxed_141_, v_y_14__boxed_142_);
v_r_144_ = lean_box(v_res_143_);
return v_r_144_;
}
}
static lean_object* _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_154_ = lean_box(0);
v___x_155_ = ((lean_object*)(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__4));
v___x_156_ = l_Lean_mkConst(v___x_155_, v___x_154_);
return v___x_156_;
}
}
static lean_object* _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_163_ = lean_box(0);
v___x_164_ = ((lean_object*)(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__7));
v___x_165_ = l_Lean_mkConst(v___x_164_, v___x_163_);
return v___x_165_;
}
}
static lean_object* _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = lean_box(0);
v___x_173_ = ((lean_object*)(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__10));
v___x_174_ = l_Lean_mkConst(v___x_173_, v___x_172_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instToExprCoeFnType___lam__0(uint8_t v_x_175_){
_start:
{
switch(v_x_175_)
{
case 0:
{
lean_object* v___x_176_; 
v___x_176_ = lean_obj_once(&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5, &l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5_once, _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5);
return v___x_176_;
}
case 1:
{
lean_object* v___x_177_; 
v___x_177_ = lean_obj_once(&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8, &l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8_once, _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8);
return v___x_177_;
}
default: 
{
lean_object* v___x_178_; 
v___x_178_ = lean_obj_once(&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11, &l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11_once, _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11);
return v___x_178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instToExprCoeFnType___lam__0___boxed(lean_object* v_x_179_){
_start:
{
uint8_t v_x_156__boxed_180_; lean_object* v_res_181_; 
v_x_156__boxed_180_ = lean_unbox(v_x_179_);
v_res_181_ = l_Lean_Meta_instToExprCoeFnType___lam__0(v_x_156__boxed_180_);
return v_res_181_;
}
}
static lean_object* _init_l_Lean_Meta_instToExprCoeFnType___closed__2(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_187_ = lean_box(0);
v___x_188_ = ((lean_object*)(l_Lean_Meta_instToExprCoeFnType___closed__1));
v___x_189_ = l_Lean_mkConst(v___x_188_, v___x_187_);
return v___x_189_;
}
}
static lean_object* _init_l_Lean_Meta_instToExprCoeFnType___closed__3(void){
_start:
{
lean_object* v___x_190_; lean_object* v___f_191_; lean_object* v___x_192_; 
v___x_190_ = lean_obj_once(&l_Lean_Meta_instToExprCoeFnType___closed__2, &l_Lean_Meta_instToExprCoeFnType___closed__2_once, _init_l_Lean_Meta_instToExprCoeFnType___closed__2);
v___f_191_ = ((lean_object*)(l_Lean_Meta_instToExprCoeFnType___closed__0));
v___x_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_192_, 0, v___f_191_);
lean_ctor_set(v___x_192_, 1, v___x_190_);
return v___x_192_;
}
}
static lean_object* _init_l_Lean_Meta_instToExprCoeFnType(void){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = lean_obj_once(&l_Lean_Meta_instToExprCoeFnType___closed__3, &l_Lean_Meta_instToExprCoeFnType___closed__3_once, _init_l_Lean_Meta_instToExprCoeFnType___closed__3);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_instReprCoeFnInfo_repr_spec__0(lean_object* v_a_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_nat_to_int(v_a_199_);
return v___x_200_;
}
}
static lean_object* _init_l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = lean_unsigned_to_nat(11u);
v___x_215_ = lean_nat_to_int(v___x_214_);
return v___x_215_;
}
}
static lean_object* _init_l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = lean_unsigned_to_nat(8u);
v___x_226_ = lean_nat_to_int(v___x_225_);
return v___x_226_;
}
}
static lean_object* _init_l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = ((lean_object*)(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__0));
v___x_229_ = lean_string_length(v___x_228_);
return v___x_229_;
}
}
static lean_object* _init_l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = lean_obj_once(&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__16, &l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__16_once, _init_l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__16);
v___x_231_ = lean_nat_to_int(v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCoeFnInfo_repr___redArg(lean_object* v_x_236_){
_start:
{
lean_object* v_numArgs_237_; lean_object* v_coercee_238_; uint8_t v_type_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v_numArgs_237_ = lean_ctor_get(v_x_236_, 0);
lean_inc(v_numArgs_237_);
v_coercee_238_ = lean_ctor_get(v_x_236_, 1);
lean_inc(v_coercee_238_);
v_type_239_ = lean_ctor_get_uint8(v_x_236_, sizeof(void*)*2);
lean_dec_ref(v_x_236_);
v___x_240_ = ((lean_object*)(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__5));
v___x_241_ = ((lean_object*)(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__6));
v___x_242_ = lean_obj_once(&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__7, &l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__7_once, _init_l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__7);
v___x_243_ = l_Nat_reprFast(v_numArgs_237_);
v___x_244_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
v___x_245_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_242_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
v___x_246_ = 0;
v___x_247_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_247_, 0, v___x_245_);
lean_ctor_set_uint8(v___x_247_, sizeof(void*)*1, v___x_246_);
v___x_248_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_241_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v___x_249_ = ((lean_object*)(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__9));
v___x_250_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_248_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
v___x_251_ = lean_box(1);
v___x_252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_250_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
v___x_253_ = ((lean_object*)(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__11));
v___x_254_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_252_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v___x_240_);
v___x_256_ = l_Nat_reprFast(v_coercee_238_);
v___x_257_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
v___x_258_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_242_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*1, v___x_246_);
v___x_260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_255_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
v___x_261_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v___x_249_);
v___x_262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
lean_ctor_set(v___x_262_, 1, v___x_251_);
v___x_263_ = ((lean_object*)(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__13));
v___x_264_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_262_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v___x_240_);
v___x_266_ = lean_obj_once(&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__14, &l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__14_once, _init_l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__14);
v___x_267_ = lean_unsigned_to_nat(0u);
v___x_268_ = l_Lean_Meta_instReprCoeFnType_repr(v_type_239_, v___x_267_);
v___x_269_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_266_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v___x_270_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set_uint8(v___x_270_, sizeof(void*)*1, v___x_246_);
v___x_271_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_265_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
v___x_272_ = lean_obj_once(&l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__17, &l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__17_once, _init_l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__17);
v___x_273_ = ((lean_object*)(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__18));
v___x_274_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
lean_ctor_set(v___x_274_, 1, v___x_271_);
v___x_275_ = ((lean_object*)(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__19));
v___x_276_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_274_);
lean_ctor_set(v___x_276_, 1, v___x_275_);
v___x_277_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_272_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
v___x_278_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set_uint8(v___x_278_, sizeof(void*)*1, v___x_246_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCoeFnInfo_repr(lean_object* v_x_279_, lean_object* v_prec_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l_Lean_Meta_instReprCoeFnInfo_repr___redArg(v_x_279_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprCoeFnInfo_repr___boxed(lean_object* v_x_282_, lean_object* v_prec_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_Meta_instReprCoeFnInfo_repr(v_x_282_, v_prec_283_);
lean_dec(v_prec_283_);
return v_res_284_;
}
}
static lean_object* _init_l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__3(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_294_ = lean_box(0);
v___x_295_ = ((lean_object*)(l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__2));
v___x_296_ = l_Lean_mkConst(v___x_295_, v___x_294_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instToExprCoeFnInfo___lam__0(lean_object* v_x_297_){
_start:
{
lean_object* v_numArgs_298_; lean_object* v_coercee_299_; uint8_t v_type_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v_numArgs_298_ = lean_ctor_get(v_x_297_, 0);
lean_inc(v_numArgs_298_);
v_coercee_299_ = lean_ctor_get(v_x_297_, 1);
lean_inc(v_coercee_299_);
v_type_300_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*2);
lean_dec_ref(v_x_297_);
v___x_301_ = lean_obj_once(&l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__3, &l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__3_once, _init_l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__3);
v___x_302_ = l_Lean_mkNatLit(v_numArgs_298_);
v___x_303_ = l_Lean_mkNatLit(v_coercee_299_);
switch(v_type_300_)
{
case 0:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_obj_once(&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5, &l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5_once, _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5);
v___x_305_ = l_Lean_mkApp3(v___x_301_, v___x_302_, v___x_303_, v___x_304_);
return v___x_305_;
}
case 1:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = lean_obj_once(&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8, &l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8_once, _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8);
v___x_307_ = l_Lean_mkApp3(v___x_301_, v___x_302_, v___x_303_, v___x_306_);
return v___x_307_;
}
default: 
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = lean_obj_once(&l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11, &l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11_once, _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11);
v___x_309_ = l_Lean_mkApp3(v___x_301_, v___x_302_, v___x_303_, v___x_308_);
return v___x_309_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_instToExprCoeFnInfo___closed__2(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_315_ = lean_box(0);
v___x_316_ = ((lean_object*)(l_Lean_Meta_instToExprCoeFnInfo___closed__1));
v___x_317_ = l_Lean_mkConst(v___x_316_, v___x_315_);
return v___x_317_;
}
}
static lean_object* _init_l_Lean_Meta_instToExprCoeFnInfo___closed__3(void){
_start:
{
lean_object* v___x_318_; lean_object* v___f_319_; lean_object* v___x_320_; 
v___x_318_ = lean_obj_once(&l_Lean_Meta_instToExprCoeFnInfo___closed__2, &l_Lean_Meta_instToExprCoeFnInfo___closed__2_once, _init_l_Lean_Meta_instToExprCoeFnInfo___closed__2);
v___f_319_ = ((lean_object*)(l_Lean_Meta_instToExprCoeFnInfo___closed__0));
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v___f_319_);
lean_ctor_set(v___x_320_, 1, v___x_318_);
return v___x_320_;
}
}
static lean_object* _init_l_Lean_Meta_instToExprCoeFnInfo(void){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = lean_obj_once(&l_Lean_Meta_instToExprCoeFnInfo___closed__3, &l_Lean_Meta_instToExprCoeFnInfo___closed__3_once, _init_l_Lean_Meta_instToExprCoeFnInfo___closed__3);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(lean_object* v_st_322_, lean_object* v_x_323_){
_start:
{
lean_object* v_fst_324_; lean_object* v_snd_325_; lean_object* v___x_326_; 
v_fst_324_ = lean_ctor_get(v_x_323_, 0);
lean_inc(v_fst_324_);
v_snd_325_ = lean_ctor_get(v_x_323_, 1);
lean_inc(v_snd_325_);
lean_dec_ref(v_x_323_);
v___x_326_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_324_, v_snd_325_, v_st_322_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(lean_object* v_x_327_, lean_object* v_a_328_){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_329_, 0, v_a_328_);
lean_inc_ref_n(v___x_329_, 2);
v___x_330_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
lean_ctor_set(v___x_330_, 2, v___x_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed(lean_object* v_x_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(v_x_331_, v_a_332_);
lean_dec_ref(v_x_331_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(lean_object* v___y_334_){
_start:
{
lean_inc(v___y_334_);
return v___y_334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed(lean_object* v___y_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(v___y_335_);
lean_dec(v___y_335_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_));
v___x_353_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed(lean_object* v_a_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_();
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCoeFnInfo_x3f___redArg(lean_object* v_fn_356_, lean_object* v_a_357_){
_start:
{
lean_object* v___x_359_; lean_object* v_env_360_; lean_object* v___x_361_; lean_object* v_ext_362_; lean_object* v_toEnvExtension_363_; lean_object* v_asyncMode_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_359_ = lean_st_ref_get(v_a_357_);
v_env_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc_ref(v_env_360_);
lean_dec(v___x_359_);
v___x_361_ = l_Lean_Meta_coeExt;
v_ext_362_ = lean_ctor_get(v___x_361_, 1);
v_toEnvExtension_363_ = lean_ctor_get(v_ext_362_, 0);
v_asyncMode_364_ = lean_ctor_get(v_toEnvExtension_363_, 2);
v___x_365_ = lean_box(1);
v___x_366_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_365_, v___x_361_, v_env_360_, v_asyncMode_364_);
v___x_367_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_366_, v_fn_356_);
lean_dec(v___x_366_);
v___x_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCoeFnInfo_x3f___redArg___boxed(lean_object* v_fn_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_Meta_getCoeFnInfo_x3f___redArg(v_fn_369_, v_a_370_);
lean_dec(v_a_370_);
lean_dec(v_fn_369_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCoeFnInfo_x3f(lean_object* v_fn_373_, lean_object* v_a_374_, lean_object* v_a_375_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_Meta_getCoeFnInfo_x3f___redArg(v_fn_373_, v_a_375_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCoeFnInfo_x3f___boxed(lean_object* v_fn_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_Meta_getCoeFnInfo_x3f(v_fn_378_, v_a_379_, v_a_380_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
lean_dec(v_fn_378_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2_spec__4(lean_object* v_msgData_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v___x_389_; lean_object* v_env_390_; lean_object* v___x_391_; lean_object* v_mctx_392_; lean_object* v_lctx_393_; lean_object* v_options_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_389_ = lean_st_ref_get(v___y_387_);
v_env_390_ = lean_ctor_get(v___x_389_, 0);
lean_inc_ref(v_env_390_);
lean_dec(v___x_389_);
v___x_391_ = lean_st_ref_get(v___y_385_);
v_mctx_392_ = lean_ctor_get(v___x_391_, 0);
lean_inc_ref(v_mctx_392_);
lean_dec(v___x_391_);
v_lctx_393_ = lean_ctor_get(v___y_384_, 2);
v_options_394_ = lean_ctor_get(v___y_386_, 2);
lean_inc_ref(v_options_394_);
lean_inc_ref(v_lctx_393_);
v___x_395_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_395_, 0, v_env_390_);
lean_ctor_set(v___x_395_, 1, v_mctx_392_);
lean_ctor_set(v___x_395_, 2, v_lctx_393_);
lean_ctor_set(v___x_395_, 3, v_options_394_);
v___x_396_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
lean_ctor_set(v___x_396_, 1, v_msgData_383_);
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2_spec__4___boxed(lean_object* v_msgData_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2_spec__4(v_msgData_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2___redArg(lean_object* v_msg_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v_ref_411_; lean_object* v___x_412_; lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_421_; 
v_ref_411_ = lean_ctor_get(v___y_408_, 5);
v___x_412_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2_spec__4(v_msg_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
v_a_413_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_421_ == 0)
{
v___x_415_ = v___x_412_;
v_isShared_416_ = v_isSharedCheck_421_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_412_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_421_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_417_; lean_object* v___x_419_; 
lean_inc(v_ref_411_);
v___x_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_417_, 0, v_ref_411_);
lean_ctor_set(v___x_417_, 1, v_a_413_);
if (v_isShared_416_ == 0)
{
lean_ctor_set_tag(v___x_415_, 1);
lean_ctor_set(v___x_415_, 0, v___x_417_);
v___x_419_ = v___x_415_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2___redArg___boxed(lean_object* v_msg_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2___redArg(v_msg_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___redArg(lean_object* v_ref_429_, lean_object* v_msg_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v_fileName_436_; lean_object* v_fileMap_437_; lean_object* v_options_438_; lean_object* v_currRecDepth_439_; lean_object* v_maxRecDepth_440_; lean_object* v_ref_441_; lean_object* v_currNamespace_442_; lean_object* v_openDecls_443_; lean_object* v_initHeartbeats_444_; lean_object* v_maxHeartbeats_445_; lean_object* v_quotContext_446_; lean_object* v_currMacroScope_447_; uint8_t v_diag_448_; lean_object* v_cancelTk_x3f_449_; uint8_t v_suppressElabErrors_450_; lean_object* v_inheritedTraceOptions_451_; lean_object* v_ref_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v_fileName_436_ = lean_ctor_get(v___y_433_, 0);
v_fileMap_437_ = lean_ctor_get(v___y_433_, 1);
v_options_438_ = lean_ctor_get(v___y_433_, 2);
v_currRecDepth_439_ = lean_ctor_get(v___y_433_, 3);
v_maxRecDepth_440_ = lean_ctor_get(v___y_433_, 4);
v_ref_441_ = lean_ctor_get(v___y_433_, 5);
v_currNamespace_442_ = lean_ctor_get(v___y_433_, 6);
v_openDecls_443_ = lean_ctor_get(v___y_433_, 7);
v_initHeartbeats_444_ = lean_ctor_get(v___y_433_, 8);
v_maxHeartbeats_445_ = lean_ctor_get(v___y_433_, 9);
v_quotContext_446_ = lean_ctor_get(v___y_433_, 10);
v_currMacroScope_447_ = lean_ctor_get(v___y_433_, 11);
v_diag_448_ = lean_ctor_get_uint8(v___y_433_, sizeof(void*)*14);
v_cancelTk_x3f_449_ = lean_ctor_get(v___y_433_, 12);
v_suppressElabErrors_450_ = lean_ctor_get_uint8(v___y_433_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_451_ = lean_ctor_get(v___y_433_, 13);
v_ref_452_ = l_Lean_replaceRef(v_ref_429_, v_ref_441_);
lean_inc_ref(v_inheritedTraceOptions_451_);
lean_inc(v_cancelTk_x3f_449_);
lean_inc(v_currMacroScope_447_);
lean_inc(v_quotContext_446_);
lean_inc(v_maxHeartbeats_445_);
lean_inc(v_initHeartbeats_444_);
lean_inc(v_openDecls_443_);
lean_inc(v_currNamespace_442_);
lean_inc(v_maxRecDepth_440_);
lean_inc(v_currRecDepth_439_);
lean_inc_ref(v_options_438_);
lean_inc_ref(v_fileMap_437_);
lean_inc_ref(v_fileName_436_);
v___x_453_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_453_, 0, v_fileName_436_);
lean_ctor_set(v___x_453_, 1, v_fileMap_437_);
lean_ctor_set(v___x_453_, 2, v_options_438_);
lean_ctor_set(v___x_453_, 3, v_currRecDepth_439_);
lean_ctor_set(v___x_453_, 4, v_maxRecDepth_440_);
lean_ctor_set(v___x_453_, 5, v_ref_452_);
lean_ctor_set(v___x_453_, 6, v_currNamespace_442_);
lean_ctor_set(v___x_453_, 7, v_openDecls_443_);
lean_ctor_set(v___x_453_, 8, v_initHeartbeats_444_);
lean_ctor_set(v___x_453_, 9, v_maxHeartbeats_445_);
lean_ctor_set(v___x_453_, 10, v_quotContext_446_);
lean_ctor_set(v___x_453_, 11, v_currMacroScope_447_);
lean_ctor_set(v___x_453_, 12, v_cancelTk_x3f_449_);
lean_ctor_set(v___x_453_, 13, v_inheritedTraceOptions_451_);
lean_ctor_set_uint8(v___x_453_, sizeof(void*)*14, v_diag_448_);
lean_ctor_set_uint8(v___x_453_, sizeof(void*)*14 + 1, v_suppressElabErrors_450_);
v___x_454_ = l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2___redArg(v_msg_430_, v___y_431_, v___y_432_, v___x_453_, v___y_434_);
lean_dec_ref_known(v___x_453_, 14);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_ref_455_, lean_object* v_msg_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___redArg(v_ref_455_, v_msg_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v_ref_455_);
return v_res_462_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_463_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_466_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_467_ = lean_unsigned_to_nat(0u);
v___x_468_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
lean_ctor_set(v___x_468_, 2, v___x_467_);
lean_ctor_set(v___x_468_, 3, v___x_467_);
lean_ctor_set(v___x_468_, 4, v___x_466_);
lean_ctor_set(v___x_468_, 5, v___x_466_);
lean_ctor_set(v___x_468_, 6, v___x_466_);
lean_ctor_set(v___x_468_, 7, v___x_466_);
lean_ctor_set(v___x_468_, 8, v___x_466_);
lean_ctor_set(v___x_468_, 9, v___x_466_);
return v___x_468_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_469_ = lean_unsigned_to_nat(32u);
v___x_470_ = lean_mk_empty_array_with_capacity(v___x_469_);
v___x_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
return v___x_471_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__4(void){
_start:
{
size_t v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_472_ = ((size_t)5ULL);
v___x_473_ = lean_unsigned_to_nat(0u);
v___x_474_ = lean_unsigned_to_nat(32u);
v___x_475_ = lean_mk_empty_array_with_capacity(v___x_474_);
v___x_476_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_477_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_477_, 0, v___x_476_);
lean_ctor_set(v___x_477_, 1, v___x_475_);
lean_ctor_set(v___x_477_, 2, v___x_473_);
lean_ctor_set(v___x_477_, 3, v___x_473_);
lean_ctor_set_usize(v___x_477_, 4, v___x_472_);
return v___x_477_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_478_ = lean_box(1);
v___x_479_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_480_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_481_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
lean_ctor_set(v___x_481_, 1, v___x_479_);
lean_ctor_set(v___x_481_, 2, v___x_478_);
return v___x_481_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_484_ = l_Lean_stringToMessageData(v___x_483_);
return v___x_484_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_487_ = l_Lean_stringToMessageData(v___x_486_);
return v___x_487_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_490_ = l_Lean_stringToMessageData(v___x_489_);
return v___x_490_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_493_ = l_Lean_stringToMessageData(v___x_492_);
return v___x_493_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__15(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__14));
v___x_496_ = l_Lean_stringToMessageData(v___x_495_);
return v___x_496_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__17(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__16));
v___x_499_ = l_Lean_stringToMessageData(v___x_498_);
return v___x_499_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__19(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__18));
v___x_502_ = l_Lean_stringToMessageData(v___x_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_503_, lean_object* v_declHint_504_, lean_object* v___y_505_){
_start:
{
lean_object* v___x_507_; lean_object* v_env_508_; uint8_t v___y_510_; uint8_t v___x_566_; uint8_t v___x_567_; 
v___x_507_ = lean_st_ref_get(v___y_505_);
v_env_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc_ref(v_env_508_);
lean_dec(v___x_507_);
v___x_566_ = l_Lean_Name_isAnonymous(v_declHint_504_);
v___x_567_ = lean_bool_not(v___x_566_);
if (v___x_567_ == 0)
{
v___y_510_ = v___x_567_;
goto v___jp_509_;
}
else
{
uint8_t v_isExporting_568_; 
v_isExporting_568_ = lean_ctor_get_uint8(v_env_508_, sizeof(void*)*8);
v___y_510_ = v_isExporting_568_;
goto v___jp_509_;
}
v___jp_509_:
{
if (v___y_510_ == 0)
{
lean_object* v___x_511_; 
lean_dec_ref(v_env_508_);
lean_dec(v_declHint_504_);
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v_msg_503_);
return v___x_511_;
}
else
{
uint8_t v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_512_ = 0;
lean_inc_ref(v_env_508_);
v___x_513_ = l_Lean_Environment_setExporting(v_env_508_, v___x_512_);
lean_inc(v_declHint_504_);
lean_inc_ref(v___x_513_);
v___x_514_ = l_Lean_Environment_contains(v___x_513_, v_declHint_504_, v___y_510_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; 
lean_dec_ref(v___x_513_);
lean_dec_ref(v_env_508_);
lean_dec(v_declHint_504_);
v___x_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_515_, 0, v_msg_503_);
return v___x_515_;
}
else
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v_c_521_; lean_object* v___x_522_; 
v___x_516_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_517_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_518_ = l_Lean_Options_empty;
v___x_519_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_519_, 0, v___x_513_);
lean_ctor_set(v___x_519_, 1, v___x_516_);
lean_ctor_set(v___x_519_, 2, v___x_517_);
lean_ctor_set(v___x_519_, 3, v___x_518_);
lean_inc(v_declHint_504_);
v___x_520_ = l_Lean_MessageData_ofConstName(v_declHint_504_, v___x_512_);
v_c_521_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_521_, 0, v___x_519_);
lean_ctor_set(v_c_521_, 1, v___x_520_);
v___x_522_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_508_, v_declHint_504_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
lean_dec_ref(v_env_508_);
lean_dec(v_declHint_504_);
v___x_523_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
lean_ctor_set(v___x_524_, 1, v_c_521_);
v___x_525_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_524_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = l_Lean_MessageData_note(v___x_526_);
v___x_528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_528_, 0, v_msg_503_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
v___x_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
return v___x_529_;
}
else
{
lean_object* v_val_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_565_; 
v_val_530_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_565_ == 0)
{
v___x_532_ = v___x_522_;
v_isShared_533_ = v_isSharedCheck_565_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_val_530_);
lean_dec(v___x_522_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_565_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v_mod_537_; uint8_t v___x_538_; 
v___x_534_ = lean_box(0);
v___x_535_ = l_Lean_Environment_header(v_env_508_);
lean_dec_ref(v_env_508_);
v___x_536_ = l_Lean_EnvironmentHeader_moduleNames(v___x_535_);
v_mod_537_ = lean_array_get(v___x_534_, v___x_536_, v_val_530_);
lean_dec(v_val_530_);
lean_dec_ref(v___x_536_);
v___x_538_ = l_Lean_isPrivateName(v_declHint_504_);
lean_dec(v_declHint_504_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_539_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
lean_ctor_set(v___x_540_, 1, v_c_521_);
v___x_541_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_540_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
v___x_543_ = l_Lean_MessageData_ofName(v_mod_537_);
v___x_544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_542_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
v___x_545_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_544_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
v___x_547_ = l_Lean_MessageData_note(v___x_546_);
v___x_548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_548_, 0, v_msg_503_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
if (v_isShared_533_ == 0)
{
lean_ctor_set_tag(v___x_532_, 0);
lean_ctor_set(v___x_532_, 0, v___x_548_);
v___x_550_ = v___x_532_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_563_; 
v___x_552_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
lean_ctor_set(v___x_553_, 1, v_c_521_);
v___x_554_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_553_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = l_Lean_MessageData_ofName(v_mod_537_);
v___x_557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_555_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
v___x_558_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__19);
v___x_559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_557_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
v___x_560_ = l_Lean_MessageData_note(v___x_559_);
v___x_561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_561_, 0, v_msg_503_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
if (v_isShared_533_ == 0)
{
lean_ctor_set_tag(v___x_532_, 0);
lean_ctor_set(v___x_532_, 0, v___x_561_);
v___x_563_ = v___x_532_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_561_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_569_, lean_object* v_declHint_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_569_, v_declHint_570_, v___y_571_);
lean_dec(v___y_571_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8(lean_object* v_msg_574_, lean_object* v_declHint_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v___x_581_; lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_591_; 
v___x_581_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_574_, v_declHint_575_, v___y_579_);
v_a_582_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_591_ == 0)
{
v___x_584_ = v___x_581_;
v_isShared_585_ = v_isSharedCheck_591_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_581_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_591_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_586_ = l_Lean_unknownIdentifierMessageTag;
v___x_587_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
lean_ctor_set(v___x_587_, 1, v_a_582_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_587_);
v___x_589_ = v___x_584_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_587_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8___boxed(lean_object* v_msg_592_, lean_object* v_declHint_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8(v_msg_592_, v_declHint_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7___redArg(lean_object* v_ref_600_, lean_object* v_msg_601_, lean_object* v_declHint_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v___x_608_; lean_object* v_a_609_; lean_object* v___x_610_; 
v___x_608_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8(v_msg_601_, v_declHint_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
v_a_609_ = lean_ctor_get(v___x_608_, 0);
lean_inc(v_a_609_);
lean_dec_ref(v___x_608_);
v___x_610_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___redArg(v_ref_600_, v_a_609_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7___redArg___boxed(lean_object* v_ref_611_, lean_object* v_msg_612_, lean_object* v_declHint_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7___redArg(v_ref_611_, v_msg_612_, v_declHint_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v_ref_611_);
return v_res_619_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__0));
v___x_622_ = l_Lean_stringToMessageData(v___x_621_);
return v___x_622_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__2));
v___x_625_ = l_Lean_stringToMessageData(v___x_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_ref_626_, lean_object* v_constName_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v___x_633_; uint8_t v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_633_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__1);
v___x_634_ = 0;
lean_inc(v_constName_627_);
v___x_635_ = l_Lean_MessageData_ofConstName(v_constName_627_, v___x_634_);
v___x_636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_633_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
v___x_637_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3);
v___x_638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_636_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
v___x_639_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7___redArg(v_ref_626_, v___x_638_, v_constName_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_ref_640_, lean_object* v_constName_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg(v_ref_640_, v_constName_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v_ref_640_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v_ref_654_; lean_object* v___x_655_; 
v_ref_654_ = lean_ctor_get(v___y_651_, 5);
v___x_655_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg(v_ref_654_, v_constName_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1___redArg(v_constName_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0(lean_object* v_constName_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v___x_669_; lean_object* v_env_670_; uint8_t v___x_671_; lean_object* v___x_672_; 
v___x_669_ = lean_st_ref_get(v___y_667_);
v_env_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc_ref(v_env_670_);
lean_dec(v___x_669_);
v___x_671_ = 0;
lean_inc(v_constName_663_);
v___x_672_ = l_Lean_Environment_findConstVal_x3f(v_env_670_, v_constName_663_, v___x_671_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v___x_673_; 
v___x_673_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1___redArg(v_constName_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_);
return v___x_673_;
}
else
{
lean_object* v_val_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
lean_dec(v_constName_663_);
v_val_674_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_672_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_val_674_);
lean_dec(v___x_672_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
lean_ctor_set_tag(v___x_676_, 0);
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_val_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0___boxed(lean_object* v_constName_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0(v_constName_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__1(lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
if (lean_obj_tag(v_a_689_) == 0)
{
lean_object* v___x_691_; 
v___x_691_ = l_List_reverse___redArg(v_a_690_);
return v___x_691_;
}
else
{
lean_object* v_head_692_; lean_object* v_tail_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_702_; 
v_head_692_ = lean_ctor_get(v_a_689_, 0);
v_tail_693_ = lean_ctor_get(v_a_689_, 1);
v_isSharedCheck_702_ = !lean_is_exclusive(v_a_689_);
if (v_isSharedCheck_702_ == 0)
{
v___x_695_ = v_a_689_;
v_isShared_696_ = v_isSharedCheck_702_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_tail_693_);
lean_inc(v_head_692_);
lean_dec(v_a_689_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_702_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_697_ = l_Lean_mkLevelParam(v_head_692_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 1, v_a_690_);
lean_ctor_set(v___x_695_, 0, v___x_697_);
v___x_699_ = v___x_695_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_a_690_);
v___x_699_ = v_reuseFailAlloc_701_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
v_a_689_ = v_tail_693_;
v_a_690_ = v___x_699_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0(lean_object* v_constName_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v___x_709_; 
lean_inc(v_constName_703_);
v___x_709_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0(v_constName_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_721_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_721_ == 0)
{
v___x_712_ = v___x_709_;
v_isShared_713_ = v_isSharedCheck_721_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_709_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_721_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v_levelParams_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_719_; 
v_levelParams_714_ = lean_ctor_get(v_a_710_, 1);
lean_inc(v_levelParams_714_);
lean_dec(v_a_710_);
v___x_715_ = lean_box(0);
v___x_716_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__1(v_levelParams_714_, v___x_715_);
v___x_717_ = l_Lean_mkConst(v_constName_703_, v___x_716_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v___x_717_);
v___x_719_ = v___x_712_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_717_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec(v_constName_703_);
v_a_722_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_709_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_709_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0___boxed(lean_object* v_constName_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0(v_constName_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Meta_registerCoercion_spec__1(lean_object* v_as_737_, lean_object* v_j_738_){
_start:
{
lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_739_ = lean_array_get_size(v_as_737_);
v___x_740_ = lean_nat_dec_lt(v_j_738_, v___x_739_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; 
lean_dec(v_j_738_);
v___x_741_ = lean_box(0);
return v___x_741_;
}
else
{
lean_object* v___x_742_; uint8_t v_binderInfo_743_; uint8_t v___x_744_; 
v___x_742_ = lean_array_fget_borrowed(v_as_737_, v_j_738_);
v_binderInfo_743_ = lean_ctor_get_uint8(v___x_742_, sizeof(void*)*1);
v___x_744_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_743_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = lean_unsigned_to_nat(1u);
v___x_746_ = lean_nat_add(v_j_738_, v___x_745_);
lean_dec(v_j_738_);
v_j_738_ = v___x_746_;
goto _start;
}
else
{
lean_object* v___x_748_; 
v___x_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_748_, 0, v_j_738_);
return v___x_748_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Meta_registerCoercion_spec__1___boxed(lean_object* v_as_749_, lean_object* v_j_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Array_findIdx_x3f_loop___at___00Lean_Meta_registerCoercion_spec__1(v_as_749_, v_j_750_);
lean_dec_ref(v_as_749_);
return v_res_751_;
}
}
static lean_object* _init_l_Lean_Meta_registerCoercion___closed__0(void){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_752_;
}
}
static lean_object* _init_l_Lean_Meta_registerCoercion___closed__1(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = lean_obj_once(&l_Lean_Meta_registerCoercion___closed__0, &l_Lean_Meta_registerCoercion___closed__0_once, _init_l_Lean_Meta_registerCoercion___closed__0);
v___x_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
return v___x_754_;
}
}
static lean_object* _init_l_Lean_Meta_registerCoercion___closed__2(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = lean_obj_once(&l_Lean_Meta_registerCoercion___closed__1, &l_Lean_Meta_registerCoercion___closed__1_once, _init_l_Lean_Meta_registerCoercion___closed__1);
v___x_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
return v___x_756_;
}
}
static lean_object* _init_l_Lean_Meta_registerCoercion___closed__3(void){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = lean_obj_once(&l_Lean_Meta_registerCoercion___closed__1, &l_Lean_Meta_registerCoercion___closed__1_once, _init_l_Lean_Meta_registerCoercion___closed__1);
v___x_758_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
lean_ctor_set(v___x_758_, 2, v___x_757_);
lean_ctor_set(v___x_758_, 3, v___x_757_);
lean_ctor_set(v___x_758_, 4, v___x_757_);
lean_ctor_set(v___x_758_, 5, v___x_757_);
return v___x_758_;
}
}
static lean_object* _init_l_Lean_Meta_registerCoercion___closed__5(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = ((lean_object*)(l_Lean_Meta_registerCoercion___closed__4));
v___x_761_ = l_Lean_stringToMessageData(v___x_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerCoercion(lean_object* v_name_762_, lean_object* v_info_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_info_770_; lean_object* v___y_771_; lean_object* v___y_772_; 
if (lean_obj_tag(v_info_763_) == 0)
{
lean_object* v___x_812_; 
lean_inc(v_name_762_);
v___x_812_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0(v_name_762_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_a_813_);
lean_dec_ref_known(v___x_812_, 1);
v___x_814_ = lean_box(0);
v___x_815_ = l_Lean_Meta_getFunInfo(v_a_813_, v___x_814_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_a_816_; lean_object* v_paramInfo_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_842_; 
v_a_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_a_816_);
lean_dec_ref_known(v___x_815_, 1);
v_paramInfo_817_ = lean_ctor_get(v_a_816_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v_a_816_);
if (v_isSharedCheck_842_ == 0)
{
lean_object* v_unused_843_; 
v_unused_843_ = lean_ctor_get(v_a_816_, 1);
lean_dec(v_unused_843_);
v___x_819_ = v_a_816_;
v_isShared_820_ = v_isSharedCheck_842_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_paramInfo_817_);
lean_dec(v_a_816_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_842_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = lean_unsigned_to_nat(0u);
v___x_822_ = l_Array_findIdx_x3f_loop___at___00Lean_Meta_registerCoercion_spec__1(v_paramInfo_817_, v___x_821_);
lean_dec_ref(v_paramInfo_817_);
if (lean_obj_tag(v___x_822_) == 1)
{
lean_object* v_val_823_; lean_object* v___x_824_; lean_object* v___x_825_; uint8_t v___x_826_; lean_object* v___x_827_; 
lean_del_object(v___x_819_);
v_val_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_val_823_);
lean_dec_ref_known(v___x_822_, 1);
v___x_824_ = lean_unsigned_to_nat(1u);
v___x_825_ = lean_nat_add(v_val_823_, v___x_824_);
v___x_826_ = 0;
v___x_827_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_827_, 0, v___x_825_);
lean_ctor_set(v___x_827_, 1, v_val_823_);
lean_ctor_set_uint8(v___x_827_, sizeof(void*)*2, v___x_826_);
v_info_770_ = v___x_827_;
v___y_771_ = v_a_765_;
v___y_772_ = v_a_767_;
goto v___jp_769_;
}
else
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_831_; 
lean_dec(v___x_822_);
v___x_828_ = l_Lean_MessageData_ofName(v_name_762_);
v___x_829_ = lean_obj_once(&l_Lean_Meta_registerCoercion___closed__5, &l_Lean_Meta_registerCoercion___closed__5_once, _init_l_Lean_Meta_registerCoercion___closed__5);
if (v_isShared_820_ == 0)
{
lean_ctor_set_tag(v___x_819_, 7);
lean_ctor_set(v___x_819_, 1, v___x_829_);
lean_ctor_set(v___x_819_, 0, v___x_828_);
v___x_831_ = v___x_819_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_828_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v___x_829_);
v___x_831_ = v_reuseFailAlloc_841_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
lean_object* v___x_832_; lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
v___x_832_ = l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2___redArg(v___x_831_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
v_a_833_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_832_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_832_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
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
}
}
else
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
lean_dec(v_name_762_);
v_a_844_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_815_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_815_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_844_);
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
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
lean_dec(v_name_762_);
v_a_852_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_812_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_812_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
else
{
lean_object* v_val_860_; 
v_val_860_ = lean_ctor_get(v_info_763_, 0);
lean_inc(v_val_860_);
lean_dec_ref_known(v_info_763_, 1);
v_info_770_ = v_val_860_;
v___y_771_ = v_a_765_;
v___y_772_ = v_a_767_;
goto v___jp_769_;
}
v___jp_769_:
{
lean_object* v___x_773_; lean_object* v_env_774_; lean_object* v_nextMacroScope_775_; lean_object* v_ngen_776_; lean_object* v_auxDeclNGen_777_; lean_object* v_traceState_778_; lean_object* v_messages_779_; lean_object* v_infoState_780_; lean_object* v_snapshotTasks_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_810_; 
v___x_773_ = lean_st_ref_take(v___y_772_);
v_env_774_ = lean_ctor_get(v___x_773_, 0);
v_nextMacroScope_775_ = lean_ctor_get(v___x_773_, 1);
v_ngen_776_ = lean_ctor_get(v___x_773_, 2);
v_auxDeclNGen_777_ = lean_ctor_get(v___x_773_, 3);
v_traceState_778_ = lean_ctor_get(v___x_773_, 4);
v_messages_779_ = lean_ctor_get(v___x_773_, 6);
v_infoState_780_ = lean_ctor_get(v___x_773_, 7);
v_snapshotTasks_781_ = lean_ctor_get(v___x_773_, 8);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_810_ == 0)
{
lean_object* v_unused_811_; 
v_unused_811_ = lean_ctor_get(v___x_773_, 5);
lean_dec(v_unused_811_);
v___x_783_ = v___x_773_;
v_isShared_784_ = v_isSharedCheck_810_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_snapshotTasks_781_);
lean_inc(v_infoState_780_);
lean_inc(v_messages_779_);
lean_inc(v_traceState_778_);
lean_inc(v_auxDeclNGen_777_);
lean_inc(v_ngen_776_);
lean_inc(v_nextMacroScope_775_);
lean_inc(v_env_774_);
lean_dec(v___x_773_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_810_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_790_; 
v___x_785_ = l_Lean_Meta_coeExt;
v___x_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_786_, 0, v_name_762_);
lean_ctor_set(v___x_786_, 1, v_info_770_);
v___x_787_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v___x_785_, v_env_774_, v___x_786_);
v___x_788_ = lean_obj_once(&l_Lean_Meta_registerCoercion___closed__2, &l_Lean_Meta_registerCoercion___closed__2_once, _init_l_Lean_Meta_registerCoercion___closed__2);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 5, v___x_788_);
lean_ctor_set(v___x_783_, 0, v___x_787_);
v___x_790_ = v___x_783_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_787_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v_nextMacroScope_775_);
lean_ctor_set(v_reuseFailAlloc_809_, 2, v_ngen_776_);
lean_ctor_set(v_reuseFailAlloc_809_, 3, v_auxDeclNGen_777_);
lean_ctor_set(v_reuseFailAlloc_809_, 4, v_traceState_778_);
lean_ctor_set(v_reuseFailAlloc_809_, 5, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_809_, 6, v_messages_779_);
lean_ctor_set(v_reuseFailAlloc_809_, 7, v_infoState_780_);
lean_ctor_set(v_reuseFailAlloc_809_, 8, v_snapshotTasks_781_);
v___x_790_ = v_reuseFailAlloc_809_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v_mctx_793_; lean_object* v_zetaDeltaFVarIds_794_; lean_object* v_postponed_795_; lean_object* v_diag_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_807_; 
v___x_791_ = lean_st_ref_set(v___y_772_, v___x_790_);
v___x_792_ = lean_st_ref_take(v___y_771_);
v_mctx_793_ = lean_ctor_get(v___x_792_, 0);
v_zetaDeltaFVarIds_794_ = lean_ctor_get(v___x_792_, 2);
v_postponed_795_ = lean_ctor_get(v___x_792_, 3);
v_diag_796_ = lean_ctor_get(v___x_792_, 4);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_807_ == 0)
{
lean_object* v_unused_808_; 
v_unused_808_ = lean_ctor_get(v___x_792_, 1);
lean_dec(v_unused_808_);
v___x_798_ = v___x_792_;
v_isShared_799_ = v_isSharedCheck_807_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_diag_796_);
lean_inc(v_postponed_795_);
lean_inc(v_zetaDeltaFVarIds_794_);
lean_inc(v_mctx_793_);
lean_dec(v___x_792_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_807_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_800_; lean_object* v___x_802_; 
v___x_800_ = lean_obj_once(&l_Lean_Meta_registerCoercion___closed__3, &l_Lean_Meta_registerCoercion___closed__3_once, _init_l_Lean_Meta_registerCoercion___closed__3);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 1, v___x_800_);
v___x_802_ = v___x_798_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_mctx_793_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v___x_800_);
lean_ctor_set(v_reuseFailAlloc_806_, 2, v_zetaDeltaFVarIds_794_);
lean_ctor_set(v_reuseFailAlloc_806_, 3, v_postponed_795_);
lean_ctor_set(v_reuseFailAlloc_806_, 4, v_diag_796_);
v___x_802_ = v_reuseFailAlloc_806_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_803_ = lean_st_ref_set(v___y_771_, v___x_802_);
v___x_804_ = lean_box(0);
v___x_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
return v___x_805_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerCoercion___boxed(lean_object* v_name_861_, lean_object* v_info_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lean_Meta_registerCoercion(v_name_861_, v_info_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
lean_dec(v_a_866_);
lean_dec_ref(v_a_865_);
lean_dec(v_a_864_);
lean_dec_ref(v_a_863_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2(lean_object* v_00_u03b1_869_, lean_object* v_msg_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2___redArg(v_msg_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2___boxed(lean_object* v_00_u03b1_877_, lean_object* v_msg_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2(v_00_u03b1_877_, v_msg_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_885_, lean_object* v_constName_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1___redArg(v_constName_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_893_, lean_object* v_constName_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1(v_00_u03b1_893_, v_constName_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b1_901_, lean_object* v_ref_902_, lean_object* v_constName_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg(v_ref_902_, v_constName_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b1_910_, lean_object* v_ref_911_, lean_object* v_constName_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5(v_00_u03b1_910_, v_ref_911_, v_constName_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v_ref_911_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7(lean_object* v_00_u03b1_919_, lean_object* v_ref_920_, lean_object* v_msg_921_, lean_object* v_declHint_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7___redArg(v_ref_920_, v_msg_921_, v_declHint_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7___boxed(lean_object* v_00_u03b1_929_, lean_object* v_ref_930_, lean_object* v_msg_931_, lean_object* v_declHint_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7(v_00_u03b1_929_, v_ref_930_, v_msg_931_, v_declHint_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v_ref_930_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9(lean_object* v_msg_939_, lean_object* v_declHint_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_939_, v_declHint_940_, v___y_944_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_947_, lean_object* v_declHint_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9(v_msg_947_, v_declHint_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_955_, lean_object* v_ref_956_, lean_object* v_msg_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___redArg(v_ref_956_, v_msg_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_964_, lean_object* v_ref_965_, lean_object* v_msg_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9(v_00_u03b1_964_, v_ref_965_, v_msg_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v_ref_965_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(lean_object* v_decl_973_, lean_object* v_____r_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = lean_box(0);
v___x_981_ = l_Lean_Meta_registerCoercion(v_decl_973_, v___x_980_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2____boxed(lean_object* v_decl_982_, lean_object* v_____r_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(v_decl_982_, v_____r_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
return v_res_989_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__0));
v___x_992_ = l_Lean_stringToMessageData(v___x_991_);
return v___x_992_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__2));
v___x_995_ = l_Lean_stringToMessageData(v___x_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg(lean_object* v_name_999_, uint8_t v_kind_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___y_1012_; 
v___x_1006_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__1);
v___x_1007_ = l_Lean_MessageData_ofName(v_name_999_);
v___x_1008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1006_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
v___x_1009_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__3);
v___x_1010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1008_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
switch(v_kind_1000_)
{
case 0:
{
lean_object* v___x_1019_; 
v___x_1019_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__4));
v___y_1012_ = v___x_1019_;
goto v___jp_1011_;
}
case 1:
{
lean_object* v___x_1020_; 
v___x_1020_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__5));
v___y_1012_ = v___x_1020_;
goto v___jp_1011_;
}
default: 
{
lean_object* v___x_1021_; 
v___x_1021_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__6));
v___y_1012_ = v___x_1021_;
goto v___jp_1011_;
}
}
v___jp_1011_:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
lean_inc_ref(v___y_1012_);
v___x_1013_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1013_, 0, v___y_1012_);
v___x_1014_ = l_Lean_MessageData_ofFormat(v___x_1013_);
v___x_1015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1010_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3);
v___x_1017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1015_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2___redArg(v___x_1017_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
return v___x_1018_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_name_1022_, lean_object* v_kind_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
uint8_t v_kind_boxed_1029_; lean_object* v_res_1030_; 
v_kind_boxed_1029_ = lean_unbox(v_kind_1023_);
v_res_1030_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg(v_name_1022_, v_kind_boxed_1029_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
return v_res_1030_;
}
}
static uint64_t _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1037_; uint64_t v___x_1038_; 
v___x_1037_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_));
v___x_1038_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1037_);
return v___x_1038_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1039_ = lean_uint64_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1040_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_));
v___x_1041_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
lean_ctor_set_uint64(v___x_1041_, sizeof(void*)*1, v___x_1039_);
return v___x_1041_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1042_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
return v___x_1044_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1046_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
lean_ctor_set(v___x_1046_, 2, v___x_1045_);
lean_ctor_set(v___x_1046_, 3, v___x_1045_);
lean_ctor_set(v___x_1046_, 4, v___x_1045_);
lean_ctor_set(v___x_1046_, 5, v___x_1045_);
return v___x_1046_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1048_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
lean_ctor_set(v___x_1048_, 2, v___x_1047_);
lean_ctor_set(v___x_1048_, 3, v___x_1047_);
lean_ctor_set(v___x_1048_, 4, v___x_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(lean_object* v___x_1049_, lean_object* v___x_1050_, lean_object* v___x_1051_, lean_object* v_decl_1052_, lean_object* v___stx_1053_, uint8_t v_kind_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
uint8_t v___x_1058_; uint8_t v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; size_t v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___y_1078_; uint8_t v___x_1088_; uint8_t v___x_1089_; 
v___x_1058_ = 1;
v___x_1059_ = 0;
v___x_1060_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1061_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1062_ = lean_unsigned_to_nat(32u);
v___x_1063_ = lean_mk_empty_array_with_capacity(v___x_1062_);
v___x_1064_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_1065_ = ((size_t)5ULL);
lean_inc_n(v___x_1049_, 6);
v___x_1066_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1066_, 0, v___x_1064_);
lean_ctor_set(v___x_1066_, 1, v___x_1063_);
lean_ctor_set(v___x_1066_, 2, v___x_1049_);
lean_ctor_set(v___x_1066_, 3, v___x_1049_);
lean_ctor_set_usize(v___x_1066_, 4, v___x_1065_);
v___x_1067_ = lean_box(1);
lean_inc_ref(v___x_1066_);
v___x_1068_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1061_);
lean_ctor_set(v___x_1068_, 1, v___x_1066_);
lean_ctor_set(v___x_1068_, 2, v___x_1067_);
v___x_1069_ = lean_mk_empty_array_with_capacity(v___x_1049_);
v___x_1070_ = lean_box(0);
lean_inc(v___x_1050_);
v___x_1071_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1071_, 0, v___x_1060_);
lean_ctor_set(v___x_1071_, 1, v___x_1050_);
lean_ctor_set(v___x_1071_, 2, v___x_1068_);
lean_ctor_set(v___x_1071_, 3, v___x_1069_);
lean_ctor_set(v___x_1071_, 4, v___x_1070_);
lean_ctor_set(v___x_1071_, 5, v___x_1049_);
lean_ctor_set(v___x_1071_, 6, v___x_1070_);
lean_ctor_set_uint8(v___x_1071_, sizeof(void*)*7, v___x_1059_);
lean_ctor_set_uint8(v___x_1071_, sizeof(void*)*7 + 1, v___x_1059_);
lean_ctor_set_uint8(v___x_1071_, sizeof(void*)*7 + 2, v___x_1059_);
lean_ctor_set_uint8(v___x_1071_, sizeof(void*)*7 + 3, v___x_1058_);
v___x_1072_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1049_);
lean_ctor_set(v___x_1072_, 1, v___x_1049_);
lean_ctor_set(v___x_1072_, 2, v___x_1049_);
lean_ctor_set(v___x_1072_, 3, v___x_1049_);
lean_ctor_set(v___x_1072_, 4, v___x_1061_);
lean_ctor_set(v___x_1072_, 5, v___x_1061_);
lean_ctor_set(v___x_1072_, 6, v___x_1061_);
lean_ctor_set(v___x_1072_, 7, v___x_1061_);
lean_ctor_set(v___x_1072_, 8, v___x_1061_);
lean_ctor_set(v___x_1072_, 9, v___x_1061_);
v___x_1073_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1074_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1075_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1072_);
lean_ctor_set(v___x_1075_, 1, v___x_1073_);
lean_ctor_set(v___x_1075_, 2, v___x_1050_);
lean_ctor_set(v___x_1075_, 3, v___x_1066_);
lean_ctor_set(v___x_1075_, 4, v___x_1074_);
v___x_1076_ = lean_st_mk_ref(v___x_1075_);
v___x_1088_ = 0;
v___x_1089_ = l_Lean_instBEqAttributeKind_beq(v_kind_1054_, v___x_1088_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; 
lean_dec(v_decl_1052_);
v___x_1090_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg(v___x_1051_, v_kind_1054_, v___x_1071_, v___x_1076_, v___y_1055_, v___y_1056_);
lean_dec_ref_known(v___x_1071_, 7);
v___y_1078_ = v___x_1090_;
goto v___jp_1077_;
}
else
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
lean_dec(v___x_1051_);
v___x_1091_ = lean_box(0);
v___x_1092_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(v_decl_1052_, v___x_1091_, v___x_1071_, v___x_1076_, v___y_1055_, v___y_1056_);
lean_dec_ref_known(v___x_1071_, 7);
v___y_1078_ = v___x_1092_;
goto v___jp_1077_;
}
v___jp_1077_:
{
if (lean_obj_tag(v___y_1078_) == 0)
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1087_; 
v_a_1079_ = lean_ctor_get(v___y_1078_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___y_1078_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1081_ = v___y_1078_;
v_isShared_1082_ = v_isSharedCheck_1087_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___y_1078_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1087_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1083_; lean_object* v___x_1085_; 
v___x_1083_ = lean_st_ref_get(v___x_1076_);
lean_dec(v___x_1076_);
lean_dec(v___x_1083_);
if (v_isShared_1082_ == 0)
{
v___x_1085_ = v___x_1081_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1079_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
else
{
lean_dec(v___x_1076_);
return v___y_1078_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2____boxed(lean_object* v___x_1093_, lean_object* v___x_1094_, lean_object* v___x_1095_, lean_object* v_decl_1096_, lean_object* v___stx_1097_, lean_object* v_kind_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
uint8_t v_kind_boxed_1102_; lean_object* v_res_1103_; 
v_kind_boxed_1102_ = lean_unbox(v_kind_1098_);
v_res_1103_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(v___x_1093_, v___x_1094_, v___x_1095_, v_decl_1096_, v___stx_1097_, v_kind_boxed_1102_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___stx_1097_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v___x_1108_; lean_object* v_env_1109_; lean_object* v_options_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1108_ = lean_st_ref_get(v___y_1106_);
v_env_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc_ref(v_env_1109_);
lean_dec(v___x_1108_);
v_options_1110_ = lean_ctor_get(v___y_1105_, 2);
v___x_1111_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_1112_ = lean_unsigned_to_nat(32u);
v___x_1113_ = lean_mk_empty_array_with_capacity(v___x_1112_);
lean_dec_ref(v___x_1113_);
v___x_1114_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
lean_inc_ref(v_options_1110_);
v___x_1115_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1115_, 0, v_env_1109_);
lean_ctor_set(v___x_1115_, 1, v___x_1111_);
lean_ctor_set(v___x_1115_, 2, v___x_1114_);
lean_ctor_set(v___x_1115_, 3, v_options_1110_);
v___x_1116_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
lean_ctor_set(v___x_1116_, 1, v_msgData_1104_);
v___x_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0_spec__0(v_msgData_1118_, v___y_1119_, v___y_1120_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v_ref_1127_; lean_object* v___x_1128_; lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1137_; 
v_ref_1127_ = lean_ctor_get(v___y_1124_, 5);
v___x_1128_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0_spec__0(v_msg_1123_, v___y_1124_, v___y_1125_);
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1131_ = v___x_1128_;
v_isShared_1132_ = v_isSharedCheck_1137_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1128_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1137_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1133_; lean_object* v___x_1135_; 
lean_inc(v_ref_1127_);
v___x_1133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1133_, 0, v_ref_1127_);
lean_ctor_set(v___x_1133_, 1, v_a_1129_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set_tag(v___x_1131_, 1);
lean_ctor_set(v___x_1131_, 0, v___x_1133_);
v___x_1135_ = v___x_1131_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0___redArg(v_msg_1138_, v___y_1139_, v___y_1140_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
return v_res_1142_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_));
v___x_1145_ = l_Lean_stringToMessageData(v___x_1144_);
return v___x_1145_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_));
v___x_1148_ = l_Lean_stringToMessageData(v___x_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(lean_object* v___x_1149_, lean_object* v_decl_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1154_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1155_ = l_Lean_MessageData_ofName(v___x_1149_);
v___x_1156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1154_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1156_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
v___x_1159_ = l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0___redArg(v___x_1158_, v___y_1151_, v___y_1152_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2____boxed(lean_object* v___x_1160_, lean_object* v_decl_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(v___x_1160_, v_decl_1161_, v___y_1162_, v___y_1163_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v_decl_1161_);
return v_res_1165_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1206_ = lean_unsigned_to_nat(3842861879u);
v___x_1207_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_));
v___x_1208_ = l_Lean_Name_num___override(v___x_1207_, v___x_1206_);
return v___x_1208_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1210_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_));
v___x_1211_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1212_ = l_Lean_Name_str___override(v___x_1211_, v___x_1210_);
return v___x_1212_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1214_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_));
v___x_1215_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1216_ = l_Lean_Name_str___override(v___x_1215_, v___x_1214_);
return v___x_1216_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1217_ = lean_unsigned_to_nat(2u);
v___x_1218_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1219_ = l_Lean_Name_num___override(v___x_1218_, v___x_1217_);
return v___x_1219_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1229_ = 0;
v___x_1230_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_));
v___x_1231_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_));
v___x_1232_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1233_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
lean_ctor_set(v___x_1233_, 1, v___x_1231_);
lean_ctor_set(v___x_1233_, 2, v___x_1230_);
lean_ctor_set_uint8(v___x_1233_, sizeof(void*)*3, v___x_1229_);
return v___x_1233_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1234_; lean_object* v___f_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___f_1234_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_));
v___f_1235_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_));
v___x_1236_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1237_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
lean_ctor_set(v___x_1237_, 1, v___f_1235_);
lean_ctor_set(v___x_1237_, 2, v___f_1234_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1240_ = l_Lean_registerBuiltinAttribute(v___x_1239_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2____boxed(lean_object* v_a_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_();
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1243_, lean_object* v_msg_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v___x_1248_; 
v___x_1248_ = l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0___redArg(v_msg_1244_, v___y_1245_, v___y_1246_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1249_, lean_object* v_msg_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0(v_00_u03b1_1249_, v_msg_1250_, v___y_1251_, v___y_1252_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b1_1255_, lean_object* v_name_1256_, uint8_t v_kind_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg(v_name_1256_, v_kind_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b1_1264_, lean_object* v_name_1265_, lean_object* v_kind_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
uint8_t v_kind_boxed_1272_; lean_object* v_res_1273_; 
v_kind_boxed_1272_ = lean_unbox(v_kind_1266_);
v_res_1273_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1(v_00_u03b1_1264_, v_name_1265_, v_kind_boxed_1272_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
return v_res_1273_;
}
}
lean_object* runtime_initialize_Lean_Meta_FunInfo(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_CoeAttr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

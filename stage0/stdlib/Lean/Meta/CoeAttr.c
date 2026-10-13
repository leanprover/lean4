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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
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
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 8, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__27;
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
static const lean_string_object l_Lean_Meta_registerCoercion___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = " has no explicit arguments"};
static const lean_object* l_Lean_Meta_registerCoercion___closed__3 = (const lean_object*)&l_Lean_Meta_registerCoercion___closed__3_value;
static lean_once_cell_t l_Lean_Meta_registerCoercion___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_registerCoercion___closed__4;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(lean_object* v_st_318_, lean_object* v_x_319_){
_start:
{
lean_object* v_fst_320_; lean_object* v_snd_321_; lean_object* v___x_322_; 
v_fst_320_ = lean_ctor_get(v_x_319_, 0);
lean_inc(v_fst_320_);
v_snd_321_ = lean_ctor_get(v_x_319_, 1);
lean_inc(v_snd_321_);
lean_dec_ref(v_x_319_);
v___x_322_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_320_, v_snd_321_, v_st_318_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(lean_object* v_x_323_, lean_object* v_a_324_){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_325_, 0, v_a_324_);
lean_inc_ref_n(v___x_325_, 2);
v___x_326_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
lean_ctor_set(v___x_326_, 2, v___x_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed(lean_object* v_x_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(v_x_327_, v_a_328_);
lean_dec_ref(v_x_327_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(lean_object* v___y_330_){
_start:
{
lean_inc(v___y_330_);
return v___y_330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed(lean_object* v___y_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(v___y_331_);
lean_dec(v___y_331_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_));
v___x_351_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed(lean_object* v_a_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_();
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCoeFnInfo_x3f___redArg(lean_object* v_fn_354_, lean_object* v_a_355_){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v_env_359_; lean_object* v___x_360_; lean_object* v_ext_361_; lean_object* v_toEnvExtension_362_; lean_object* v_asyncMode_363_; uint8_t v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_357_ = lean_box(1);
v___x_358_ = lean_st_ref_get(v_a_355_);
v_env_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc_ref(v_env_359_);
lean_dec(v___x_358_);
v___x_360_ = l_Lean_Meta_coeExt;
v_ext_361_ = lean_ctor_get(v___x_360_, 1);
v_toEnvExtension_362_ = lean_ctor_get(v_ext_361_, 0);
v_asyncMode_363_ = lean_ctor_get(v_toEnvExtension_362_, 2);
v___x_364_ = 0;
v___x_365_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_357_, v___x_360_, v_env_359_, v_asyncMode_363_, v___x_364_);
v___x_366_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_365_, v_fn_354_);
lean_dec(v___x_365_);
v___x_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCoeFnInfo_x3f___redArg___boxed(lean_object* v_fn_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_Meta_getCoeFnInfo_x3f___redArg(v_fn_368_, v_a_369_);
lean_dec(v_a_369_);
lean_dec(v_fn_368_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCoeFnInfo_x3f(lean_object* v_fn_372_, lean_object* v_a_373_, lean_object* v_a_374_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_Meta_getCoeFnInfo_x3f___redArg(v_fn_372_, v_a_374_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCoeFnInfo_x3f___boxed(lean_object* v_fn_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_Meta_getCoeFnInfo_x3f(v_fn_377_, v_a_378_, v_a_379_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec(v_fn_377_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2_spec__4(lean_object* v_msgData_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v___x_388_; lean_object* v_env_389_; uint8_t v___x_390_; lean_object* v_env_391_; lean_object* v___x_392_; lean_object* v_toCold_393_; lean_object* v_mctx_394_; lean_object* v_lctx_395_; lean_object* v_options_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_388_ = lean_st_ref_get(v___y_386_);
v_env_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc_ref(v_env_389_);
lean_dec(v___x_388_);
v___x_390_ = 0;
v_env_391_ = l_Lean_Environment_setRecordingDeps(v_env_389_, v___x_390_);
v___x_392_ = lean_st_ref_get(v___y_384_);
v_toCold_393_ = lean_ctor_get(v___y_385_, 0);
v_mctx_394_ = lean_ctor_get(v___x_392_, 0);
lean_inc_ref(v_mctx_394_);
lean_dec(v___x_392_);
v_lctx_395_ = lean_ctor_get(v___y_383_, 2);
v_options_396_ = lean_ctor_get(v_toCold_393_, 2);
lean_inc_ref(v_options_396_);
lean_inc_ref(v_lctx_395_);
v___x_397_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_397_, 0, v_env_391_);
lean_ctor_set(v___x_397_, 1, v_mctx_394_);
lean_ctor_set(v___x_397_, 2, v_lctx_395_);
lean_ctor_set(v___x_397_, 3, v_options_396_);
v___x_398_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
lean_ctor_set(v___x_398_, 1, v_msgData_382_);
v___x_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2_spec__4___boxed(lean_object* v_msgData_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2_spec__4(v_msgData_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2___redArg(lean_object* v_msg_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v_ref_413_; lean_object* v___x_414_; lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_423_; 
v_ref_413_ = lean_ctor_get(v___y_410_, 2);
v___x_414_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2_spec__4(v_msg_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
v_a_415_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_423_ == 0)
{
v___x_417_ = v___x_414_;
v_isShared_418_ = v_isSharedCheck_423_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_423_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v___x_421_; 
lean_inc(v_ref_413_);
v___x_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_419_, 0, v_ref_413_);
lean_ctor_set(v___x_419_, 1, v_a_415_);
if (v_isShared_418_ == 0)
{
lean_ctor_set_tag(v___x_417_, 1);
lean_ctor_set(v___x_417_, 0, v___x_419_);
v___x_421_ = v___x_417_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_419_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2___redArg___boxed(lean_object* v_msg_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2___redArg(v_msg_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___redArg(lean_object* v_ref_431_, lean_object* v_msg_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_toCold_438_; lean_object* v_currRecDepth_439_; lean_object* v_ref_440_; uint16_t v_optionFlags_441_; uint8_t v_suppressElabErrors_442_; uint8_t v_isRecordingDeps_443_; lean_object* v_ref_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v_toCold_438_ = lean_ctor_get(v___y_435_, 0);
v_currRecDepth_439_ = lean_ctor_get(v___y_435_, 1);
v_ref_440_ = lean_ctor_get(v___y_435_, 2);
v_optionFlags_441_ = lean_ctor_get_uint16(v___y_435_, sizeof(void*)*3);
v_suppressElabErrors_442_ = lean_ctor_get_uint8(v___y_435_, sizeof(void*)*3 + 2);
v_isRecordingDeps_443_ = lean_ctor_get_uint8(v___y_435_, sizeof(void*)*3 + 3);
v_ref_444_ = l_Lean_replaceRef(v_ref_431_, v_ref_440_);
lean_inc(v_currRecDepth_439_);
lean_inc_ref(v_toCold_438_);
v___x_445_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_445_, 0, v_toCold_438_);
lean_ctor_set(v___x_445_, 1, v_currRecDepth_439_);
lean_ctor_set(v___x_445_, 2, v_ref_444_);
lean_ctor_set_uint16(v___x_445_, sizeof(void*)*3, v_optionFlags_441_);
lean_ctor_set_uint8(v___x_445_, sizeof(void*)*3 + 2, v_suppressElabErrors_442_);
lean_ctor_set_uint8(v___x_445_, sizeof(void*)*3 + 3, v_isRecordingDeps_443_);
v___x_446_ = l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2___redArg(v_msg_432_, v___y_433_, v___y_434_, v___x_445_, v___y_436_);
lean_dec_ref_known(v___x_445_, 3);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_ref_447_, lean_object* v_msg_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___redArg(v_ref_447_, v_msg_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v_ref_447_);
return v_res_454_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_455_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
return v___x_457_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_458_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_459_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_460_ = lean_unsigned_to_nat(0u);
v___x_461_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
lean_ctor_set(v___x_461_, 2, v___x_460_);
lean_ctor_set(v___x_461_, 3, v___x_460_);
lean_ctor_set(v___x_461_, 4, v___x_459_);
lean_ctor_set(v___x_461_, 5, v___x_459_);
lean_ctor_set(v___x_461_, 6, v___x_459_);
lean_ctor_set(v___x_461_, 7, v___x_459_);
lean_ctor_set(v___x_461_, 8, v___x_459_);
lean_ctor_set(v___x_461_, 9, v___x_459_);
lean_ctor_set(v___x_461_, 10, v___x_459_);
lean_ctor_set(v___x_461_, 11, v___x_458_);
return v___x_461_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_462_ = lean_unsigned_to_nat(32u);
v___x_463_ = lean_mk_empty_array_with_capacity(v___x_462_);
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
return v___x_464_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__4(void){
_start:
{
size_t v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_465_ = ((size_t)5ULL);
v___x_466_ = lean_unsigned_to_nat(0u);
v___x_467_ = lean_unsigned_to_nat(32u);
v___x_468_ = lean_mk_empty_array_with_capacity(v___x_467_);
v___x_469_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_470_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_470_, 0, v___x_469_);
lean_ctor_set(v___x_470_, 1, v___x_468_);
lean_ctor_set(v___x_470_, 2, v___x_466_);
lean_ctor_set(v___x_470_, 3, v___x_466_);
lean_ctor_set_usize(v___x_470_, 4, v___x_465_);
return v___x_470_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_471_ = lean_box(1);
v___x_472_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_473_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_474_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
lean_ctor_set(v___x_474_, 1, v___x_472_);
lean_ctor_set(v___x_474_, 2, v___x_471_);
return v___x_474_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_477_ = l_Lean_stringToMessageData(v___x_476_);
return v___x_477_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_480_ = l_Lean_stringToMessageData(v___x_479_);
return v___x_480_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_483_ = l_Lean_stringToMessageData(v___x_482_);
return v___x_483_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_486_ = l_Lean_stringToMessageData(v___x_485_);
return v___x_486_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__15(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__14));
v___x_489_ = l_Lean_stringToMessageData(v___x_488_);
return v___x_489_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__17(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__16));
v___x_492_ = l_Lean_stringToMessageData(v___x_491_);
return v___x_492_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__19(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__18));
v___x_495_ = l_Lean_stringToMessageData(v___x_494_);
return v___x_495_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__21(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__20));
v___x_498_ = l_Lean_stringToMessageData(v___x_497_);
return v___x_498_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__23(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__22));
v___x_501_ = l_Lean_stringToMessageData(v___x_500_);
return v___x_501_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__25(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__24));
v___x_504_ = l_Lean_stringToMessageData(v___x_503_);
return v___x_504_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__27(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__26));
v___x_507_ = l_Lean_stringToMessageData(v___x_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_508_, lean_object* v_declHint_509_, lean_object* v___y_510_){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v_env_514_; uint8_t v___x_515_; 
v___x_512_ = lean_box(0);
v___x_513_ = lean_st_ref_get(v___y_510_);
v_env_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc_ref(v_env_514_);
lean_dec(v___x_513_);
v___x_515_ = l_Lean_Name_isAnonymous(v_declHint_509_);
if (v___x_515_ == 0)
{
uint8_t v_isExporting_516_; 
v_isExporting_516_ = lean_ctor_get_uint8(v_env_514_, sizeof(void*)*13);
if (v_isExporting_516_ == 0)
{
lean_object* v___x_517_; 
lean_dec_ref(v_env_514_);
lean_dec(v_declHint_509_);
v___x_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_517_, 0, v_msg_508_);
return v___x_517_;
}
else
{
lean_object* v___x_518_; uint8_t v___x_519_; 
lean_inc_ref(v_env_514_);
v___x_518_ = l_Lean_Environment_setExporting(v_env_514_, v___x_515_);
lean_inc(v_declHint_509_);
lean_inc_ref(v___x_518_);
v___x_519_ = l_Lean_Environment_contains(v___x_518_, v_declHint_509_, v_isExporting_516_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; 
lean_dec_ref(v___x_518_);
lean_dec_ref(v_env_514_);
lean_dec(v_declHint_509_);
v___x_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_520_, 0, v_msg_508_);
return v___x_520_;
}
else
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v_c_526_; lean_object* v___x_527_; 
v___x_521_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_522_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_523_ = l_Lean_Options_empty;
v___x_524_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_524_, 0, v___x_518_);
lean_ctor_set(v___x_524_, 1, v___x_521_);
lean_ctor_set(v___x_524_, 2, v___x_522_);
lean_ctor_set(v___x_524_, 3, v___x_523_);
lean_inc(v_declHint_509_);
v___x_525_ = l_Lean_MessageData_ofConstName(v_declHint_509_, v___x_515_);
v_c_526_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_526_, 0, v___x_524_);
lean_ctor_set(v_c_526_, 1, v___x_525_);
v___x_527_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_514_, v_declHint_509_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
lean_dec_ref(v_env_514_);
lean_dec(v_declHint_509_);
v___x_528_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
lean_ctor_set(v___x_529_, 1, v_c_526_);
v___x_530_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_529_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = l_Lean_MessageData_note(v___x_531_);
v___x_533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_533_, 0, v_msg_508_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
return v___x_534_;
}
else
{
lean_object* v_val_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_591_; 
v_val_535_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_591_ == 0)
{
v___x_537_ = v___x_527_;
v_isShared_538_ = v_isSharedCheck_591_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_val_535_);
lean_dec(v___x_527_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_591_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_539_; lean_object* v_modules_540_; lean_object* v_moduleNames_541_; lean_object* v_mod_542_; uint8_t v___y_544_; uint8_t v___x_574_; 
v___x_539_ = l_Lean_Environment_header(v_env_514_);
lean_dec_ref(v_env_514_);
v_modules_540_ = lean_ctor_get(v___x_539_, 3);
lean_inc_ref(v_modules_540_);
v_moduleNames_541_ = lean_ctor_get(v___x_539_, 4);
lean_inc_ref(v_moduleNames_541_);
lean_dec_ref(v___x_539_);
v_mod_542_ = lean_array_get(v___x_512_, v_moduleNames_541_, v_val_535_);
lean_dec_ref(v_moduleNames_541_);
v___x_574_ = l_Lean_isPrivateName(v_declHint_509_);
lean_dec(v_declHint_509_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_575_ = lean_array_get_size(v_modules_540_);
v___x_576_ = lean_nat_dec_lt(v_val_535_, v___x_575_);
if (v___x_576_ == 0)
{
lean_dec_ref(v_modules_540_);
lean_dec(v_val_535_);
v___y_544_ = v___x_574_;
goto v___jp_543_;
}
else
{
lean_object* v___x_577_; lean_object* v_toImport_578_; uint8_t v_isExported_579_; 
v___x_577_ = lean_array_fget(v_modules_540_, v_val_535_);
lean_dec(v_val_535_);
lean_dec_ref(v_modules_540_);
v_toImport_578_ = lean_ctor_get(v___x_577_, 0);
lean_inc_ref(v_toImport_578_);
lean_dec(v___x_577_);
v_isExported_579_ = lean_ctor_get_uint8(v_toImport_578_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_578_);
v___y_544_ = v_isExported_579_;
goto v___jp_543_;
}
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
lean_dec_ref(v_modules_540_);
lean_del_object(v___x_537_);
lean_dec(v_val_535_);
v___x_580_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v_c_526_);
v___x_582_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__25);
v___x_583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_581_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
v___x_584_ = l_Lean_MessageData_ofName(v_mod_542_);
v___x_585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_583_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v___x_586_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__27);
v___x_587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_585_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
v___x_588_ = l_Lean_MessageData_note(v___x_587_);
v___x_589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_589_, 0, v_msg_508_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
v___x_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
return v___x_590_;
}
v___jp_543_:
{
if (v___y_544_ == 0)
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_545_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
lean_ctor_set(v___x_546_, 1, v_c_526_);
v___x_547_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_546_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
v___x_549_ = l_Lean_MessageData_ofName(v_mod_542_);
v___x_550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_548_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
v___x_551_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_550_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = l_Lean_MessageData_note(v___x_552_);
v___x_554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_554_, 0, v_msg_508_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
if (v_isShared_538_ == 0)
{
lean_ctor_set_tag(v___x_537_, 0);
lean_ctor_set(v___x_537_, 0, v___x_554_);
v___x_556_ = v___x_537_;
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
else
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_572_; 
v___x_558_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
lean_ctor_set(v___x_559_, 1, v_c_526_);
v___x_560_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__19);
v___x_561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_559_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
v___x_562_ = l_Lean_MessageData_ofName(v_mod_542_);
lean_inc_ref(v___x_562_);
v___x_563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_561_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
v___x_564_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__21);
v___x_565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_563_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
v___x_566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
lean_ctor_set(v___x_566_, 1, v___x_562_);
v___x_567_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__23);
v___x_568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_566_);
lean_ctor_set(v___x_568_, 1, v___x_567_);
v___x_569_ = l_Lean_MessageData_note(v___x_568_);
v___x_570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_570_, 0, v_msg_508_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
if (v_isShared_538_ == 0)
{
lean_ctor_set_tag(v___x_537_, 0);
lean_ctor_set(v___x_537_, 0, v___x_570_);
v___x_572_ = v___x_537_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_570_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_592_; 
lean_dec_ref(v_env_514_);
lean_dec(v_declHint_509_);
v___x_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_592_, 0, v_msg_508_);
return v___x_592_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_593_, lean_object* v_declHint_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_593_, v_declHint_594_, v___y_595_);
lean_dec(v___y_595_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8(lean_object* v_msg_598_, lean_object* v_declHint_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v___x_605_; lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_615_; 
v___x_605_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_598_, v_declHint_599_, v___y_603_);
v_a_606_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_615_ == 0)
{
v___x_608_ = v___x_605_;
v_isShared_609_ = v_isSharedCheck_615_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_605_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_615_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_610_ = l_Lean_unknownIdentifierMessageTag;
v___x_611_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
lean_ctor_set(v___x_611_, 1, v_a_606_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v___x_611_);
v___x_613_ = v___x_608_;
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8___boxed(lean_object* v_msg_616_, lean_object* v_declHint_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8(v_msg_616_, v_declHint_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7___redArg(lean_object* v_ref_624_, lean_object* v_msg_625_, lean_object* v_declHint_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v___x_632_; lean_object* v_a_633_; lean_object* v___x_634_; 
v___x_632_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8(v_msg_625_, v_declHint_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref(v___x_632_);
v___x_634_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___redArg(v_ref_624_, v_a_633_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7___redArg___boxed(lean_object* v_ref_635_, lean_object* v_msg_636_, lean_object* v_declHint_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7___redArg(v_ref_635_, v_msg_636_, v_declHint_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v_ref_635_);
return v_res_643_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__0));
v___x_646_ = l_Lean_stringToMessageData(v___x_645_);
return v___x_646_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__2));
v___x_649_ = l_Lean_stringToMessageData(v___x_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_ref_650_, lean_object* v_constName_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v___x_657_; uint8_t v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_657_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__1);
v___x_658_ = 0;
lean_inc(v_constName_651_);
v___x_659_ = l_Lean_MessageData_ofConstName(v_constName_651_, v___x_658_);
v___x_660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_657_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
v___x_661_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3);
v___x_662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_660_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7___redArg(v_ref_650_, v___x_662_, v_constName_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_ref_664_, lean_object* v_constName_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg(v_ref_664_, v_constName_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v_ref_664_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_ref_678_; lean_object* v___x_679_; 
v_ref_678_ = lean_ctor_get(v___y_675_, 2);
v___x_679_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg(v_ref_678_, v_constName_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1___redArg(v_constName_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0(lean_object* v_constName_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
lean_object* v___x_693_; lean_object* v_env_694_; uint8_t v___x_695_; lean_object* v___x_696_; 
v___x_693_ = lean_st_ref_get(v___y_691_);
v_env_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc_ref(v_env_694_);
lean_dec(v___x_693_);
v___x_695_ = 0;
lean_inc(v_constName_687_);
v___x_696_ = l_Lean_Environment_findConstVal_x3f(v_env_694_, v_constName_687_, v___x_695_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v___x_697_; 
v___x_697_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1___redArg(v_constName_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
return v___x_697_;
}
else
{
lean_object* v_val_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
lean_dec(v_constName_687_);
v_val_698_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_696_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_val_698_);
lean_dec(v___x_696_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
lean_ctor_set_tag(v___x_700_, 0);
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_val_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0___boxed(lean_object* v_constName_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0(v_constName_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__1(lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
if (lean_obj_tag(v_a_713_) == 0)
{
lean_object* v___x_715_; 
v___x_715_ = l_List_reverse___redArg(v_a_714_);
return v___x_715_;
}
else
{
lean_object* v_head_716_; lean_object* v_tail_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_726_; 
v_head_716_ = lean_ctor_get(v_a_713_, 0);
v_tail_717_ = lean_ctor_get(v_a_713_, 1);
v_isSharedCheck_726_ = !lean_is_exclusive(v_a_713_);
if (v_isSharedCheck_726_ == 0)
{
v___x_719_ = v_a_713_;
v_isShared_720_ = v_isSharedCheck_726_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_tail_717_);
lean_inc(v_head_716_);
lean_dec(v_a_713_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_726_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_721_; lean_object* v___x_723_; 
v___x_721_ = l_Lean_mkLevelParam(v_head_716_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 1, v_a_714_);
lean_ctor_set(v___x_719_, 0, v___x_721_);
v___x_723_ = v___x_719_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_a_714_);
v___x_723_ = v_reuseFailAlloc_725_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
v_a_713_ = v_tail_717_;
v_a_714_ = v___x_723_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0(lean_object* v_constName_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v___x_733_; 
lean_inc(v_constName_727_);
v___x_733_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0(v_constName_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_745_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_745_ == 0)
{
v___x_736_ = v___x_733_;
v_isShared_737_ = v_isSharedCheck_745_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_733_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_745_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v_levelParams_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_743_; 
v_levelParams_738_ = lean_ctor_get(v_a_734_, 1);
lean_inc(v_levelParams_738_);
lean_dec(v_a_734_);
v___x_739_ = lean_box(0);
v___x_740_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__1(v_levelParams_738_, v___x_739_);
v___x_741_ = l_Lean_mkConst(v_constName_727_, v___x_740_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v___x_741_);
v___x_743_ = v___x_736_;
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
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
lean_dec(v_constName_727_);
v_a_746_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_733_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_733_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0___boxed(lean_object* v_constName_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0(v_constName_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Meta_registerCoercion_spec__1(lean_object* v_as_761_, lean_object* v_j_762_){
_start:
{
lean_object* v___x_763_; uint8_t v___x_764_; 
v___x_763_ = lean_array_get_size(v_as_761_);
v___x_764_ = lean_nat_dec_lt(v_j_762_, v___x_763_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; 
lean_dec(v_j_762_);
v___x_765_ = lean_box(0);
return v___x_765_;
}
else
{
lean_object* v___x_766_; uint8_t v_binderInfo_767_; uint8_t v___x_768_; 
v___x_766_ = lean_array_fget_borrowed(v_as_761_, v_j_762_);
v_binderInfo_767_ = lean_ctor_get_uint8(v___x_766_, sizeof(void*)*1);
v___x_768_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_767_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = lean_unsigned_to_nat(1u);
v___x_770_ = lean_nat_add(v_j_762_, v___x_769_);
lean_dec(v_j_762_);
v_j_762_ = v___x_770_;
goto _start;
}
else
{
lean_object* v___x_772_; 
v___x_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_772_, 0, v_j_762_);
return v___x_772_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Meta_registerCoercion_spec__1___boxed(lean_object* v_as_773_, lean_object* v_j_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Array_findIdx_x3f_loop___at___00Lean_Meta_registerCoercion_spec__1(v_as_773_, v_j_774_);
lean_dec_ref(v_as_773_);
return v_res_775_;
}
}
static lean_object* _init_l_Lean_Meta_registerCoercion___closed__0(void){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
return v___x_777_;
}
}
static lean_object* _init_l_Lean_Meta_registerCoercion___closed__1(void){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = lean_obj_once(&l_Lean_Meta_registerCoercion___closed__0, &l_Lean_Meta_registerCoercion___closed__0_once, _init_l_Lean_Meta_registerCoercion___closed__0);
v___x_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
return v___x_779_;
}
}
static lean_object* _init_l_Lean_Meta_registerCoercion___closed__2(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_obj_once(&l_Lean_Meta_registerCoercion___closed__0, &l_Lean_Meta_registerCoercion___closed__0_once, _init_l_Lean_Meta_registerCoercion___closed__0);
v___x_781_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
lean_ctor_set(v___x_781_, 2, v___x_780_);
lean_ctor_set(v___x_781_, 3, v___x_780_);
lean_ctor_set(v___x_781_, 4, v___x_780_);
lean_ctor_set(v___x_781_, 5, v___x_780_);
return v___x_781_;
}
}
static lean_object* _init_l_Lean_Meta_registerCoercion___closed__4(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = ((lean_object*)(l_Lean_Meta_registerCoercion___closed__3));
v___x_784_ = l_Lean_stringToMessageData(v___x_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerCoercion(lean_object* v_name_785_, lean_object* v_info_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_info_793_; lean_object* v___y_794_; lean_object* v___y_795_; 
if (lean_obj_tag(v_info_786_) == 0)
{
lean_object* v___x_836_; 
lean_inc(v_name_785_);
v___x_836_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0(v_name_785_, v_a_787_, v_a_788_, v_a_789_, v_a_790_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v_a_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v_a_837_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_a_837_);
lean_dec_ref_known(v___x_836_, 1);
v___x_838_ = lean_box(0);
v___x_839_ = l_Lean_Meta_getFunInfo(v_a_837_, v___x_838_, v_a_787_, v_a_788_, v_a_789_, v_a_790_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v_paramInfo_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_866_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_a_840_);
lean_dec_ref_known(v___x_839_, 1);
v_paramInfo_841_ = lean_ctor_get(v_a_840_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v_a_840_);
if (v_isSharedCheck_866_ == 0)
{
lean_object* v_unused_867_; 
v_unused_867_ = lean_ctor_get(v_a_840_, 1);
lean_dec(v_unused_867_);
v___x_843_ = v_a_840_;
v_isShared_844_ = v_isSharedCheck_866_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_paramInfo_841_);
lean_dec(v_a_840_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_866_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = lean_unsigned_to_nat(0u);
v___x_846_ = l_Array_findIdx_x3f_loop___at___00Lean_Meta_registerCoercion_spec__1(v_paramInfo_841_, v___x_845_);
lean_dec_ref(v_paramInfo_841_);
if (lean_obj_tag(v___x_846_) == 1)
{
lean_object* v_val_847_; lean_object* v___x_848_; lean_object* v___x_849_; uint8_t v___x_850_; lean_object* v___x_851_; 
lean_del_object(v___x_843_);
v_val_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_val_847_);
lean_dec_ref_known(v___x_846_, 1);
v___x_848_ = lean_unsigned_to_nat(1u);
v___x_849_ = lean_nat_add(v_val_847_, v___x_848_);
v___x_850_ = 0;
v___x_851_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_851_, 0, v___x_849_);
lean_ctor_set(v___x_851_, 1, v_val_847_);
lean_ctor_set_uint8(v___x_851_, sizeof(void*)*2, v___x_850_);
v_info_793_ = v___x_851_;
v___y_794_ = v_a_788_;
v___y_795_ = v_a_790_;
goto v___jp_792_;
}
else
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_855_; 
lean_dec(v___x_846_);
v___x_852_ = l_Lean_MessageData_ofName(v_name_785_);
v___x_853_ = lean_obj_once(&l_Lean_Meta_registerCoercion___closed__4, &l_Lean_Meta_registerCoercion___closed__4_once, _init_l_Lean_Meta_registerCoercion___closed__4);
if (v_isShared_844_ == 0)
{
lean_ctor_set_tag(v___x_843_, 7);
lean_ctor_set(v___x_843_, 1, v___x_853_);
lean_ctor_set(v___x_843_, 0, v___x_852_);
v___x_855_ = v___x_843_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_852_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v___x_853_);
v___x_855_ = v_reuseFailAlloc_865_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
lean_object* v___x_856_; lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
v___x_856_ = l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2___redArg(v___x_855_, v_a_787_, v_a_788_, v_a_789_, v_a_790_);
v_a_857_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v___x_856_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_856_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_a_857_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
}
}
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
lean_dec(v_name_785_);
v_a_868_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_839_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_839_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_dec(v_name_785_);
v_a_876_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_836_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_836_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
else
{
lean_object* v_val_884_; 
v_val_884_ = lean_ctor_get(v_info_786_, 0);
lean_inc(v_val_884_);
lean_dec_ref_known(v_info_786_, 1);
v_info_793_ = v_val_884_;
v___y_794_ = v_a_788_;
v___y_795_ = v_a_790_;
goto v___jp_792_;
}
v___jp_792_:
{
lean_object* v___x_796_; lean_object* v_env_797_; lean_object* v_nextMacroScope_798_; lean_object* v_ngen_799_; lean_object* v_auxDeclNGen_800_; lean_object* v_traceState_801_; lean_object* v_recordedDeps_802_; lean_object* v_messages_803_; lean_object* v_infoState_804_; lean_object* v_snapshotTasks_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_834_; 
v___x_796_ = lean_st_ref_take(v___y_795_);
v_env_797_ = lean_ctor_get(v___x_796_, 0);
v_nextMacroScope_798_ = lean_ctor_get(v___x_796_, 1);
v_ngen_799_ = lean_ctor_get(v___x_796_, 2);
v_auxDeclNGen_800_ = lean_ctor_get(v___x_796_, 3);
v_traceState_801_ = lean_ctor_get(v___x_796_, 4);
v_recordedDeps_802_ = lean_ctor_get(v___x_796_, 6);
v_messages_803_ = lean_ctor_get(v___x_796_, 7);
v_infoState_804_ = lean_ctor_get(v___x_796_, 8);
v_snapshotTasks_805_ = lean_ctor_get(v___x_796_, 9);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_834_ == 0)
{
lean_object* v_unused_835_; 
v_unused_835_ = lean_ctor_get(v___x_796_, 5);
lean_dec(v_unused_835_);
v___x_807_ = v___x_796_;
v_isShared_808_ = v_isSharedCheck_834_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_snapshotTasks_805_);
lean_inc(v_infoState_804_);
lean_inc(v_messages_803_);
lean_inc(v_recordedDeps_802_);
lean_inc(v_traceState_801_);
lean_inc(v_auxDeclNGen_800_);
lean_inc(v_ngen_799_);
lean_inc(v_nextMacroScope_798_);
lean_inc(v_env_797_);
lean_dec(v___x_796_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_834_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_814_; 
v___x_809_ = l_Lean_Meta_coeExt;
v___x_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_810_, 0, v_name_785_);
lean_ctor_set(v___x_810_, 1, v_info_793_);
v___x_811_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v___x_809_, v_env_797_, v___x_810_);
v___x_812_ = lean_obj_once(&l_Lean_Meta_registerCoercion___closed__1, &l_Lean_Meta_registerCoercion___closed__1_once, _init_l_Lean_Meta_registerCoercion___closed__1);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 5, v___x_812_);
lean_ctor_set(v___x_807_, 0, v___x_811_);
v___x_814_ = v___x_807_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_nextMacroScope_798_);
lean_ctor_set(v_reuseFailAlloc_833_, 2, v_ngen_799_);
lean_ctor_set(v_reuseFailAlloc_833_, 3, v_auxDeclNGen_800_);
lean_ctor_set(v_reuseFailAlloc_833_, 4, v_traceState_801_);
lean_ctor_set(v_reuseFailAlloc_833_, 5, v___x_812_);
lean_ctor_set(v_reuseFailAlloc_833_, 6, v_recordedDeps_802_);
lean_ctor_set(v_reuseFailAlloc_833_, 7, v_messages_803_);
lean_ctor_set(v_reuseFailAlloc_833_, 8, v_infoState_804_);
lean_ctor_set(v_reuseFailAlloc_833_, 9, v_snapshotTasks_805_);
v___x_814_ = v_reuseFailAlloc_833_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v_mctx_817_; lean_object* v_zetaDeltaFVarIds_818_; lean_object* v_postponed_819_; lean_object* v_diag_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_831_; 
v___x_815_ = lean_st_ref_put(v___y_795_, v___x_814_);
v___x_816_ = lean_st_ref_take(v___y_794_);
v_mctx_817_ = lean_ctor_get(v___x_816_, 0);
v_zetaDeltaFVarIds_818_ = lean_ctor_get(v___x_816_, 2);
v_postponed_819_ = lean_ctor_get(v___x_816_, 3);
v_diag_820_ = lean_ctor_get(v___x_816_, 4);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_831_ == 0)
{
lean_object* v_unused_832_; 
v_unused_832_ = lean_ctor_get(v___x_816_, 1);
lean_dec(v_unused_832_);
v___x_822_ = v___x_816_;
v_isShared_823_ = v_isSharedCheck_831_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_diag_820_);
lean_inc(v_postponed_819_);
lean_inc(v_zetaDeltaFVarIds_818_);
lean_inc(v_mctx_817_);
lean_dec(v___x_816_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_831_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_827_; 
v___x_824_ = lean_box(0);
v___x_825_ = lean_obj_once(&l_Lean_Meta_registerCoercion___closed__2, &l_Lean_Meta_registerCoercion___closed__2_once, _init_l_Lean_Meta_registerCoercion___closed__2);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 1, v___x_825_);
v___x_827_ = v___x_822_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_mctx_817_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v___x_825_);
lean_ctor_set(v_reuseFailAlloc_830_, 2, v_zetaDeltaFVarIds_818_);
lean_ctor_set(v_reuseFailAlloc_830_, 3, v_postponed_819_);
lean_ctor_set(v_reuseFailAlloc_830_, 4, v_diag_820_);
v___x_827_ = v_reuseFailAlloc_830_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = lean_st_ref_put(v___y_794_, v___x_827_);
v___x_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_824_);
return v___x_829_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerCoercion___boxed(lean_object* v_name_885_, lean_object* v_info_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Lean_Meta_registerCoercion(v_name_885_, v_info_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
lean_dec(v_a_890_);
lean_dec_ref(v_a_889_);
lean_dec(v_a_888_);
lean_dec_ref(v_a_887_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2(lean_object* v_00_u03b1_893_, lean_object* v_msg_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2___redArg(v_msg_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2___boxed(lean_object* v_00_u03b1_901_, lean_object* v_msg_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2(v_00_u03b1_901_, v_msg_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_909_, lean_object* v_constName_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1___redArg(v_constName_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_917_, lean_object* v_constName_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1(v_00_u03b1_917_, v_constName_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b1_925_, lean_object* v_ref_926_, lean_object* v_constName_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg(v_ref_926_, v_constName_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b1_934_, lean_object* v_ref_935_, lean_object* v_constName_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5(v_00_u03b1_934_, v_ref_935_, v_constName_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v_ref_935_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7(lean_object* v_00_u03b1_943_, lean_object* v_ref_944_, lean_object* v_msg_945_, lean_object* v_declHint_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7___redArg(v_ref_944_, v_msg_945_, v_declHint_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7___boxed(lean_object* v_00_u03b1_953_, lean_object* v_ref_954_, lean_object* v_msg_955_, lean_object* v_declHint_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7(v_00_u03b1_953_, v_ref_954_, v_msg_955_, v_declHint_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v_ref_954_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9(lean_object* v_msg_963_, lean_object* v_declHint_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_963_, v_declHint_964_, v___y_968_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_971_, lean_object* v_declHint_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9(v_msg_971_, v_declHint_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_979_, lean_object* v_ref_980_, lean_object* v_msg_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___redArg(v_ref_980_, v_msg_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_988_, lean_object* v_ref_989_, lean_object* v_msg_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9(v_00_u03b1_988_, v_ref_989_, v_msg_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v_ref_989_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(lean_object* v_decl_997_, lean_object* v_____r_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = lean_box(0);
v___x_1005_ = l_Lean_Meta_registerCoercion(v_decl_997_, v___x_1004_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2____boxed(lean_object* v_decl_1006_, lean_object* v_____r_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(v_decl_1006_, v_____r_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
return v_res_1013_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__0));
v___x_1016_ = l_Lean_stringToMessageData(v___x_1015_);
return v___x_1016_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__2));
v___x_1019_ = l_Lean_stringToMessageData(v___x_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg(lean_object* v_name_1023_, uint8_t v_kind_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___y_1036_; 
v___x_1030_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__1);
v___x_1031_ = l_Lean_MessageData_ofName(v_name_1023_);
v___x_1032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1030_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__3);
v___x_1034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1032_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
switch(v_kind_1024_)
{
case 0:
{
lean_object* v___x_1043_; 
v___x_1043_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__4));
v___y_1036_ = v___x_1043_;
goto v___jp_1035_;
}
case 1:
{
lean_object* v___x_1044_; 
v___x_1044_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__5));
v___y_1036_ = v___x_1044_;
goto v___jp_1035_;
}
default: 
{
lean_object* v___x_1045_; 
v___x_1045_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__6));
v___y_1036_ = v___x_1045_;
goto v___jp_1035_;
}
}
v___jp_1035_:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
lean_inc_ref(v___y_1036_);
v___x_1037_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1037_, 0, v___y_1036_);
v___x_1038_ = l_Lean_MessageData_ofFormat(v___x_1037_);
v___x_1039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1034_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3);
v___x_1041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1039_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
v___x_1042_ = l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2___redArg(v___x_1041_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
return v___x_1042_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_name_1046_, lean_object* v_kind_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
uint8_t v_kind_boxed_1053_; lean_object* v_res_1054_; 
v_kind_boxed_1053_ = lean_unbox(v_kind_1047_);
v_res_1054_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg(v_name_1046_, v_kind_boxed_1053_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
return v_res_1054_;
}
}
static uint64_t _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1061_; uint64_t v___x_1062_; 
v___x_1061_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_));
v___x_1062_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1061_);
return v___x_1062_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1063_ = lean_uint64_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1064_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_));
v___x_1065_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set_uint64(v___x_1065_, sizeof(void*)*1, v___x_1063_);
return v___x_1065_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
return v___x_1067_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1069_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
lean_ctor_set(v___x_1069_, 2, v___x_1068_);
lean_ctor_set(v___x_1069_, 3, v___x_1068_);
lean_ctor_set(v___x_1069_, 4, v___x_1068_);
lean_ctor_set(v___x_1069_, 5, v___x_1068_);
return v___x_1069_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1071_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
lean_ctor_set(v___x_1071_, 2, v___x_1070_);
lean_ctor_set(v___x_1071_, 3, v___x_1070_);
lean_ctor_set(v___x_1071_, 4, v___x_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(lean_object* v___x_1072_, lean_object* v___x_1073_, lean_object* v___x_1074_, lean_object* v_decl_1075_, lean_object* v___stx_1076_, uint8_t v_kind_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
uint8_t v___x_1081_; uint8_t v___x_1082_; uint8_t v___x_1083_; uint8_t v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; size_t v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___y_1104_; 
v___x_1081_ = 0;
v___x_1082_ = l_Lean_instBEqAttributeKind_beq(v_kind_1077_, v___x_1081_);
v___x_1083_ = 1;
v___x_1084_ = 0;
v___x_1085_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1086_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1087_ = lean_unsigned_to_nat(32u);
v___x_1088_ = lean_mk_empty_array_with_capacity(v___x_1087_);
v___x_1089_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_1090_ = ((size_t)5ULL);
lean_inc_n(v___x_1072_, 6);
v___x_1091_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1091_, 0, v___x_1089_);
lean_ctor_set(v___x_1091_, 1, v___x_1088_);
lean_ctor_set(v___x_1091_, 2, v___x_1072_);
lean_ctor_set(v___x_1091_, 3, v___x_1072_);
lean_ctor_set_usize(v___x_1091_, 4, v___x_1090_);
v___x_1092_ = lean_box(1);
lean_inc_ref(v___x_1091_);
v___x_1093_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1086_);
lean_ctor_set(v___x_1093_, 1, v___x_1091_);
lean_ctor_set(v___x_1093_, 2, v___x_1092_);
v___x_1094_ = lean_mk_empty_array_with_capacity(v___x_1072_);
v___x_1095_ = lean_box(0);
lean_inc(v___x_1073_);
v___x_1096_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1096_, 0, v___x_1085_);
lean_ctor_set(v___x_1096_, 1, v___x_1073_);
lean_ctor_set(v___x_1096_, 2, v___x_1093_);
lean_ctor_set(v___x_1096_, 3, v___x_1094_);
lean_ctor_set(v___x_1096_, 4, v___x_1095_);
lean_ctor_set(v___x_1096_, 5, v___x_1072_);
lean_ctor_set(v___x_1096_, 6, v___x_1095_);
lean_ctor_set_uint8(v___x_1096_, sizeof(void*)*7, v___x_1084_);
lean_ctor_set_uint8(v___x_1096_, sizeof(void*)*7 + 1, v___x_1084_);
lean_ctor_set_uint8(v___x_1096_, sizeof(void*)*7 + 2, v___x_1084_);
lean_ctor_set_uint8(v___x_1096_, sizeof(void*)*7 + 3, v___x_1083_);
v___x_1097_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1098_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1072_);
lean_ctor_set(v___x_1098_, 1, v___x_1072_);
lean_ctor_set(v___x_1098_, 2, v___x_1072_);
lean_ctor_set(v___x_1098_, 3, v___x_1072_);
lean_ctor_set(v___x_1098_, 4, v___x_1086_);
lean_ctor_set(v___x_1098_, 5, v___x_1086_);
lean_ctor_set(v___x_1098_, 6, v___x_1086_);
lean_ctor_set(v___x_1098_, 7, v___x_1086_);
lean_ctor_set(v___x_1098_, 8, v___x_1086_);
lean_ctor_set(v___x_1098_, 9, v___x_1086_);
lean_ctor_set(v___x_1098_, 10, v___x_1086_);
lean_ctor_set(v___x_1098_, 11, v___x_1097_);
v___x_1099_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1100_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1101_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1098_);
lean_ctor_set(v___x_1101_, 1, v___x_1099_);
lean_ctor_set(v___x_1101_, 2, v___x_1073_);
lean_ctor_set(v___x_1101_, 3, v___x_1091_);
lean_ctor_set(v___x_1101_, 4, v___x_1100_);
v___x_1102_ = lean_st_mk_ref(v___x_1101_);
if (v___x_1082_ == 0)
{
lean_object* v___x_1114_; 
lean_dec(v_decl_1075_);
v___x_1114_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg(v___x_1074_, v_kind_1077_, v___x_1096_, v___x_1102_, v___y_1078_, v___y_1079_);
lean_dec_ref_known(v___x_1096_, 7);
v___y_1104_ = v___x_1114_;
goto v___jp_1103_;
}
else
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
lean_dec(v___x_1074_);
v___x_1115_ = lean_box(0);
v___x_1116_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(v_decl_1075_, v___x_1115_, v___x_1096_, v___x_1102_, v___y_1078_, v___y_1079_);
lean_dec_ref_known(v___x_1096_, 7);
v___y_1104_ = v___x_1116_;
goto v___jp_1103_;
}
v___jp_1103_:
{
if (lean_obj_tag(v___y_1104_) == 0)
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1113_; 
v_a_1105_ = lean_ctor_get(v___y_1104_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___y_1104_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1107_ = v___y_1104_;
v_isShared_1108_ = v_isSharedCheck_1113_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___y_1104_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1113_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1109_; lean_object* v___x_1111_; 
v___x_1109_ = lean_st_ref_get(v___x_1102_);
lean_dec(v___x_1102_);
lean_dec(v___x_1109_);
if (v_isShared_1108_ == 0)
{
v___x_1111_ = v___x_1107_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1105_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
else
{
lean_dec(v___x_1102_);
return v___y_1104_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2____boxed(lean_object* v___x_1117_, lean_object* v___x_1118_, lean_object* v___x_1119_, lean_object* v_decl_1120_, lean_object* v___stx_1121_, lean_object* v_kind_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
uint8_t v_kind_boxed_1126_; lean_object* v_res_1127_; 
v_kind_boxed_1126_ = lean_unbox(v_kind_1122_);
v_res_1127_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(v___x_1117_, v___x_1118_, v___x_1119_, v_decl_1120_, v___stx_1121_, v_kind_boxed_1126_, v___y_1123_, v___y_1124_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___stx_1121_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v___x_1132_; lean_object* v_toCold_1133_; lean_object* v_env_1134_; lean_object* v_options_1135_; uint8_t v___x_1136_; lean_object* v_env_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1132_ = lean_st_ref_get(v___y_1130_);
v_toCold_1133_ = lean_ctor_get(v___y_1129_, 0);
v_env_1134_ = lean_ctor_get(v___x_1132_, 0);
lean_inc_ref(v_env_1134_);
lean_dec(v___x_1132_);
v_options_1135_ = lean_ctor_get(v_toCold_1133_, 2);
v___x_1136_ = 0;
v_env_1137_ = l_Lean_Environment_setRecordingDeps(v_env_1134_, v___x_1136_);
v___x_1138_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_1139_ = lean_unsigned_to_nat(32u);
v___x_1140_ = lean_mk_empty_array_with_capacity(v___x_1139_);
lean_dec_ref(v___x_1140_);
v___x_1141_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
lean_inc_ref(v_options_1135_);
v___x_1142_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1142_, 0, v_env_1137_);
lean_ctor_set(v___x_1142_, 1, v___x_1138_);
lean_ctor_set(v___x_1142_, 2, v___x_1141_);
lean_ctor_set(v___x_1142_, 3, v_options_1135_);
v___x_1143_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
lean_ctor_set(v___x_1143_, 1, v_msgData_1128_);
v___x_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0_spec__0(v_msgData_1145_, v___y_1146_, v___y_1147_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_ref_1154_; lean_object* v___x_1155_; lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1164_; 
v_ref_1154_ = lean_ctor_get(v___y_1151_, 2);
v___x_1155_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0_spec__0(v_msg_1150_, v___y_1151_, v___y_1152_);
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1158_ = v___x_1155_;
v_isShared_1159_ = v_isSharedCheck_1164_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1155_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1164_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1160_; lean_object* v___x_1162_; 
lean_inc(v_ref_1154_);
v___x_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1160_, 0, v_ref_1154_);
lean_ctor_set(v___x_1160_, 1, v_a_1156_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set_tag(v___x_1158_, 1);
lean_ctor_set(v___x_1158_, 0, v___x_1160_);
v___x_1162_ = v___x_1158_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1160_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0___redArg(v_msg_1165_, v___y_1166_, v___y_1167_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
return v_res_1169_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_));
v___x_1172_ = l_Lean_stringToMessageData(v___x_1171_);
return v___x_1172_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_));
v___x_1175_ = l_Lean_stringToMessageData(v___x_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(lean_object* v___x_1176_, lean_object* v_decl_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1181_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1182_ = l_Lean_MessageData_ofName(v___x_1176_);
v___x_1183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1181_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___x_1184_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1183_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
v___x_1186_ = l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0___redArg(v___x_1185_, v___y_1178_, v___y_1179_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2____boxed(lean_object* v___x_1187_, lean_object* v_decl_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(v___x_1187_, v_decl_1188_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v_decl_1188_);
return v_res_1192_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1233_ = lean_unsigned_to_nat(3842861879u);
v___x_1234_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_));
v___x_1235_ = l_Lean_Name_num___override(v___x_1234_, v___x_1233_);
return v___x_1235_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1237_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_));
v___x_1238_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1239_ = l_Lean_Name_str___override(v___x_1238_, v___x_1237_);
return v___x_1239_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1241_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_));
v___x_1242_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1243_ = l_Lean_Name_str___override(v___x_1242_, v___x_1241_);
return v___x_1243_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1244_ = lean_unsigned_to_nat(2u);
v___x_1245_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1246_ = l_Lean_Name_num___override(v___x_1245_, v___x_1244_);
return v___x_1246_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1256_ = 0;
v___x_1257_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_));
v___x_1258_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_));
v___x_1259_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1260_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
lean_ctor_set(v___x_1260_, 1, v___x_1258_);
lean_ctor_set(v___x_1260_, 2, v___x_1257_);
lean_ctor_set_uint8(v___x_1260_, sizeof(void*)*3, v___x_1256_);
return v___x_1260_;
}
}
static lean_object* _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1261_; lean_object* v___f_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___f_1261_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_));
v___f_1262_ = ((lean_object*)(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_));
v___x_1263_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1264_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
lean_ctor_set(v___x_1264_, 1, v___f_1262_);
lean_ctor_set(v___x_1264_, 2, v___f_1261_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = lean_obj_once(&l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_, &l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
v___x_1267_ = l_Lean_registerBuiltinAttribute(v___x_1266_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2____boxed(lean_object* v_a_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_();
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1270_, lean_object* v_msg_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0___redArg(v_msg_1271_, v___y_1272_, v___y_1273_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1276_, lean_object* v_msg_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0(v_00_u03b1_1276_, v_msg_1277_, v___y_1278_, v___y_1279_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b1_1282_, lean_object* v_name_1283_, uint8_t v_kind_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg(v_name_1283_, v_kind_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b1_1291_, lean_object* v_name_1292_, lean_object* v_kind_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
uint8_t v_kind_boxed_1299_; lean_object* v_res_1300_; 
v_kind_boxed_1299_ = lean_unbox(v_kind_1293_);
v_res_1300_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1(v_00_u03b1_1291_, v_name_1292_, v_kind_boxed_1299_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
return v_res_1300_;
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

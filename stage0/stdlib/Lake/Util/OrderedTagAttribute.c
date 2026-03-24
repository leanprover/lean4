// Lean compiler output
// Module: Lake.Util.OrderedTagAttribute
// Imports: public import Lean.Attributes
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instInhabitedEnvExtension_default(lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedAttributeImpl_default;
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___redArg(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
static const lean_string_object l_Lake_instInhabitedOrderedTagAttribute_default___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "(`Inhabited.default` for `IO.Error`)"};
static const lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___lam__0___closed__0 = (const lean_object*)&l_Lake_instInhabitedOrderedTagAttribute_default___lam__0___closed__0_value;
static const lean_ctor_object l_Lake_instInhabitedOrderedTagAttribute_default___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Lake_instInhabitedOrderedTagAttribute_default___lam__0___closed__0_value)}};
static const lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___lam__0___closed__1 = (const lean_object*)&l_Lake_instInhabitedOrderedTagAttribute_default___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___lam__1___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___closed__0 = (const lean_object*)&l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___lam__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_instInhabitedOrderedTagAttribute_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instInhabitedOrderedTagAttribute_default___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedOrderedTagAttribute_default___closed__0_value;
static const lean_closure_object l_Lake_instInhabitedOrderedTagAttribute_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instInhabitedOrderedTagAttribute_default___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___closed__1 = (const lean_object*)&l_Lake_instInhabitedOrderedTagAttribute_default___closed__1_value;
static const lean_closure_object l_Lake_instInhabitedOrderedTagAttribute_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___closed__2 = (const lean_object*)&l_Lake_instInhabitedOrderedTagAttribute_default___closed__2_value;
static const lean_closure_object l_Lake_instInhabitedOrderedTagAttribute_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instInhabitedOrderedTagAttribute_default___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___closed__3 = (const lean_object*)&l_Lake_instInhabitedOrderedTagAttribute_default___closed__3_value;
static lean_once_cell_t l_Lake_instInhabitedOrderedTagAttribute_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___closed__4;
static lean_once_cell_t l_Lake_instInhabitedOrderedTagAttribute_default___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___closed__5;
static lean_once_cell_t l_Lake_instInhabitedOrderedTagAttribute_default___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___closed__6;
LEAN_EXPORT lean_object* l_Lake_instInhabitedOrderedTagAttribute_default;
LEAN_EXPORT lean_object* l_Lake_instInhabitedOrderedTagAttribute;
static const lean_string_object l_Lake_registerOrderedTagAttribute___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lake_registerOrderedTagAttribute___auto__1___closed__0 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__0_value;
static const lean_string_object l_Lake_registerOrderedTagAttribute___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lake_registerOrderedTagAttribute___auto__1___closed__1 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__1_value;
static const lean_string_object l_Lake_registerOrderedTagAttribute___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lake_registerOrderedTagAttribute___auto__1___closed__2 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__2_value;
static const lean_string_object l_Lake_registerOrderedTagAttribute___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lake_registerOrderedTagAttribute___auto__1___closed__3 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__3_value;
static const lean_ctor_object l_Lake_registerOrderedTagAttribute___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_registerOrderedTagAttribute___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__4_value_aux_0),((lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_registerOrderedTagAttribute___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__4_value_aux_1),((lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lake_registerOrderedTagAttribute___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__4_value_aux_2),((lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lake_registerOrderedTagAttribute___auto__1___closed__4 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__4_value;
static const lean_array_object l_Lake_registerOrderedTagAttribute___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_registerOrderedTagAttribute___auto__1___closed__5 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__5_value;
static const lean_string_object l_Lake_registerOrderedTagAttribute___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lake_registerOrderedTagAttribute___auto__1___closed__6 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__6_value;
static const lean_ctor_object l_Lake_registerOrderedTagAttribute___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_registerOrderedTagAttribute___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__7_value_aux_0),((lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_registerOrderedTagAttribute___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__7_value_aux_1),((lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lake_registerOrderedTagAttribute___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__7_value_aux_2),((lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lake_registerOrderedTagAttribute___auto__1___closed__7 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__7_value;
static const lean_string_object l_Lake_registerOrderedTagAttribute___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lake_registerOrderedTagAttribute___auto__1___closed__8 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__8_value;
static const lean_ctor_object l_Lake_registerOrderedTagAttribute___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lake_registerOrderedTagAttribute___auto__1___closed__9 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__9_value;
static const lean_string_object l_Lake_registerOrderedTagAttribute___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lake_registerOrderedTagAttribute___auto__1___closed__10 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__10_value;
static const lean_ctor_object l_Lake_registerOrderedTagAttribute___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_registerOrderedTagAttribute___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__11_value_aux_0),((lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_registerOrderedTagAttribute___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__11_value_aux_1),((lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lake_registerOrderedTagAttribute___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__11_value_aux_2),((lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lake_registerOrderedTagAttribute___auto__1___closed__11 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__11_value;
static lean_once_cell_t l_Lake_registerOrderedTagAttribute___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_registerOrderedTagAttribute___auto__1___closed__12;
static lean_once_cell_t l_Lake_registerOrderedTagAttribute___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_registerOrderedTagAttribute___auto__1___closed__13;
static const lean_string_object l_Lake_registerOrderedTagAttribute___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lake_registerOrderedTagAttribute___auto__1___closed__14 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__14_value;
static const lean_string_object l_Lake_registerOrderedTagAttribute___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "declName"};
static const lean_object* l_Lake_registerOrderedTagAttribute___auto__1___closed__15 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__15_value;
static const lean_ctor_object l_Lake_registerOrderedTagAttribute___auto__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_registerOrderedTagAttribute___auto__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__16_value_aux_0),((lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_registerOrderedTagAttribute___auto__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__16_value_aux_1),((lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_registerOrderedTagAttribute___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__16_value_aux_2),((lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(113, 211, 58, 33, 138, 196, 138, 106)}};
static const lean_object* l_Lake_registerOrderedTagAttribute___auto__1___closed__16 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__16_value;
static const lean_string_object l_Lake_registerOrderedTagAttribute___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decl_name%"};
static const lean_object* l_Lake_registerOrderedTagAttribute___auto__1___closed__17 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___auto__1___closed__17_value;
static lean_once_cell_t l_Lake_registerOrderedTagAttribute___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_registerOrderedTagAttribute___auto__1___closed__18;
static lean_once_cell_t l_Lake_registerOrderedTagAttribute___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_registerOrderedTagAttribute___auto__1___closed__19;
static lean_once_cell_t l_Lake_registerOrderedTagAttribute___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_registerOrderedTagAttribute___auto__1___closed__20;
static lean_once_cell_t l_Lake_registerOrderedTagAttribute___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_registerOrderedTagAttribute___auto__1___closed__21;
static lean_once_cell_t l_Lake_registerOrderedTagAttribute___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_registerOrderedTagAttribute___auto__1___closed__22;
static lean_once_cell_t l_Lake_registerOrderedTagAttribute___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_registerOrderedTagAttribute___auto__1___closed__23;
static lean_once_cell_t l_Lake_registerOrderedTagAttribute___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_registerOrderedTagAttribute___auto__1___closed__24;
static lean_once_cell_t l_Lake_registerOrderedTagAttribute___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_registerOrderedTagAttribute___auto__1___closed__25;
static lean_once_cell_t l_Lake_registerOrderedTagAttribute___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_registerOrderedTagAttribute___auto__1___closed__26;
static lean_once_cell_t l_Lake_registerOrderedTagAttribute___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_registerOrderedTagAttribute___auto__1___closed__27;
static lean_once_cell_t l_Lake_registerOrderedTagAttribute___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_registerOrderedTagAttribute___auto__1___closed__28;
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___auto__1;
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__0___boxed(lean_object*);
static const lean_string_object l_Lake_registerOrderedTagAttribute___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "tag attribute"};
static const lean_object* l_Lake_registerOrderedTagAttribute___lam__1___closed__0 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___lam__1___closed__0_value;
static const lean_ctor_object l_Lake_registerOrderedTagAttribute___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_registerOrderedTagAttribute___lam__1___closed__0_value)}};
static const lean_object* l_Lake_registerOrderedTagAttribute___lam__1___closed__1 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___lam__1___closed__1_value;
static const lean_ctor_object l_Lake_registerOrderedTagAttribute___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_registerOrderedTagAttribute___lam__1___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_registerOrderedTagAttribute___lam__1___closed__2 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___lam__1___closed__2_value;
static const lean_string_object l_Lake_registerOrderedTagAttribute___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "number of local entries: "};
static const lean_object* l_Lake_registerOrderedTagAttribute___lam__1___closed__3 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___lam__1___closed__3_value;
static const lean_ctor_object l_Lake_registerOrderedTagAttribute___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_registerOrderedTagAttribute___lam__1___closed__3_value)}};
static const lean_object* l_Lake_registerOrderedTagAttribute___lam__1___closed__4 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___lam__1___closed__4_value;
static const lean_ctor_object l_Lake_registerOrderedTagAttribute___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_registerOrderedTagAttribute___lam__1___closed__2_value),((lean_object*)&l_Lake_registerOrderedTagAttribute___lam__1___closed__4_value)}};
static const lean_object* l_Lake_registerOrderedTagAttribute___lam__1___closed__5 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___lam__1___closed__5_value;
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__5(lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__5___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_registerOrderedTagAttribute___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l_Lake_registerOrderedTagAttribute___lam__6___closed__0 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___lam__6___closed__0_value;
static lean_once_cell_t l_Lake_registerOrderedTagAttribute___lam__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_registerOrderedTagAttribute___lam__6___closed__1;
static const lean_string_object l_Lake_registerOrderedTagAttribute___lam__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l_Lake_registerOrderedTagAttribute___lam__6___closed__2 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___lam__6___closed__2_value;
static lean_once_cell_t l_Lake_registerOrderedTagAttribute___lam__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_registerOrderedTagAttribute___lam__6___closed__3;
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Invalid attribute scope: Attribute `["};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "]` must be global, not `"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__5;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "global"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__6 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__6_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__7 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__7_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scoped"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__8 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Cannot add attribute `["};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` to declaration `"};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "` because it is in an imported module"};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_registerOrderedTagAttribute___lam__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_registerOrderedTagAttribute___lam__7___closed__0;
static lean_once_cell_t l_Lake_registerOrderedTagAttribute___lam__7___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_registerOrderedTagAttribute___lam__7___closed__1;
static lean_once_cell_t l_Lake_registerOrderedTagAttribute___lam__7___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_registerOrderedTagAttribute___lam__7___closed__2;
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_registerOrderedTagAttribute___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_registerOrderedTagAttribute___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_registerOrderedTagAttribute___closed__0 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___closed__0_value;
static const lean_closure_object l_Lake_registerOrderedTagAttribute___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_registerOrderedTagAttribute___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_registerOrderedTagAttribute___closed__1 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___closed__1_value;
static const lean_closure_object l_Lake_registerOrderedTagAttribute___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_registerOrderedTagAttribute___lam__2___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_registerOrderedTagAttribute___closed__2 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___closed__2_value;
static const lean_closure_object l_Lake_registerOrderedTagAttribute___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_registerOrderedTagAttribute___lam__3, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_registerOrderedTagAttribute___closed__3 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___closed__3_value;
static const lean_array_object l_Lake_registerOrderedTagAttribute___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_registerOrderedTagAttribute___closed__4 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___closed__4_value;
static const lean_closure_object l_Lake_registerOrderedTagAttribute___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_registerOrderedTagAttribute___lam__4___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lake_registerOrderedTagAttribute___closed__4_value)} };
static const lean_object* l_Lake_registerOrderedTagAttribute___closed__5 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___closed__5_value;
static const lean_closure_object l_Lake_registerOrderedTagAttribute___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_registerOrderedTagAttribute___lam__5___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lake_registerOrderedTagAttribute___closed__4_value)} };
static const lean_object* l_Lake_registerOrderedTagAttribute___closed__6 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___closed__6_value;
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_OrderedTagAttribute_hasTag___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_OrderedTagAttribute_hasTag___closed__0;
LEAN_EXPORT uint8_t l_Lake_OrderedTagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrderedTagAttribute_hasTag___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrderedTagAttribute_getAllEntries_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrderedTagAttribute_getAllEntries_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_OrderedTagAttribute_getAllEntries___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_OrderedTagAttribute_getAllEntries___closed__0;
LEAN_EXPORT lean_object* l_Lake_OrderedTagAttribute_getAllEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrderedTagAttribute_getAllEntries___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___lam__0(lean_object* v_x_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = ((lean_object*)(l_Lake_instInhabitedOrderedTagAttribute_default___lam__0___closed__1));
v___x_8_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___lam__0___boxed(lean_object* v_x_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lake_instInhabitedOrderedTagAttribute_default___lam__0(v_x_9_, v___y_10_);
lean_dec_ref(v___y_10_);
lean_dec_ref(v_x_9_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___lam__1(lean_object* v_s_13_, lean_object* v_x_14_){
_start:
{
lean_inc_ref(v_s_13_);
return v_s_13_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___lam__1___boxed(lean_object* v_s_15_, lean_object* v_x_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Lake_instInhabitedOrderedTagAttribute_default___lam__1(v_s_15_, v_x_16_);
lean_dec(v_x_16_);
lean_dec_ref(v_s_15_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___lam__2(lean_object* v_x_20_, lean_object* v_x_21_, uint8_t v_x_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = ((lean_object*)(l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___closed__0));
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___boxed(lean_object* v_x_24_, lean_object* v_x_25_, lean_object* v_x_26_){
_start:
{
uint8_t v_x_77__boxed_27_; lean_object* v_res_28_; 
v_x_77__boxed_27_ = lean_unbox(v_x_26_);
v_res_28_ = l_Lake_instInhabitedOrderedTagAttribute_default___lam__2(v_x_24_, v_x_25_, v_x_77__boxed_27_);
lean_dec_ref(v_x_25_);
lean_dec_ref(v_x_24_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___lam__3(lean_object* v_x_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lean_box(0);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___lam__3___boxed(lean_object* v_x_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lake_instInhabitedOrderedTagAttribute_default___lam__3(v_x_31_);
lean_dec_ref(v_x_31_);
return v_res_32_;
}
}
static lean_object* _init_l_Lake_instInhabitedOrderedTagAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_37_;
}
}
static lean_object* _init_l_Lake_instInhabitedOrderedTagAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_38_; lean_object* v___f_39_; lean_object* v___f_40_; lean_object* v___f_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___f_38_ = ((lean_object*)(l_Lake_instInhabitedOrderedTagAttribute_default___closed__3));
v___f_39_ = ((lean_object*)(l_Lake_instInhabitedOrderedTagAttribute_default___closed__2));
v___f_40_ = ((lean_object*)(l_Lake_instInhabitedOrderedTagAttribute_default___closed__1));
v___f_41_ = ((lean_object*)(l_Lake_instInhabitedOrderedTagAttribute_default___closed__0));
v___x_42_ = lean_box(0);
v___x_43_ = lean_obj_once(&l_Lake_instInhabitedOrderedTagAttribute_default___closed__4, &l_Lake_instInhabitedOrderedTagAttribute_default___closed__4_once, _init_l_Lake_instInhabitedOrderedTagAttribute_default___closed__4);
v___x_44_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
lean_ctor_set(v___x_44_, 1, v___x_42_);
lean_ctor_set(v___x_44_, 2, v___f_41_);
lean_ctor_set(v___x_44_, 3, v___f_40_);
lean_ctor_set(v___x_44_, 4, v___f_39_);
lean_ctor_set(v___x_44_, 5, v___f_38_);
return v___x_44_;
}
}
static lean_object* _init_l_Lake_instInhabitedOrderedTagAttribute_default___closed__6(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_45_ = lean_obj_once(&l_Lake_instInhabitedOrderedTagAttribute_default___closed__5, &l_Lake_instInhabitedOrderedTagAttribute_default___closed__5_once, _init_l_Lake_instInhabitedOrderedTagAttribute_default___closed__5);
v___x_46_ = l_Lean_instInhabitedAttributeImpl_default;
v___x_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
lean_ctor_set(v___x_47_, 1, v___x_45_);
return v___x_47_;
}
}
static lean_object* _init_l_Lake_instInhabitedOrderedTagAttribute_default(void){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lean_obj_once(&l_Lake_instInhabitedOrderedTagAttribute_default___closed__6, &l_Lake_instInhabitedOrderedTagAttribute_default___closed__6_once, _init_l_Lake_instInhabitedOrderedTagAttribute_default___closed__6);
return v___x_48_;
}
}
static lean_object* _init_l_Lake_instInhabitedOrderedTagAttribute(void){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lake_instInhabitedOrderedTagAttribute_default;
return v___x_49_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__12(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___auto__1___closed__10));
v___x_77_ = l_Lean_mkAtom(v___x_76_);
return v___x_77_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__13(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_78_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___auto__1___closed__12, &l_Lake_registerOrderedTagAttribute___auto__1___closed__12_once, _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__12);
v___x_79_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___auto__1___closed__5));
v___x_80_ = lean_array_push(v___x_79_, v___x_78_);
return v___x_80_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__18(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___auto__1___closed__17));
v___x_90_ = l_Lean_mkAtom(v___x_89_);
return v___x_90_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__19(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_91_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___auto__1___closed__18, &l_Lake_registerOrderedTagAttribute___auto__1___closed__18_once, _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__18);
v___x_92_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___auto__1___closed__5));
v___x_93_ = lean_array_push(v___x_92_, v___x_91_);
return v___x_93_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__20(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_94_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___auto__1___closed__19, &l_Lake_registerOrderedTagAttribute___auto__1___closed__19_once, _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__19);
v___x_95_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___auto__1___closed__16));
v___x_96_ = lean_box(2);
v___x_97_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v___x_95_);
lean_ctor_set(v___x_97_, 2, v___x_94_);
return v___x_97_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__21(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_98_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___auto__1___closed__20, &l_Lake_registerOrderedTagAttribute___auto__1___closed__20_once, _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__20);
v___x_99_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___auto__1___closed__13, &l_Lake_registerOrderedTagAttribute___auto__1___closed__13_once, _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__13);
v___x_100_ = lean_array_push(v___x_99_, v___x_98_);
return v___x_100_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__22(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_101_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___auto__1___closed__21, &l_Lake_registerOrderedTagAttribute___auto__1___closed__21_once, _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__21);
v___x_102_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___auto__1___closed__11));
v___x_103_ = lean_box(2);
v___x_104_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
lean_ctor_set(v___x_104_, 1, v___x_102_);
lean_ctor_set(v___x_104_, 2, v___x_101_);
return v___x_104_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__23(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_105_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___auto__1___closed__22, &l_Lake_registerOrderedTagAttribute___auto__1___closed__22_once, _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__22);
v___x_106_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___auto__1___closed__5));
v___x_107_ = lean_array_push(v___x_106_, v___x_105_);
return v___x_107_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__24(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_108_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___auto__1___closed__23, &l_Lake_registerOrderedTagAttribute___auto__1___closed__23_once, _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__23);
v___x_109_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___auto__1___closed__9));
v___x_110_ = lean_box(2);
v___x_111_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
lean_ctor_set(v___x_111_, 1, v___x_109_);
lean_ctor_set(v___x_111_, 2, v___x_108_);
return v___x_111_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__25(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_112_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___auto__1___closed__24, &l_Lake_registerOrderedTagAttribute___auto__1___closed__24_once, _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__24);
v___x_113_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___auto__1___closed__5));
v___x_114_ = lean_array_push(v___x_113_, v___x_112_);
return v___x_114_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__26(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_115_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___auto__1___closed__25, &l_Lake_registerOrderedTagAttribute___auto__1___closed__25_once, _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__25);
v___x_116_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___auto__1___closed__7));
v___x_117_ = lean_box(2);
v___x_118_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
lean_ctor_set(v___x_118_, 1, v___x_116_);
lean_ctor_set(v___x_118_, 2, v___x_115_);
return v___x_118_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__27(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_119_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___auto__1___closed__26, &l_Lake_registerOrderedTagAttribute___auto__1___closed__26_once, _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__26);
v___x_120_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___auto__1___closed__5));
v___x_121_ = lean_array_push(v___x_120_, v___x_119_);
return v___x_121_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__28(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_122_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___auto__1___closed__27, &l_Lake_registerOrderedTagAttribute___auto__1___closed__27_once, _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__27);
v___x_123_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___auto__1___closed__4));
v___x_124_ = lean_box(2);
v___x_125_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
lean_ctor_set(v___x_125_, 1, v___x_123_);
lean_ctor_set(v___x_125_, 2, v___x_122_);
return v___x_125_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___auto__1(void){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___auto__1___closed__28, &l_Lake_registerOrderedTagAttribute___auto__1___closed__28_once, _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__28);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__0(lean_object* v_es_127_){
_start:
{
lean_inc_ref(v_es_127_);
return v_es_127_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__0___boxed(lean_object* v_es_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lake_registerOrderedTagAttribute___lam__0(v_es_128_);
lean_dec_ref(v_es_128_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__1(lean_object* v_s_142_){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_143_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___lam__1___closed__5));
v___x_144_ = lean_array_get_size(v_s_142_);
v___x_145_ = l_Nat_reprFast(v___x_144_);
v___x_146_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
v___x_147_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_143_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__1___boxed(lean_object* v_s_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lake_registerOrderedTagAttribute___lam__1(v_s_148_);
lean_dec_ref(v_s_148_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__2(lean_object* v_x_150_, lean_object* v_s_151_, uint8_t v_x_152_){
_start:
{
lean_inc_ref(v_s_151_);
return v_s_151_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__2___boxed(lean_object* v_x_153_, lean_object* v_s_154_, lean_object* v_x_155_){
_start:
{
uint8_t v_x_2211__boxed_156_; lean_object* v_res_157_; 
v_x_2211__boxed_156_ = lean_unbox(v_x_155_);
v_res_157_ = l_Lake_registerOrderedTagAttribute___lam__2(v_x_153_, v_s_154_, v_x_2211__boxed_156_);
lean_dec_ref(v_s_154_);
lean_dec_ref(v_x_153_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__3(lean_object* v_s_158_, lean_object* v_n_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = lean_array_push(v_s_158_, v_n_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__4(lean_object* v___x_161_, lean_object* v_x_162_, lean_object* v_x_163_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_161_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__4___boxed(lean_object* v___x_166_, lean_object* v_x_167_, lean_object* v_x_168_, lean_object* v___y_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lake_registerOrderedTagAttribute___lam__4(v___x_166_, v_x_167_, v_x_168_);
lean_dec_ref(v_x_168_);
lean_dec_ref(v_x_167_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__5(lean_object* v___x_171_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_173_, 0, v___x_171_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__5___boxed(lean_object* v___x_174_, lean_object* v___y_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lake_registerOrderedTagAttribute___lam__5(v___x_174_);
return v_res_176_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_177_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__0);
v___x_179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
return v___x_179_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1);
v___x_181_ = lean_unsigned_to_nat(0u);
v___x_182_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
lean_ctor_set(v___x_182_, 2, v___x_181_);
lean_ctor_set(v___x_182_, 3, v___x_180_);
lean_ctor_set(v___x_182_, 4, v___x_180_);
lean_ctor_set(v___x_182_, 5, v___x_180_);
lean_ctor_set(v___x_182_, 6, v___x_180_);
lean_ctor_set(v___x_182_, 7, v___x_180_);
lean_ctor_set(v___x_182_, 8, v___x_180_);
return v___x_182_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_183_ = lean_unsigned_to_nat(32u);
v___x_184_ = lean_mk_empty_array_with_capacity(v___x_183_);
v___x_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
return v___x_185_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_186_ = ((size_t)5ULL);
v___x_187_ = lean_unsigned_to_nat(0u);
v___x_188_ = lean_unsigned_to_nat(32u);
v___x_189_ = lean_mk_empty_array_with_capacity(v___x_188_);
v___x_190_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__3);
v___x_191_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v___x_189_);
lean_ctor_set(v___x_191_, 2, v___x_187_);
lean_ctor_set(v___x_191_, 3, v___x_187_);
lean_ctor_set_usize(v___x_191_, 4, v___x_186_);
return v___x_191_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_192_ = lean_box(1);
v___x_193_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__4);
v___x_194_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1);
v___x_195_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v___x_193_);
lean_ctor_set(v___x_195_, 2, v___x_192_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0(lean_object* v_msgData_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
lean_object* v___x_200_; lean_object* v_env_201_; lean_object* v_options_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_200_ = lean_st_ref_get(v___y_198_);
v_env_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc_ref(v_env_201_);
lean_dec(v___x_200_);
v_options_202_ = lean_ctor_get(v___y_197_, 2);
v___x_203_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__2);
v___x_204_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_202_);
v___x_205_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_205_, 0, v_env_201_);
lean_ctor_set(v___x_205_, 1, v___x_203_);
lean_ctor_set(v___x_205_, 2, v___x_204_);
lean_ctor_set(v___x_205_, 3, v_options_202_);
v___x_206_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v_msgData_196_);
v___x_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___boxed(lean_object* v_msgData_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0(v_msgData_208_, v___y_209_, v___y_210_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg(lean_object* v_msg_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v_ref_217_; lean_object* v___x_218_; lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_227_; 
v_ref_217_ = lean_ctor_get(v___y_214_, 5);
v___x_218_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0(v_msg_213_, v___y_214_, v___y_215_);
v_a_219_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_227_ == 0)
{
v___x_221_ = v___x_218_;
v_isShared_222_ = v_isSharedCheck_227_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_dec(v___x_218_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_227_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_223_; lean_object* v___x_225_; 
lean_inc(v_ref_217_);
v___x_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_223_, 0, v_ref_217_);
lean_ctor_set(v___x_223_, 1, v_a_219_);
if (v_isShared_222_ == 0)
{
lean_ctor_set_tag(v___x_221_, 1);
lean_ctor_set(v___x_221_, 0, v___x_223_);
v___x_225_ = v___x_221_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_223_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg___boxed(lean_object* v_msg_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg(v_msg_228_, v___y_229_, v___y_230_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
return v_res_232_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___lam__6___closed__1(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___lam__6___closed__0));
v___x_235_ = l_Lean_stringToMessageData(v___x_234_);
return v___x_235_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___lam__6___closed__3(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___lam__6___closed__2));
v___x_238_ = l_Lean_stringToMessageData(v___x_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__6(lean_object* v_name_239_, lean_object* v_decl_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_244_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___lam__6___closed__1, &l_Lake_registerOrderedTagAttribute___lam__6___closed__1_once, _init_l_Lake_registerOrderedTagAttribute___lam__6___closed__1);
v___x_245_ = l_Lean_MessageData_ofName(v_name_239_);
v___x_246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_244_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
v___x_247_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___lam__6___closed__3, &l_Lake_registerOrderedTagAttribute___lam__6___closed__3_once, _init_l_Lake_registerOrderedTagAttribute___lam__6___closed__3);
v___x_248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_246_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v___x_249_ = l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg(v___x_248_, v___y_241_, v___y_242_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__6___boxed(lean_object* v_name_250_, lean_object* v_decl_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lake_registerOrderedTagAttribute___lam__6(v_name_250_, v_decl_251_, v___y_252_, v___y_253_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v_decl_251_);
return v_res_255_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__0));
v___x_258_ = l_Lean_stringToMessageData(v___x_257_);
return v___x_258_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__2));
v___x_261_ = l_Lean_stringToMessageData(v___x_260_);
return v___x_261_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__4));
v___x_264_ = l_Lean_stringToMessageData(v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg(lean_object* v_name_268_, uint8_t v_kind_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___y_279_; 
v___x_273_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__1);
v___x_274_ = l_Lean_MessageData_ofName(v_name_268_);
v___x_275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_273_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
v___x_276_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__3);
v___x_277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_275_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
switch(v_kind_269_)
{
case 0:
{
lean_object* v___x_286_; 
v___x_286_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__6));
v___y_279_ = v___x_286_;
goto v___jp_278_;
}
case 1:
{
lean_object* v___x_287_; 
v___x_287_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__7));
v___y_279_ = v___x_287_;
goto v___jp_278_;
}
default: 
{
lean_object* v___x_288_; 
v___x_288_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__8));
v___y_279_ = v___x_288_;
goto v___jp_278_;
}
}
v___jp_278_:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_280_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_280_, 0, v___y_279_);
v___x_281_ = l_Lean_MessageData_ofFormat(v___x_280_);
v___x_282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_277_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__5);
v___x_284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_282_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg(v___x_284_, v___y_270_, v___y_271_);
return v___x_285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___boxed(lean_object* v_name_289_, lean_object* v_kind_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
uint8_t v_kind_boxed_294_; lean_object* v_res_295_; 
v_kind_boxed_294_ = lean_unbox(v_kind_290_);
v_res_295_ = l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg(v_name_289_, v_kind_boxed_294_, v___y_291_, v___y_292_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
return v_res_295_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__0));
v___x_298_ = l_Lean_stringToMessageData(v___x_297_);
return v___x_298_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__2));
v___x_301_ = l_Lean_stringToMessageData(v___x_300_);
return v___x_301_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__4));
v___x_304_ = l_Lean_stringToMessageData(v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg(lean_object* v_attrName_305_, lean_object* v_declName_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_310_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__1);
v___x_311_ = l_Lean_MessageData_ofName(v_attrName_305_);
v___x_312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_310_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v___x_313_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__3);
v___x_314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_312_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = 0;
v___x_316_ = l_Lean_MessageData_ofConstName(v_declName_306_, v___x_315_);
v___x_317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_314_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
v___x_318_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__5);
v___x_319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_317_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg(v___x_319_, v___y_307_, v___y_308_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___boxed(lean_object* v_attrName_321_, lean_object* v_declName_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg(v_attrName_321_, v_declName_322_, v___y_323_, v___y_324_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
return v_res_326_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___lam__7___closed__0(void){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_327_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___lam__7___closed__1(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___lam__7___closed__0, &l_Lake_registerOrderedTagAttribute___lam__7___closed__0_once, _init_l_Lake_registerOrderedTagAttribute___lam__7___closed__0);
v___x_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
return v___x_329_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___lam__7___closed__2(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___lam__7___closed__1, &l_Lake_registerOrderedTagAttribute___lam__7___closed__1_once, _init_l_Lake_registerOrderedTagAttribute___lam__7___closed__1);
v___x_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__7(lean_object* v_validate_332_, lean_object* v_a_333_, lean_object* v_name_334_, lean_object* v_decl_335_, lean_object* v_stx_336_, uint8_t v_kind_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v___y_342_; lean_object* v___y_343_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___x_384_; 
v___x_384_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_336_, v___y_338_, v___y_339_);
if (lean_obj_tag(v___x_384_) == 0)
{
uint8_t v___x_385_; uint8_t v___x_386_; 
lean_dec_ref(v___x_384_);
v___x_385_ = 0;
v___x_386_ = l_Lean_instBEqAttributeKind_beq(v_kind_337_, v___x_385_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; 
lean_dec(v_decl_335_);
lean_dec_ref(v_a_333_);
lean_dec_ref(v_validate_332_);
v___x_387_ = l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg(v_name_334_, v_kind_337_, v___y_338_, v___y_339_);
return v___x_387_;
}
else
{
v___y_378_ = v___y_338_;
v___y_379_ = v___y_339_;
goto v___jp_377_;
}
}
else
{
lean_dec(v_decl_335_);
lean_dec(v_name_334_);
lean_dec_ref(v_a_333_);
lean_dec_ref(v_validate_332_);
return v___x_384_;
}
v___jp_341_:
{
lean_object* v___x_344_; 
lean_inc(v___y_343_);
lean_inc_ref(v___y_342_);
lean_inc(v_decl_335_);
v___x_344_ = lean_apply_4(v_validate_332_, v_decl_335_, v___y_342_, v___y_343_, lean_box(0));
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_375_; 
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_375_ == 0)
{
lean_object* v_unused_376_; 
v_unused_376_ = lean_ctor_get(v___x_344_, 0);
lean_dec(v_unused_376_);
v___x_346_ = v___x_344_;
v_isShared_347_ = v_isSharedCheck_375_;
goto v_resetjp_345_;
}
else
{
lean_dec(v___x_344_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_375_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_348_; lean_object* v_toEnvExtension_349_; lean_object* v_env_350_; lean_object* v_nextMacroScope_351_; lean_object* v_ngen_352_; lean_object* v_auxDeclNGen_353_; lean_object* v_traceState_354_; lean_object* v_messages_355_; lean_object* v_infoState_356_; lean_object* v_snapshotTasks_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_373_; 
v___x_348_ = lean_st_ref_take(v___y_343_);
v_toEnvExtension_349_ = lean_ctor_get(v_a_333_, 0);
v_env_350_ = lean_ctor_get(v___x_348_, 0);
v_nextMacroScope_351_ = lean_ctor_get(v___x_348_, 1);
v_ngen_352_ = lean_ctor_get(v___x_348_, 2);
v_auxDeclNGen_353_ = lean_ctor_get(v___x_348_, 3);
v_traceState_354_ = lean_ctor_get(v___x_348_, 4);
v_messages_355_ = lean_ctor_get(v___x_348_, 6);
v_infoState_356_ = lean_ctor_get(v___x_348_, 7);
v_snapshotTasks_357_ = lean_ctor_get(v___x_348_, 8);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_373_ == 0)
{
lean_object* v_unused_374_; 
v_unused_374_ = lean_ctor_get(v___x_348_, 5);
lean_dec(v_unused_374_);
v___x_359_ = v___x_348_;
v_isShared_360_ = v_isSharedCheck_373_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_snapshotTasks_357_);
lean_inc(v_infoState_356_);
lean_inc(v_messages_355_);
lean_inc(v_traceState_354_);
lean_inc(v_auxDeclNGen_353_);
lean_inc(v_ngen_352_);
lean_inc(v_nextMacroScope_351_);
lean_inc(v_env_350_);
lean_dec(v___x_348_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_373_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v_asyncMode_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
v_asyncMode_361_ = lean_ctor_get(v_toEnvExtension_349_, 2);
lean_inc(v_asyncMode_361_);
v___x_362_ = lean_box(0);
v___x_363_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_333_, v_env_350_, v_decl_335_, v_asyncMode_361_, v___x_362_);
lean_dec(v_asyncMode_361_);
v___x_364_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___lam__7___closed__2, &l_Lake_registerOrderedTagAttribute___lam__7___closed__2_once, _init_l_Lake_registerOrderedTagAttribute___lam__7___closed__2);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 5, v___x_364_);
lean_ctor_set(v___x_359_, 0, v___x_363_);
v___x_366_ = v___x_359_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_nextMacroScope_351_);
lean_ctor_set(v_reuseFailAlloc_372_, 2, v_ngen_352_);
lean_ctor_set(v_reuseFailAlloc_372_, 3, v_auxDeclNGen_353_);
lean_ctor_set(v_reuseFailAlloc_372_, 4, v_traceState_354_);
lean_ctor_set(v_reuseFailAlloc_372_, 5, v___x_364_);
lean_ctor_set(v_reuseFailAlloc_372_, 6, v_messages_355_);
lean_ctor_set(v_reuseFailAlloc_372_, 7, v_infoState_356_);
lean_ctor_set(v_reuseFailAlloc_372_, 8, v_snapshotTasks_357_);
v___x_366_ = v_reuseFailAlloc_372_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_370_; 
v___x_367_ = lean_st_ref_set(v___y_343_, v___x_366_);
v___x_368_ = lean_box(0);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v___x_368_);
v___x_370_ = v___x_346_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_368_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
}
}
else
{
lean_dec(v_decl_335_);
lean_dec_ref(v_a_333_);
return v___x_344_;
}
}
v___jp_377_:
{
lean_object* v___x_380_; lean_object* v_env_381_; lean_object* v___x_382_; 
v___x_380_ = lean_st_ref_get(v___y_379_);
v_env_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc_ref(v_env_381_);
lean_dec(v___x_380_);
v___x_382_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_381_, v_decl_335_);
lean_dec_ref(v_env_381_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_dec(v_name_334_);
v___y_342_ = v___y_378_;
v___y_343_ = v___y_379_;
goto v___jp_341_;
}
else
{
lean_object* v___x_383_; 
lean_dec_ref(v___x_382_);
lean_dec_ref(v_a_333_);
lean_dec_ref(v_validate_332_);
v___x_383_ = l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg(v_name_334_, v_decl_335_, v___y_378_, v___y_379_);
return v___x_383_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__7___boxed(lean_object* v_validate_388_, lean_object* v_a_389_, lean_object* v_name_390_, lean_object* v_decl_391_, lean_object* v_stx_392_, lean_object* v_kind_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
uint8_t v_kind_boxed_397_; lean_object* v_res_398_; 
v_kind_boxed_397_ = lean_unbox(v_kind_393_);
v_res_398_ = l_Lake_registerOrderedTagAttribute___lam__7(v_validate_388_, v_a_389_, v_name_390_, v_decl_391_, v_stx_392_, v_kind_boxed_397_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute(lean_object* v_name_409_, lean_object* v_descr_410_, lean_object* v_validate_411_, lean_object* v_ref_412_){
_start:
{
lean_object* v___f_414_; lean_object* v___f_415_; lean_object* v___f_416_; lean_object* v___f_417_; lean_object* v___f_418_; lean_object* v___f_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___f_414_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___closed__0));
v___f_415_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___closed__1));
v___f_416_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___closed__2));
v___f_417_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___closed__3));
v___f_418_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___closed__5));
v___f_419_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___closed__6));
v___x_420_ = lean_box(2);
v___x_421_ = lean_box(0);
lean_inc(v_ref_412_);
v___x_422_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_422_, 0, v_ref_412_);
lean_ctor_set(v___x_422_, 1, v___f_419_);
lean_ctor_set(v___x_422_, 2, v___f_418_);
lean_ctor_set(v___x_422_, 3, v___f_417_);
lean_ctor_set(v___x_422_, 4, v___f_416_);
lean_ctor_set(v___x_422_, 5, v___f_415_);
lean_ctor_set(v___x_422_, 6, v___x_420_);
lean_ctor_set(v___x_422_, 7, v___x_421_);
v___x_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v___f_414_);
v___x_424_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_423_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; lean_object* v___f_426_; lean_object* v___f_427_; uint8_t v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_a_425_);
lean_dec_ref(v___x_424_);
lean_inc(v_name_409_);
v___f_426_ = lean_alloc_closure((void*)(l_Lake_registerOrderedTagAttribute___lam__6___boxed), 5, 1);
lean_closure_set(v___f_426_, 0, v_name_409_);
lean_inc(v_name_409_);
lean_inc(v_a_425_);
v___f_427_ = lean_alloc_closure((void*)(l_Lake_registerOrderedTagAttribute___lam__7___boxed), 9, 3);
lean_closure_set(v___f_427_, 0, v_validate_411_);
lean_closure_set(v___f_427_, 1, v_a_425_);
lean_closure_set(v___f_427_, 2, v_name_409_);
v___x_428_ = 0;
v___x_429_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_429_, 0, v_ref_412_);
lean_ctor_set(v___x_429_, 1, v_name_409_);
lean_ctor_set(v___x_429_, 2, v_descr_410_);
lean_ctor_set_uint8(v___x_429_, sizeof(void*)*3, v___x_428_);
v___x_430_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
lean_ctor_set(v___x_430_, 1, v___f_427_);
lean_ctor_set(v___x_430_, 2, v___f_426_);
lean_inc_ref(v___x_430_);
v___x_431_ = l_Lean_registerBuiltinAttribute(v___x_430_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_439_; 
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_439_ == 0)
{
lean_object* v_unused_440_; 
v_unused_440_ = lean_ctor_get(v___x_431_, 0);
lean_dec(v_unused_440_);
v___x_433_ = v___x_431_;
v_isShared_434_ = v_isSharedCheck_439_;
goto v_resetjp_432_;
}
else
{
lean_dec(v___x_431_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_439_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_435_; lean_object* v___x_437_; 
v___x_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_435_, 0, v___x_430_);
lean_ctor_set(v___x_435_, 1, v_a_425_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v___x_435_);
v___x_437_ = v___x_433_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_435_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
else
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
lean_dec_ref(v___x_430_);
lean_dec(v_a_425_);
v_a_441_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_448_ == 0)
{
v___x_443_ = v___x_431_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_431_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_441_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
else
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
lean_dec(v_ref_412_);
lean_dec_ref(v_validate_411_);
lean_dec_ref(v_descr_410_);
lean_dec(v_name_409_);
v_a_449_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_456_ == 0)
{
v___x_451_ = v___x_424_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_424_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_a_449_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___boxed(lean_object* v_name_457_, lean_object* v_descr_458_, lean_object* v_validate_459_, lean_object* v_ref_460_, lean_object* v_a_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lake_registerOrderedTagAttribute(v_name_457_, v_descr_458_, v_validate_459_, v_ref_460_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0(lean_object* v_00_u03b1_463_, lean_object* v_msg_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg(v_msg_464_, v___y_465_, v___y_466_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___boxed(lean_object* v_00_u03b1_469_, lean_object* v_msg_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0(v_00_u03b1_469_, v_msg_470_, v___y_471_, v___y_472_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1(lean_object* v_00_u03b1_475_, lean_object* v_attrName_476_, lean_object* v_declName_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg(v_attrName_476_, v_declName_477_, v___y_478_, v___y_479_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___boxed(lean_object* v_00_u03b1_482_, lean_object* v_attrName_483_, lean_object* v_declName_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1(v_00_u03b1_482_, v_attrName_483_, v_declName_484_, v___y_485_, v___y_486_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2(lean_object* v_00_u03b1_489_, lean_object* v_name_490_, uint8_t v_kind_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg(v_name_490_, v_kind_491_, v___y_492_, v___y_493_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___boxed(lean_object* v_00_u03b1_496_, lean_object* v_name_497_, lean_object* v_kind_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
uint8_t v_kind_boxed_502_; lean_object* v_res_503_; 
v_kind_boxed_502_ = lean_unbox(v_kind_498_);
v_res_503_ = l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2(v_00_u03b1_496_, v_name_497_, v_kind_boxed_502_, v___y_499_, v___y_500_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
return v_res_503_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0_spec__0(lean_object* v_a_504_, lean_object* v_as_505_, size_t v_i_506_, size_t v_stop_507_){
_start:
{
uint8_t v___x_508_; 
v___x_508_ = lean_usize_dec_eq(v_i_506_, v_stop_507_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_509_ = lean_array_uget_borrowed(v_as_505_, v_i_506_);
v___x_510_ = lean_name_eq(v_a_504_, v___x_509_);
if (v___x_510_ == 0)
{
size_t v___x_511_; size_t v___x_512_; 
v___x_511_ = ((size_t)1ULL);
v___x_512_ = lean_usize_add(v_i_506_, v___x_511_);
v_i_506_ = v___x_512_;
goto _start;
}
else
{
return v___x_510_;
}
}
else
{
uint8_t v___x_514_; 
v___x_514_ = 0;
return v___x_514_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0_spec__0___boxed(lean_object* v_a_515_, lean_object* v_as_516_, lean_object* v_i_517_, lean_object* v_stop_518_){
_start:
{
size_t v_i_boxed_519_; size_t v_stop_boxed_520_; uint8_t v_res_521_; lean_object* v_r_522_; 
v_i_boxed_519_ = lean_unbox_usize(v_i_517_);
lean_dec(v_i_517_);
v_stop_boxed_520_ = lean_unbox_usize(v_stop_518_);
lean_dec(v_stop_518_);
v_res_521_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0_spec__0(v_a_515_, v_as_516_, v_i_boxed_519_, v_stop_boxed_520_);
lean_dec_ref(v_as_516_);
lean_dec(v_a_515_);
v_r_522_ = lean_box(v_res_521_);
return v_r_522_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0(lean_object* v_as_523_, lean_object* v_a_524_){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; 
v___x_525_ = lean_unsigned_to_nat(0u);
v___x_526_ = lean_array_get_size(v_as_523_);
v___x_527_ = lean_nat_dec_lt(v___x_525_, v___x_526_);
if (v___x_527_ == 0)
{
return v___x_527_;
}
else
{
if (v___x_527_ == 0)
{
return v___x_527_;
}
else
{
size_t v___x_528_; size_t v___x_529_; uint8_t v___x_530_; 
v___x_528_ = ((size_t)0ULL);
v___x_529_ = lean_usize_of_nat(v___x_526_);
v___x_530_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0_spec__0(v_a_524_, v_as_523_, v___x_528_, v___x_529_);
return v___x_530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0___boxed(lean_object* v_as_531_, lean_object* v_a_532_){
_start:
{
uint8_t v_res_533_; lean_object* v_r_534_; 
v_res_533_ = l_Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0(v_as_531_, v_a_532_);
lean_dec(v_a_532_);
lean_dec_ref(v_as_531_);
v_r_534_ = lean_box(v_res_533_);
return v_r_534_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___redArg(lean_object* v_as_535_, lean_object* v_k_536_, lean_object* v_x_537_, lean_object* v_x_538_){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v_m_541_; lean_object* v_a_542_; uint8_t v___x_543_; 
v___x_539_ = lean_nat_add(v_x_537_, v_x_538_);
v___x_540_ = lean_unsigned_to_nat(1u);
v_m_541_ = lean_nat_shiftr(v___x_539_, v___x_540_);
lean_dec(v___x_539_);
v_a_542_ = lean_array_fget_borrowed(v_as_535_, v_m_541_);
v___x_543_ = l_Lean_Name_quickLt(v_a_542_, v_k_536_);
if (v___x_543_ == 0)
{
uint8_t v___x_544_; 
lean_dec(v_x_538_);
v___x_544_ = l_Lean_Name_quickLt(v_k_536_, v_a_542_);
if (v___x_544_ == 0)
{
uint8_t v___x_545_; 
lean_dec(v_m_541_);
lean_dec(v_x_537_);
v___x_545_ = 1;
return v___x_545_;
}
else
{
lean_object* v___x_546_; uint8_t v___x_547_; 
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = lean_nat_dec_eq(v_m_541_, v___x_546_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_548_ = lean_nat_sub(v_m_541_, v___x_540_);
lean_dec(v_m_541_);
v___x_549_ = lean_nat_dec_lt(v___x_548_, v_x_537_);
if (v___x_549_ == 0)
{
v_x_538_ = v___x_548_;
goto _start;
}
else
{
lean_dec(v___x_548_);
lean_dec(v_x_537_);
return v___x_543_;
}
}
else
{
lean_dec(v_m_541_);
lean_dec(v_x_537_);
return v___x_543_;
}
}
}
else
{
lean_object* v___x_551_; uint8_t v___x_552_; 
lean_dec(v_x_537_);
v___x_551_ = lean_nat_add(v_m_541_, v___x_540_);
lean_dec(v_m_541_);
v___x_552_ = lean_nat_dec_le(v___x_551_, v_x_538_);
if (v___x_552_ == 0)
{
lean_dec(v___x_551_);
lean_dec(v_x_538_);
return v___x_552_;
}
else
{
v_x_537_ = v___x_551_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___redArg___boxed(lean_object* v_as_554_, lean_object* v_k_555_, lean_object* v_x_556_, lean_object* v_x_557_){
_start:
{
uint8_t v_res_558_; lean_object* v_r_559_; 
v_res_558_ = l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___redArg(v_as_554_, v_k_555_, v_x_556_, v_x_557_);
lean_dec(v_k_555_);
lean_dec_ref(v_as_554_);
v_r_559_ = lean_box(v_res_558_);
return v_r_559_;
}
}
static lean_object* _init_l_Lake_OrderedTagAttribute_hasTag___closed__0(void){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Array_instInhabited(lean_box(0));
return v___x_560_;
}
}
LEAN_EXPORT uint8_t l_Lake_OrderedTagAttribute_hasTag(lean_object* v_attr_561_, lean_object* v_env_562_, lean_object* v_decl_563_){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = lean_obj_once(&l_Lake_OrderedTagAttribute_hasTag___closed__0, &l_Lake_OrderedTagAttribute_hasTag___closed__0_once, _init_l_Lake_OrderedTagAttribute_hasTag___closed__0);
v___x_565_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_562_, v_decl_563_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_ext_566_; lean_object* v_toEnvExtension_567_; lean_object* v_asyncMode_568_; lean_object* v___x_569_; lean_object* v___x_570_; uint8_t v___x_571_; 
v_ext_566_ = lean_ctor_get(v_attr_561_, 1);
v_toEnvExtension_567_ = lean_ctor_get(v_ext_566_, 0);
v_asyncMode_568_ = lean_ctor_get(v_toEnvExtension_567_, 2);
v___x_569_ = lean_box(0);
v___x_570_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_564_, v_ext_566_, v_env_562_, v_asyncMode_568_, v___x_569_);
v___x_571_ = l_Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0(v___x_570_, v_decl_563_);
lean_dec(v___x_570_);
return v___x_571_;
}
else
{
lean_object* v_val_572_; lean_object* v_ext_573_; uint8_t v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; uint8_t v___x_578_; 
v_val_572_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_val_572_);
lean_dec_ref(v___x_565_);
v_ext_573_ = lean_ctor_get(v_attr_561_, 1);
v___x_574_ = 0;
v___x_575_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_564_, v_ext_573_, v_env_562_, v_val_572_, v___x_574_);
lean_dec(v_val_572_);
lean_dec_ref(v_env_562_);
v___x_576_ = lean_unsigned_to_nat(0u);
v___x_577_ = lean_array_get_size(v___x_575_);
v___x_578_ = lean_nat_dec_lt(v___x_576_, v___x_577_);
if (v___x_578_ == 0)
{
lean_dec_ref(v___x_575_);
return v___x_578_;
}
else
{
lean_object* v___x_579_; lean_object* v___x_580_; uint8_t v___x_581_; 
v___x_579_ = lean_unsigned_to_nat(1u);
v___x_580_ = lean_nat_sub(v___x_577_, v___x_579_);
v___x_581_ = lean_nat_dec_le(v___x_576_, v___x_580_);
if (v___x_581_ == 0)
{
lean_dec(v___x_580_);
lean_dec_ref(v___x_575_);
return v___x_581_;
}
else
{
uint8_t v___x_582_; 
v___x_582_ = l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___redArg(v___x_575_, v_decl_563_, v___x_576_, v___x_580_);
lean_dec_ref(v___x_575_);
return v___x_582_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrderedTagAttribute_hasTag___boxed(lean_object* v_attr_583_, lean_object* v_env_584_, lean_object* v_decl_585_){
_start:
{
uint8_t v_res_586_; lean_object* v_r_587_; 
v_res_586_ = l_Lake_OrderedTagAttribute_hasTag(v_attr_583_, v_env_584_, v_decl_585_);
lean_dec(v_decl_585_);
lean_dec_ref(v_attr_583_);
v_r_587_ = lean_box(v_res_586_);
return v_r_587_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1(lean_object* v_as_588_, lean_object* v_k_589_, lean_object* v_x_590_, lean_object* v_x_591_, lean_object* v_x_592_){
_start:
{
uint8_t v___x_593_; 
v___x_593_ = l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___redArg(v_as_588_, v_k_589_, v_x_590_, v_x_591_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___boxed(lean_object* v_as_594_, lean_object* v_k_595_, lean_object* v_x_596_, lean_object* v_x_597_, lean_object* v_x_598_){
_start:
{
uint8_t v_res_599_; lean_object* v_r_600_; 
v_res_599_ = l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1(v_as_594_, v_k_595_, v_x_596_, v_x_597_, v_x_598_);
lean_dec(v_k_595_);
lean_dec_ref(v_as_594_);
v_r_600_ = lean_box(v_res_599_);
return v_r_600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrderedTagAttribute_getAllEntries_spec__0(lean_object* v_as_601_, size_t v_i_602_, size_t v_stop_603_, lean_object* v_b_604_){
_start:
{
uint8_t v___x_605_; 
v___x_605_ = lean_usize_dec_eq(v_i_602_, v_stop_603_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; lean_object* v___x_607_; size_t v___x_608_; size_t v___x_609_; 
v___x_606_ = lean_array_uget_borrowed(v_as_601_, v_i_602_);
v___x_607_ = l_Array_append___redArg(v_b_604_, v___x_606_);
v___x_608_ = ((size_t)1ULL);
v___x_609_ = lean_usize_add(v_i_602_, v___x_608_);
v_i_602_ = v___x_609_;
v_b_604_ = v___x_607_;
goto _start;
}
else
{
return v_b_604_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrderedTagAttribute_getAllEntries_spec__0___boxed(lean_object* v_as_611_, lean_object* v_i_612_, lean_object* v_stop_613_, lean_object* v_b_614_){
_start:
{
size_t v_i_boxed_615_; size_t v_stop_boxed_616_; lean_object* v_res_617_; 
v_i_boxed_615_ = lean_unbox_usize(v_i_612_);
lean_dec(v_i_612_);
v_stop_boxed_616_ = lean_unbox_usize(v_stop_613_);
lean_dec(v_stop_613_);
v_res_617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrderedTagAttribute_getAllEntries_spec__0(v_as_611_, v_i_boxed_615_, v_stop_boxed_616_, v_b_614_);
lean_dec_ref(v_as_611_);
return v_res_617_;
}
}
static lean_object* _init_l_Lake_OrderedTagAttribute_getAllEntries___closed__0(void){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = lean_obj_once(&l_Lake_OrderedTagAttribute_hasTag___closed__0, &l_Lake_OrderedTagAttribute_hasTag___closed__0_once, _init_l_Lake_OrderedTagAttribute_hasTag___closed__0);
v___x_619_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrderedTagAttribute_getAllEntries(lean_object* v_attr_620_, lean_object* v_env_621_){
_start:
{
lean_object* v_ext_622_; lean_object* v_toEnvExtension_623_; lean_object* v_asyncMode_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v_s_627_; lean_object* v___y_629_; lean_object* v_importedEntries_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v_ext_622_ = lean_ctor_get(v_attr_620_, 1);
v_toEnvExtension_623_ = lean_ctor_get(v_ext_622_, 0);
v_asyncMode_624_ = lean_ctor_get(v_toEnvExtension_623_, 2);
v___x_625_ = lean_obj_once(&l_Lake_OrderedTagAttribute_getAllEntries___closed__0, &l_Lake_OrderedTagAttribute_getAllEntries___closed__0_once, _init_l_Lake_OrderedTagAttribute_getAllEntries___closed__0);
v___x_626_ = lean_box(0);
v_s_627_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_625_, v_toEnvExtension_623_, v_env_621_, v_asyncMode_624_, v___x_626_);
v_importedEntries_632_ = lean_ctor_get(v_s_627_, 0);
lean_inc_ref(v_importedEntries_632_);
v___x_633_ = lean_unsigned_to_nat(0u);
v___x_634_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___closed__4));
v___x_635_ = lean_array_get_size(v_importedEntries_632_);
v___x_636_ = lean_nat_dec_lt(v___x_633_, v___x_635_);
if (v___x_636_ == 0)
{
lean_dec_ref(v_importedEntries_632_);
v___y_629_ = v___x_634_;
goto v___jp_628_;
}
else
{
uint8_t v___x_637_; 
v___x_637_ = lean_nat_dec_le(v___x_635_, v___x_635_);
if (v___x_637_ == 0)
{
if (v___x_636_ == 0)
{
lean_dec_ref(v_importedEntries_632_);
v___y_629_ = v___x_634_;
goto v___jp_628_;
}
else
{
size_t v___x_638_; size_t v___x_639_; lean_object* v___x_640_; 
v___x_638_ = ((size_t)0ULL);
v___x_639_ = lean_usize_of_nat(v___x_635_);
v___x_640_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrderedTagAttribute_getAllEntries_spec__0(v_importedEntries_632_, v___x_638_, v___x_639_, v___x_634_);
lean_dec_ref(v_importedEntries_632_);
v___y_629_ = v___x_640_;
goto v___jp_628_;
}
}
else
{
size_t v___x_641_; size_t v___x_642_; lean_object* v___x_643_; 
v___x_641_ = ((size_t)0ULL);
v___x_642_ = lean_usize_of_nat(v___x_635_);
v___x_643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrderedTagAttribute_getAllEntries_spec__0(v_importedEntries_632_, v___x_641_, v___x_642_, v___x_634_);
lean_dec_ref(v_importedEntries_632_);
v___y_629_ = v___x_643_;
goto v___jp_628_;
}
}
v___jp_628_:
{
lean_object* v_state_630_; lean_object* v___x_631_; 
v_state_630_ = lean_ctor_get(v_s_627_, 1);
lean_inc(v_state_630_);
lean_dec(v_s_627_);
v___x_631_ = l_Array_append___redArg(v___y_629_, v_state_630_);
lean_dec(v_state_630_);
return v___x_631_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrderedTagAttribute_getAllEntries___boxed(lean_object* v_attr_644_, lean_object* v_env_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_644_, v_env_645_);
lean_dec_ref(v_attr_644_);
return v_res_646_;
}
}
lean_object* runtime_initialize_Lean_Attributes(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_OrderedTagAttribute(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedOrderedTagAttribute_default = _init_l_Lake_instInhabitedOrderedTagAttribute_default();
lean_mark_persistent(l_Lake_instInhabitedOrderedTagAttribute_default);
l_Lake_instInhabitedOrderedTagAttribute = _init_l_Lake_instInhabitedOrderedTagAttribute();
lean_mark_persistent(l_Lake_instInhabitedOrderedTagAttribute);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_OrderedTagAttribute(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lake_registerOrderedTagAttribute___auto__1 = _init_l_Lake_registerOrderedTagAttribute___auto__1();
lean_mark_persistent(l_Lake_registerOrderedTagAttribute___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Attributes(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_OrderedTagAttribute(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_OrderedTagAttribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_OrderedTagAttribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_OrderedTagAttribute(builtin);
}
#ifdef __cplusplus
}
#endif

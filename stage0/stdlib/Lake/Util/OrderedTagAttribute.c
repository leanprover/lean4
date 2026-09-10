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
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
static const lean_ctor_object l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___closed__0_value),((lean_object*)&l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___closed__0_value),((lean_object*)&l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___closed__0_value)}};
static const lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___closed__1 = (const lean_object*)&l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_instInhabitedOrderedTagAttribute_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instInhabitedOrderedTagAttribute_default___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedOrderedTagAttribute_default___closed__0_value;
static const lean_closure_object l_Lake_instInhabitedOrderedTagAttribute_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instInhabitedOrderedTagAttribute_default___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___closed__1 = (const lean_object*)&l_Lake_instInhabitedOrderedTagAttribute_default___closed__1_value;
static const lean_closure_object l_Lake_instInhabitedOrderedTagAttribute_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__2___boxed(lean_object*, lean_object*);
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
static const lean_closure_object l_Lake_registerOrderedTagAttribute___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_registerOrderedTagAttribute___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_OrderedTagAttribute_hasTag___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_OrderedTagAttribute_hasTag___closed__0;
LEAN_EXPORT uint8_t l_Lake_OrderedTagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrderedTagAttribute_hasTag___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___lam__2(lean_object* v_x_22_, lean_object* v_x_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = ((lean_object*)(l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___closed__1));
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___boxed(lean_object* v_x_25_, lean_object* v_x_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Lake_instInhabitedOrderedTagAttribute_default___lam__2(v_x_25_, v_x_26_);
lean_dec_ref(v_x_26_);
lean_dec_ref(v_x_25_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___lam__3(lean_object* v_x_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lean_box(0);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedOrderedTagAttribute_default___lam__3___boxed(lean_object* v_x_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lake_instInhabitedOrderedTagAttribute_default___lam__3(v_x_30_);
lean_dec_ref(v_x_30_);
return v_res_31_;
}
}
static lean_object* _init_l_Lake_instInhabitedOrderedTagAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_36_;
}
}
static lean_object* _init_l_Lake_instInhabitedOrderedTagAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_37_; lean_object* v___f_38_; lean_object* v___f_39_; lean_object* v___f_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___f_37_ = ((lean_object*)(l_Lake_instInhabitedOrderedTagAttribute_default___closed__3));
v___f_38_ = ((lean_object*)(l_Lake_instInhabitedOrderedTagAttribute_default___closed__2));
v___f_39_ = ((lean_object*)(l_Lake_instInhabitedOrderedTagAttribute_default___closed__1));
v___f_40_ = ((lean_object*)(l_Lake_instInhabitedOrderedTagAttribute_default___closed__0));
v___x_41_ = lean_box(0);
v___x_42_ = lean_obj_once(&l_Lake_instInhabitedOrderedTagAttribute_default___closed__4, &l_Lake_instInhabitedOrderedTagAttribute_default___closed__4_once, _init_l_Lake_instInhabitedOrderedTagAttribute_default___closed__4);
v___x_43_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
lean_ctor_set(v___x_43_, 1, v___x_41_);
lean_ctor_set(v___x_43_, 2, v___f_40_);
lean_ctor_set(v___x_43_, 3, v___f_39_);
lean_ctor_set(v___x_43_, 4, v___f_38_);
lean_ctor_set(v___x_43_, 5, v___f_37_);
return v___x_43_;
}
}
static lean_object* _init_l_Lake_instInhabitedOrderedTagAttribute_default___closed__6(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_44_ = lean_obj_once(&l_Lake_instInhabitedOrderedTagAttribute_default___closed__5, &l_Lake_instInhabitedOrderedTagAttribute_default___closed__5_once, _init_l_Lake_instInhabitedOrderedTagAttribute_default___closed__5);
v___x_45_ = l_Lean_instInhabitedAttributeImpl_default;
v___x_46_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
lean_ctor_set(v___x_46_, 1, v___x_44_);
return v___x_46_;
}
}
static lean_object* _init_l_Lake_instInhabitedOrderedTagAttribute_default(void){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lean_obj_once(&l_Lake_instInhabitedOrderedTagAttribute_default___closed__6, &l_Lake_instInhabitedOrderedTagAttribute_default___closed__6_once, _init_l_Lake_instInhabitedOrderedTagAttribute_default___closed__6);
return v___x_47_;
}
}
static lean_object* _init_l_Lake_instInhabitedOrderedTagAttribute(void){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Lake_instInhabitedOrderedTagAttribute_default;
return v___x_48_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__12(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___auto__1___closed__10));
v___x_76_ = l_Lean_mkAtom(v___x_75_);
return v___x_76_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__13(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_77_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___auto__1___closed__12, &l_Lake_registerOrderedTagAttribute___auto__1___closed__12_once, _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__12);
v___x_78_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___auto__1___closed__5));
v___x_79_ = lean_array_push(v___x_78_, v___x_77_);
return v___x_79_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__18(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___auto__1___closed__17));
v___x_89_ = l_Lean_mkAtom(v___x_88_);
return v___x_89_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__19(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_90_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___auto__1___closed__18, &l_Lake_registerOrderedTagAttribute___auto__1___closed__18_once, _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__18);
v___x_91_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___auto__1___closed__5));
v___x_92_ = lean_array_push(v___x_91_, v___x_90_);
return v___x_92_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__20(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_93_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___auto__1___closed__19, &l_Lake_registerOrderedTagAttribute___auto__1___closed__19_once, _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__19);
v___x_94_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___auto__1___closed__16));
v___x_95_ = lean_box(2);
v___x_96_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
lean_ctor_set(v___x_96_, 1, v___x_94_);
lean_ctor_set(v___x_96_, 2, v___x_93_);
return v___x_96_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__21(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___auto__1___closed__20, &l_Lake_registerOrderedTagAttribute___auto__1___closed__20_once, _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__20);
v___x_98_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___auto__1___closed__13, &l_Lake_registerOrderedTagAttribute___auto__1___closed__13_once, _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__13);
v___x_99_ = lean_array_push(v___x_98_, v___x_97_);
return v___x_99_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__22(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_100_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___auto__1___closed__21, &l_Lake_registerOrderedTagAttribute___auto__1___closed__21_once, _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__21);
v___x_101_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___auto__1___closed__11));
v___x_102_ = lean_box(2);
v___x_103_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v___x_101_);
lean_ctor_set(v___x_103_, 2, v___x_100_);
return v___x_103_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__23(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___auto__1___closed__22, &l_Lake_registerOrderedTagAttribute___auto__1___closed__22_once, _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__22);
v___x_105_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___auto__1___closed__5));
v___x_106_ = lean_array_push(v___x_105_, v___x_104_);
return v___x_106_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__24(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_107_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___auto__1___closed__23, &l_Lake_registerOrderedTagAttribute___auto__1___closed__23_once, _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__23);
v___x_108_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___auto__1___closed__9));
v___x_109_ = lean_box(2);
v___x_110_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
lean_ctor_set(v___x_110_, 1, v___x_108_);
lean_ctor_set(v___x_110_, 2, v___x_107_);
return v___x_110_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__25(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_111_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___auto__1___closed__24, &l_Lake_registerOrderedTagAttribute___auto__1___closed__24_once, _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__24);
v___x_112_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___auto__1___closed__5));
v___x_113_ = lean_array_push(v___x_112_, v___x_111_);
return v___x_113_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__26(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_114_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___auto__1___closed__25, &l_Lake_registerOrderedTagAttribute___auto__1___closed__25_once, _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__25);
v___x_115_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___auto__1___closed__7));
v___x_116_ = lean_box(2);
v___x_117_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v___x_115_);
lean_ctor_set(v___x_117_, 2, v___x_114_);
return v___x_117_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__27(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_118_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___auto__1___closed__26, &l_Lake_registerOrderedTagAttribute___auto__1___closed__26_once, _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__26);
v___x_119_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___auto__1___closed__5));
v___x_120_ = lean_array_push(v___x_119_, v___x_118_);
return v___x_120_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__28(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_121_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___auto__1___closed__27, &l_Lake_registerOrderedTagAttribute___auto__1___closed__27_once, _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__27);
v___x_122_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___auto__1___closed__4));
v___x_123_ = lean_box(2);
v___x_124_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
lean_ctor_set(v___x_124_, 1, v___x_122_);
lean_ctor_set(v___x_124_, 2, v___x_121_);
return v___x_124_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___auto__1(void){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___auto__1___closed__28, &l_Lake_registerOrderedTagAttribute___auto__1___closed__28_once, _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__28);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__0(lean_object* v_es_126_){
_start:
{
lean_inc_ref(v_es_126_);
return v_es_126_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__0___boxed(lean_object* v_es_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lake_registerOrderedTagAttribute___lam__0(v_es_127_);
lean_dec_ref(v_es_127_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__1(lean_object* v_s_141_){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_142_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___lam__1___closed__5));
v___x_143_ = lean_array_get_size(v_s_141_);
v___x_144_ = l_Nat_reprFast(v___x_143_);
v___x_145_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
v___x_146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_142_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__1___boxed(lean_object* v_s_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lake_registerOrderedTagAttribute___lam__1(v_s_147_);
lean_dec_ref(v_s_147_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__2(lean_object* v_x_149_, lean_object* v_s_150_){
_start:
{
lean_object* v___x_151_; 
lean_inc_ref_n(v_s_150_, 2);
v___x_151_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_151_, 0, v_s_150_);
lean_ctor_set(v___x_151_, 1, v_s_150_);
lean_ctor_set(v___x_151_, 2, v_s_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__2___boxed(lean_object* v_x_152_, lean_object* v_s_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lake_registerOrderedTagAttribute___lam__2(v_x_152_, v_s_153_);
lean_dec_ref(v_x_152_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__3(lean_object* v_s_155_, lean_object* v_n_156_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = lean_array_push(v_s_155_, v_n_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__4(lean_object* v___x_158_, lean_object* v_x_159_, lean_object* v_x_160_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_162_, 0, v___x_158_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__4___boxed(lean_object* v___x_163_, lean_object* v_x_164_, lean_object* v_x_165_, lean_object* v___y_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lake_registerOrderedTagAttribute___lam__4(v___x_163_, v_x_164_, v_x_165_);
lean_dec_ref(v_x_165_);
lean_dec_ref(v_x_164_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__5(lean_object* v___x_168_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_170_, 0, v___x_168_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__5___boxed(lean_object* v___x_171_, lean_object* v___y_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lake_registerOrderedTagAttribute___lam__5(v___x_171_);
return v_res_173_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_174_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__0);
v___x_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
return v___x_176_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_177_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1);
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_179_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
lean_ctor_set(v___x_179_, 2, v___x_178_);
lean_ctor_set(v___x_179_, 3, v___x_178_);
lean_ctor_set(v___x_179_, 4, v___x_177_);
lean_ctor_set(v___x_179_, 5, v___x_177_);
lean_ctor_set(v___x_179_, 6, v___x_177_);
lean_ctor_set(v___x_179_, 7, v___x_177_);
lean_ctor_set(v___x_179_, 8, v___x_177_);
lean_ctor_set(v___x_179_, 9, v___x_177_);
lean_ctor_set(v___x_179_, 10, v___x_177_);
return v___x_179_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = lean_unsigned_to_nat(32u);
v___x_181_ = lean_mk_empty_array_with_capacity(v___x_180_);
v___x_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
return v___x_182_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_183_ = ((size_t)5ULL);
v___x_184_ = lean_unsigned_to_nat(0u);
v___x_185_ = lean_unsigned_to_nat(32u);
v___x_186_ = lean_mk_empty_array_with_capacity(v___x_185_);
v___x_187_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__3);
v___x_188_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v___x_186_);
lean_ctor_set(v___x_188_, 2, v___x_184_);
lean_ctor_set(v___x_188_, 3, v___x_184_);
lean_ctor_set_usize(v___x_188_, 4, v___x_183_);
return v___x_188_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_189_ = lean_box(1);
v___x_190_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__4);
v___x_191_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1);
v___x_192_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v___x_190_);
lean_ctor_set(v___x_192_, 2, v___x_189_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0(lean_object* v_msgData_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v___x_197_; lean_object* v_toCold_198_; lean_object* v_env_199_; lean_object* v_options_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_197_ = lean_st_ref_get(v___y_195_);
v_toCold_198_ = lean_ctor_get(v___y_194_, 0);
v_env_199_ = lean_ctor_get(v___x_197_, 0);
lean_inc_ref(v_env_199_);
lean_dec(v___x_197_);
v_options_200_ = lean_ctor_get(v_toCold_198_, 2);
v___x_201_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__2);
v___x_202_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_200_);
v___x_203_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_203_, 0, v_env_199_);
lean_ctor_set(v___x_203_, 1, v___x_201_);
lean_ctor_set(v___x_203_, 2, v___x_202_);
lean_ctor_set(v___x_203_, 3, v_options_200_);
v___x_204_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v_msgData_193_);
v___x_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___boxed(lean_object* v_msgData_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0(v_msgData_206_, v___y_207_, v___y_208_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg(lean_object* v_msg_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_ref_215_; lean_object* v___x_216_; lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_225_; 
v_ref_215_ = lean_ctor_get(v___y_212_, 2);
v___x_216_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0(v_msg_211_, v___y_212_, v___y_213_);
v_a_217_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_225_ == 0)
{
v___x_219_ = v___x_216_;
v_isShared_220_ = v_isSharedCheck_225_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_216_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_225_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_221_; lean_object* v___x_223_; 
lean_inc(v_ref_215_);
v___x_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_221_, 0, v_ref_215_);
lean_ctor_set(v___x_221_, 1, v_a_217_);
if (v_isShared_220_ == 0)
{
lean_ctor_set_tag(v___x_219_, 1);
lean_ctor_set(v___x_219_, 0, v___x_221_);
v___x_223_ = v___x_219_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_221_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg___boxed(lean_object* v_msg_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg(v_msg_226_, v___y_227_, v___y_228_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
return v_res_230_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___lam__6___closed__1(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___lam__6___closed__0));
v___x_233_ = l_Lean_stringToMessageData(v___x_232_);
return v___x_233_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___lam__6___closed__3(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___lam__6___closed__2));
v___x_236_ = l_Lean_stringToMessageData(v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__6(lean_object* v_name_237_, lean_object* v_decl_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_242_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___lam__6___closed__1, &l_Lake_registerOrderedTagAttribute___lam__6___closed__1_once, _init_l_Lake_registerOrderedTagAttribute___lam__6___closed__1);
v___x_243_ = l_Lean_MessageData_ofName(v_name_237_);
v___x_244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_242_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___lam__6___closed__3, &l_Lake_registerOrderedTagAttribute___lam__6___closed__3_once, _init_l_Lake_registerOrderedTagAttribute___lam__6___closed__3);
v___x_246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_244_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
v___x_247_ = l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg(v___x_246_, v___y_239_, v___y_240_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__6___boxed(lean_object* v_name_248_, lean_object* v_decl_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lake_registerOrderedTagAttribute___lam__6(v_name_248_, v_decl_249_, v___y_250_, v___y_251_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
lean_dec(v_decl_249_);
return v_res_253_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__0));
v___x_256_ = l_Lean_stringToMessageData(v___x_255_);
return v___x_256_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__2));
v___x_259_ = l_Lean_stringToMessageData(v___x_258_);
return v___x_259_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__4));
v___x_262_ = l_Lean_stringToMessageData(v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg(lean_object* v_name_266_, uint8_t v_kind_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___y_277_; 
v___x_271_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__1);
v___x_272_ = l_Lean_MessageData_ofName(v_name_266_);
v___x_273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_271_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
v___x_274_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__3);
v___x_275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_273_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
switch(v_kind_267_)
{
case 0:
{
lean_object* v___x_284_; 
v___x_284_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__6));
v___y_277_ = v___x_284_;
goto v___jp_276_;
}
case 1:
{
lean_object* v___x_285_; 
v___x_285_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__7));
v___y_277_ = v___x_285_;
goto v___jp_276_;
}
default: 
{
lean_object* v___x_286_; 
v___x_286_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__8));
v___y_277_ = v___x_286_;
goto v___jp_276_;
}
}
v___jp_276_:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
lean_inc_ref(v___y_277_);
v___x_278_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_278_, 0, v___y_277_);
v___x_279_ = l_Lean_MessageData_ofFormat(v___x_278_);
v___x_280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_275_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__5);
v___x_282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_280_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg(v___x_282_, v___y_268_, v___y_269_);
return v___x_283_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___boxed(lean_object* v_name_287_, lean_object* v_kind_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
uint8_t v_kind_boxed_292_; lean_object* v_res_293_; 
v_kind_boxed_292_ = lean_unbox(v_kind_288_);
v_res_293_ = l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg(v_name_287_, v_kind_boxed_292_, v___y_289_, v___y_290_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
return v_res_293_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__0));
v___x_296_ = l_Lean_stringToMessageData(v___x_295_);
return v___x_296_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__2));
v___x_299_ = l_Lean_stringToMessageData(v___x_298_);
return v___x_299_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__4));
v___x_302_ = l_Lean_stringToMessageData(v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg(lean_object* v_attrName_303_, lean_object* v_declName_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_308_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__1);
v___x_309_ = l_Lean_MessageData_ofName(v_attrName_303_);
v___x_310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_308_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
v___x_311_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__3);
v___x_312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_310_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v___x_313_ = 0;
v___x_314_ = l_Lean_MessageData_ofConstName(v_declName_304_, v___x_313_);
v___x_315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_312_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
v___x_316_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__5);
v___x_317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_315_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
v___x_318_ = l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg(v___x_317_, v___y_305_, v___y_306_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___boxed(lean_object* v_attrName_319_, lean_object* v_declName_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg(v_attrName_319_, v_declName_320_, v___y_321_, v___y_322_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
return v_res_324_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___lam__7___closed__0(void){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_325_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___lam__7___closed__1(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___lam__7___closed__0, &l_Lake_registerOrderedTagAttribute___lam__7___closed__0_once, _init_l_Lake_registerOrderedTagAttribute___lam__7___closed__0);
v___x_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
return v___x_327_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___lam__7___closed__2(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___lam__7___closed__1, &l_Lake_registerOrderedTagAttribute___lam__7___closed__1_once, _init_l_Lake_registerOrderedTagAttribute___lam__7___closed__1);
v___x_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__7(lean_object* v_validate_330_, lean_object* v_a_331_, lean_object* v_name_332_, lean_object* v_decl_333_, lean_object* v_stx_334_, uint8_t v_kind_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v___y_340_; lean_object* v___y_341_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___x_382_; 
v___x_382_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_334_, v___y_336_, v___y_337_);
if (lean_obj_tag(v___x_382_) == 0)
{
uint8_t v___x_383_; uint8_t v___x_384_; 
lean_dec_ref_known(v___x_382_, 1);
v___x_383_ = 0;
v___x_384_ = l_Lean_instBEqAttributeKind_beq(v_kind_335_, v___x_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; 
lean_dec(v_decl_333_);
lean_dec_ref(v_a_331_);
lean_dec_ref(v_validate_330_);
v___x_385_ = l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg(v_name_332_, v_kind_335_, v___y_336_, v___y_337_);
return v___x_385_;
}
else
{
v___y_376_ = v___y_336_;
v___y_377_ = v___y_337_;
goto v___jp_375_;
}
}
else
{
lean_dec(v_decl_333_);
lean_dec(v_name_332_);
lean_dec_ref(v_a_331_);
lean_dec_ref(v_validate_330_);
return v___x_382_;
}
v___jp_339_:
{
lean_object* v___x_342_; 
lean_inc(v___y_341_);
lean_inc_ref(v___y_340_);
lean_inc(v_decl_333_);
v___x_342_ = lean_apply_4(v_validate_330_, v_decl_333_, v___y_340_, v___y_341_, lean_box(0));
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_373_; 
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_373_ == 0)
{
lean_object* v_unused_374_; 
v_unused_374_ = lean_ctor_get(v___x_342_, 0);
lean_dec(v_unused_374_);
v___x_344_ = v___x_342_;
v_isShared_345_ = v_isSharedCheck_373_;
goto v_resetjp_343_;
}
else
{
lean_dec(v___x_342_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_373_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_346_; lean_object* v_toEnvExtension_347_; lean_object* v_env_348_; lean_object* v_nextMacroScope_349_; lean_object* v_ngen_350_; lean_object* v_auxDeclNGen_351_; lean_object* v_traceState_352_; lean_object* v_messages_353_; lean_object* v_infoState_354_; lean_object* v_snapshotTasks_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_371_; 
v___x_346_ = lean_st_ref_take(v___y_341_);
v_toEnvExtension_347_ = lean_ctor_get(v_a_331_, 0);
v_env_348_ = lean_ctor_get(v___x_346_, 0);
v_nextMacroScope_349_ = lean_ctor_get(v___x_346_, 1);
v_ngen_350_ = lean_ctor_get(v___x_346_, 2);
v_auxDeclNGen_351_ = lean_ctor_get(v___x_346_, 3);
v_traceState_352_ = lean_ctor_get(v___x_346_, 4);
v_messages_353_ = lean_ctor_get(v___x_346_, 6);
v_infoState_354_ = lean_ctor_get(v___x_346_, 7);
v_snapshotTasks_355_ = lean_ctor_get(v___x_346_, 8);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_371_ == 0)
{
lean_object* v_unused_372_; 
v_unused_372_ = lean_ctor_get(v___x_346_, 5);
lean_dec(v_unused_372_);
v___x_357_ = v___x_346_;
v_isShared_358_ = v_isSharedCheck_371_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_snapshotTasks_355_);
lean_inc(v_infoState_354_);
lean_inc(v_messages_353_);
lean_inc(v_traceState_352_);
lean_inc(v_auxDeclNGen_351_);
lean_inc(v_ngen_350_);
lean_inc(v_nextMacroScope_349_);
lean_inc(v_env_348_);
lean_dec(v___x_346_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_371_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v_asyncMode_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_364_; 
v_asyncMode_359_ = lean_ctor_get(v_toEnvExtension_347_, 2);
lean_inc(v_asyncMode_359_);
v___x_360_ = lean_box(0);
v___x_361_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_331_, v_env_348_, v_decl_333_, v_asyncMode_359_, v___x_360_);
lean_dec(v_asyncMode_359_);
v___x_362_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___lam__7___closed__2, &l_Lake_registerOrderedTagAttribute___lam__7___closed__2_once, _init_l_Lake_registerOrderedTagAttribute___lam__7___closed__2);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 5, v___x_362_);
lean_ctor_set(v___x_357_, 0, v___x_361_);
v___x_364_ = v___x_357_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_361_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_nextMacroScope_349_);
lean_ctor_set(v_reuseFailAlloc_370_, 2, v_ngen_350_);
lean_ctor_set(v_reuseFailAlloc_370_, 3, v_auxDeclNGen_351_);
lean_ctor_set(v_reuseFailAlloc_370_, 4, v_traceState_352_);
lean_ctor_set(v_reuseFailAlloc_370_, 5, v___x_362_);
lean_ctor_set(v_reuseFailAlloc_370_, 6, v_messages_353_);
lean_ctor_set(v_reuseFailAlloc_370_, 7, v_infoState_354_);
lean_ctor_set(v_reuseFailAlloc_370_, 8, v_snapshotTasks_355_);
v___x_364_ = v_reuseFailAlloc_370_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_368_; 
v___x_365_ = lean_st_ref_put(v___y_341_, v___x_364_);
v___x_366_ = lean_box(0);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 0, v___x_366_);
v___x_368_ = v___x_344_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_366_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
}
else
{
lean_dec(v_decl_333_);
lean_dec_ref(v_a_331_);
return v___x_342_;
}
}
v___jp_375_:
{
lean_object* v___x_378_; lean_object* v_env_379_; lean_object* v___x_380_; 
v___x_378_ = lean_st_ref_get(v___y_377_);
v_env_379_ = lean_ctor_get(v___x_378_, 0);
lean_inc_ref(v_env_379_);
lean_dec(v___x_378_);
v___x_380_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_379_, v_decl_333_);
lean_dec_ref(v_env_379_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_dec(v_name_332_);
v___y_340_ = v___y_376_;
v___y_341_ = v___y_377_;
goto v___jp_339_;
}
else
{
lean_object* v___x_381_; 
lean_dec_ref_known(v___x_380_, 1);
lean_dec_ref(v_a_331_);
lean_dec_ref(v_validate_330_);
v___x_381_ = l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg(v_name_332_, v_decl_333_, v___y_376_, v___y_377_);
return v___x_381_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__7___boxed(lean_object* v_validate_386_, lean_object* v_a_387_, lean_object* v_name_388_, lean_object* v_decl_389_, lean_object* v_stx_390_, lean_object* v_kind_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
uint8_t v_kind_boxed_395_; lean_object* v_res_396_; 
v_kind_boxed_395_ = lean_unbox(v_kind_391_);
v_res_396_ = l_Lake_registerOrderedTagAttribute___lam__7(v_validate_386_, v_a_387_, v_name_388_, v_decl_389_, v_stx_390_, v_kind_boxed_395_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute(lean_object* v_name_407_, lean_object* v_descr_408_, lean_object* v_validate_409_, lean_object* v_ref_410_){
_start:
{
lean_object* v___f_412_; lean_object* v___f_413_; lean_object* v___f_414_; lean_object* v___f_415_; lean_object* v___f_416_; lean_object* v___f_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___f_412_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___closed__0));
v___f_413_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___closed__1));
v___f_414_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___closed__2));
v___f_415_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___closed__3));
v___f_416_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___closed__5));
v___f_417_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___closed__6));
v___x_418_ = lean_box(2);
v___x_419_ = lean_box(0);
lean_inc(v_ref_410_);
v___x_420_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_420_, 0, v_ref_410_);
lean_ctor_set(v___x_420_, 1, v___f_417_);
lean_ctor_set(v___x_420_, 2, v___f_416_);
lean_ctor_set(v___x_420_, 3, v___f_415_);
lean_ctor_set(v___x_420_, 4, v___f_414_);
lean_ctor_set(v___x_420_, 5, v___f_413_);
lean_ctor_set(v___x_420_, 6, v___x_418_);
lean_ctor_set(v___x_420_, 7, v___x_419_);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
lean_ctor_set(v___x_421_, 1, v___f_412_);
v___x_422_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_421_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_a_423_; lean_object* v___f_424_; lean_object* v___f_425_; uint8_t v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v_a_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc_n(v_a_423_, 2);
lean_dec_ref_known(v___x_422_, 1);
lean_inc_n(v_name_407_, 2);
v___f_424_ = lean_alloc_closure((void*)(l_Lake_registerOrderedTagAttribute___lam__6___boxed), 5, 1);
lean_closure_set(v___f_424_, 0, v_name_407_);
v___f_425_ = lean_alloc_closure((void*)(l_Lake_registerOrderedTagAttribute___lam__7___boxed), 9, 3);
lean_closure_set(v___f_425_, 0, v_validate_409_);
lean_closure_set(v___f_425_, 1, v_a_423_);
lean_closure_set(v___f_425_, 2, v_name_407_);
v___x_426_ = 0;
v___x_427_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_427_, 0, v_ref_410_);
lean_ctor_set(v___x_427_, 1, v_name_407_);
lean_ctor_set(v___x_427_, 2, v_descr_408_);
lean_ctor_set_uint8(v___x_427_, sizeof(void*)*3, v___x_426_);
v___x_428_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v___f_425_);
lean_ctor_set(v___x_428_, 2, v___f_424_);
lean_inc_ref(v___x_428_);
v___x_429_ = l_Lean_registerBuiltinAttribute(v___x_428_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_437_; 
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_437_ == 0)
{
lean_object* v_unused_438_; 
v_unused_438_ = lean_ctor_get(v___x_429_, 0);
lean_dec(v_unused_438_);
v___x_431_ = v___x_429_;
v_isShared_432_ = v_isSharedCheck_437_;
goto v_resetjp_430_;
}
else
{
lean_dec(v___x_429_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_437_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_433_; lean_object* v___x_435_; 
v___x_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_428_);
lean_ctor_set(v___x_433_, 1, v_a_423_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 0, v___x_433_);
v___x_435_ = v___x_431_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_433_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
else
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
lean_dec_ref_known(v___x_428_, 3);
lean_dec(v_a_423_);
v_a_439_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_446_ == 0)
{
v___x_441_ = v___x_429_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_429_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_a_439_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
else
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
lean_dec(v_ref_410_);
lean_dec_ref(v_validate_409_);
lean_dec_ref(v_descr_408_);
lean_dec(v_name_407_);
v_a_447_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_422_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_422_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___boxed(lean_object* v_name_455_, lean_object* v_descr_456_, lean_object* v_validate_457_, lean_object* v_ref_458_, lean_object* v_a_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lake_registerOrderedTagAttribute(v_name_455_, v_descr_456_, v_validate_457_, v_ref_458_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0(lean_object* v_00_u03b1_461_, lean_object* v_msg_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg(v_msg_462_, v___y_463_, v___y_464_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___boxed(lean_object* v_00_u03b1_467_, lean_object* v_msg_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0(v_00_u03b1_467_, v_msg_468_, v___y_469_, v___y_470_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1(lean_object* v_00_u03b1_473_, lean_object* v_attrName_474_, lean_object* v_declName_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg(v_attrName_474_, v_declName_475_, v___y_476_, v___y_477_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___boxed(lean_object* v_00_u03b1_480_, lean_object* v_attrName_481_, lean_object* v_declName_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1(v_00_u03b1_480_, v_attrName_481_, v_declName_482_, v___y_483_, v___y_484_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2(lean_object* v_00_u03b1_487_, lean_object* v_name_488_, uint8_t v_kind_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg(v_name_488_, v_kind_489_, v___y_490_, v___y_491_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___boxed(lean_object* v_00_u03b1_494_, lean_object* v_name_495_, lean_object* v_kind_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
uint8_t v_kind_boxed_500_; lean_object* v_res_501_; 
v_kind_boxed_500_ = lean_unbox(v_kind_496_);
v_res_501_ = l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2(v_00_u03b1_494_, v_name_495_, v_kind_boxed_500_, v___y_497_, v___y_498_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
return v_res_501_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0_spec__0(lean_object* v_a_502_, lean_object* v_as_503_, size_t v_i_504_, size_t v_stop_505_){
_start:
{
uint8_t v___x_506_; 
v___x_506_ = lean_usize_dec_eq(v_i_504_, v_stop_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_507_ = lean_array_uget_borrowed(v_as_503_, v_i_504_);
v___x_508_ = lean_name_eq(v_a_502_, v___x_507_);
if (v___x_508_ == 0)
{
size_t v___x_509_; size_t v___x_510_; 
v___x_509_ = ((size_t)1ULL);
v___x_510_ = lean_usize_add(v_i_504_, v___x_509_);
v_i_504_ = v___x_510_;
goto _start;
}
else
{
return v___x_508_;
}
}
else
{
uint8_t v___x_512_; 
v___x_512_ = 0;
return v___x_512_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0_spec__0___boxed(lean_object* v_a_513_, lean_object* v_as_514_, lean_object* v_i_515_, lean_object* v_stop_516_){
_start:
{
size_t v_i_boxed_517_; size_t v_stop_boxed_518_; uint8_t v_res_519_; lean_object* v_r_520_; 
v_i_boxed_517_ = lean_unbox_usize(v_i_515_);
lean_dec(v_i_515_);
v_stop_boxed_518_ = lean_unbox_usize(v_stop_516_);
lean_dec(v_stop_516_);
v_res_519_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0_spec__0(v_a_513_, v_as_514_, v_i_boxed_517_, v_stop_boxed_518_);
lean_dec_ref(v_as_514_);
lean_dec(v_a_513_);
v_r_520_ = lean_box(v_res_519_);
return v_r_520_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0(lean_object* v_as_521_, lean_object* v_a_522_){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_523_ = lean_unsigned_to_nat(0u);
v___x_524_ = lean_array_get_size(v_as_521_);
v___x_525_ = lean_nat_dec_lt(v___x_523_, v___x_524_);
if (v___x_525_ == 0)
{
return v___x_525_;
}
else
{
if (v___x_525_ == 0)
{
return v___x_525_;
}
else
{
size_t v___x_526_; size_t v___x_527_; uint8_t v___x_528_; 
v___x_526_ = ((size_t)0ULL);
v___x_527_ = lean_usize_of_nat(v___x_524_);
v___x_528_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0_spec__0(v_a_522_, v_as_521_, v___x_526_, v___x_527_);
return v___x_528_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0___boxed(lean_object* v_as_529_, lean_object* v_a_530_){
_start:
{
uint8_t v_res_531_; lean_object* v_r_532_; 
v_res_531_ = l_Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0(v_as_529_, v_a_530_);
lean_dec(v_a_530_);
lean_dec_ref(v_as_529_);
v_r_532_ = lean_box(v_res_531_);
return v_r_532_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___redArg(lean_object* v___y_533_, lean_object* v_as_534_, lean_object* v_k_535_, lean_object* v_x_536_, lean_object* v_x_537_){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v_m_540_; lean_object* v_a_541_; uint8_t v___x_542_; 
v___x_538_ = lean_nat_add(v_x_536_, v_x_537_);
v___x_539_ = lean_unsigned_to_nat(1u);
v_m_540_ = lean_nat_shiftr(v___x_538_, v___x_539_);
lean_dec(v___x_538_);
v_a_541_ = lean_array_fget_borrowed(v_as_534_, v_m_540_);
v___x_542_ = l_Lean_Name_quickLt(v_a_541_, v_k_535_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; uint8_t v___x_544_; 
lean_dec(v_x_537_);
v___x_543_ = lean_unsigned_to_nat(0u);
v___x_544_ = l_Lean_Name_quickLt(v_k_535_, v_a_541_);
if (v___x_544_ == 0)
{
uint8_t v___x_545_; 
lean_dec(v_m_540_);
lean_dec(v_x_536_);
v___x_545_ = lean_nat_dec_le(v___x_543_, v___y_533_);
return v___x_545_;
}
else
{
uint8_t v___x_546_; lean_object* v___x_547_; uint8_t v___y_549_; 
v___x_546_ = lean_nat_dec_eq(v_m_540_, v___x_543_);
v___x_547_ = lean_nat_sub(v_m_540_, v___x_539_);
lean_dec(v_m_540_);
if (v___x_546_ == 0)
{
uint8_t v___x_551_; 
v___x_551_ = lean_nat_dec_lt(v___x_547_, v_x_536_);
v___y_549_ = v___x_551_;
goto v___jp_548_;
}
else
{
v___y_549_ = v___x_546_;
goto v___jp_548_;
}
v___jp_548_:
{
if (v___y_549_ == 0)
{
v_x_537_ = v___x_547_;
goto _start;
}
else
{
lean_dec(v___x_547_);
lean_dec(v_x_536_);
return v___x_542_;
}
}
}
}
else
{
lean_object* v___x_552_; uint8_t v___x_553_; 
lean_dec(v_x_536_);
v___x_552_ = lean_nat_add(v_m_540_, v___x_539_);
lean_dec(v_m_540_);
v___x_553_ = lean_nat_dec_le(v___x_552_, v_x_537_);
if (v___x_553_ == 0)
{
lean_dec(v___x_552_);
lean_dec(v_x_537_);
return v___x_553_;
}
else
{
v_x_536_ = v___x_552_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___redArg___boxed(lean_object* v___y_555_, lean_object* v_as_556_, lean_object* v_k_557_, lean_object* v_x_558_, lean_object* v_x_559_){
_start:
{
uint8_t v_res_560_; lean_object* v_r_561_; 
v_res_560_ = l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___redArg(v___y_555_, v_as_556_, v_k_557_, v_x_558_, v_x_559_);
lean_dec(v_k_557_);
lean_dec_ref(v_as_556_);
lean_dec(v___y_555_);
v_r_561_ = lean_box(v_res_560_);
return v_r_561_;
}
}
static lean_object* _init_l_Lake_OrderedTagAttribute_hasTag___closed__0(void){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Array_instInhabited(lean_box(0));
return v___x_562_;
}
}
LEAN_EXPORT uint8_t l_Lake_OrderedTagAttribute_hasTag(lean_object* v_attr_563_, lean_object* v_env_564_, lean_object* v_decl_565_){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = lean_obj_once(&l_Lake_OrderedTagAttribute_hasTag___closed__0, &l_Lake_OrderedTagAttribute_hasTag___closed__0_once, _init_l_Lake_OrderedTagAttribute_hasTag___closed__0);
v___x_567_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_564_, v_decl_565_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_ext_568_; lean_object* v_toEnvExtension_569_; lean_object* v_asyncMode_570_; lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v_ext_568_ = lean_ctor_get(v_attr_563_, 1);
v_toEnvExtension_569_ = lean_ctor_get(v_ext_568_, 0);
v_asyncMode_570_ = lean_ctor_get(v_toEnvExtension_569_, 2);
v___x_571_ = lean_box(0);
v___x_572_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_566_, v_ext_568_, v_env_564_, v_asyncMode_570_, v___x_571_);
v___x_573_ = l_Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0(v___x_572_, v_decl_565_);
lean_dec(v___x_572_);
return v___x_573_;
}
else
{
lean_object* v_val_574_; lean_object* v_ext_575_; uint8_t v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; uint8_t v___x_580_; 
v_val_574_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_val_574_);
lean_dec_ref_known(v___x_567_, 1);
v_ext_575_ = lean_ctor_get(v_attr_563_, 1);
v___x_576_ = 0;
v___x_577_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_566_, v_ext_575_, v_env_564_, v_val_574_, v___x_576_);
lean_dec(v_val_574_);
lean_dec_ref(v_env_564_);
v___x_578_ = lean_unsigned_to_nat(0u);
v___x_579_ = lean_array_get_size(v___x_577_);
v___x_580_ = lean_nat_dec_lt(v___x_578_, v___x_579_);
if (v___x_580_ == 0)
{
lean_dec_ref(v___x_577_);
return v___x_580_;
}
else
{
lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_581_ = lean_unsigned_to_nat(1u);
v___x_582_ = lean_nat_sub(v___x_579_, v___x_581_);
v___x_583_ = lean_nat_dec_le(v___x_578_, v___x_582_);
if (v___x_583_ == 0)
{
lean_dec(v___x_582_);
lean_dec_ref(v___x_577_);
return v___x_583_;
}
else
{
uint8_t v___x_584_; 
lean_inc(v___x_582_);
v___x_584_ = l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___redArg(v___x_582_, v___x_577_, v_decl_565_, v___x_578_, v___x_582_);
lean_dec_ref(v___x_577_);
lean_dec(v___x_582_);
return v___x_584_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrderedTagAttribute_hasTag___boxed(lean_object* v_attr_585_, lean_object* v_env_586_, lean_object* v_decl_587_){
_start:
{
uint8_t v_res_588_; lean_object* v_r_589_; 
v_res_588_ = l_Lake_OrderedTagAttribute_hasTag(v_attr_585_, v_env_586_, v_decl_587_);
lean_dec(v_decl_587_);
lean_dec_ref(v_attr_585_);
v_r_589_ = lean_box(v_res_588_);
return v_r_589_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1(lean_object* v___y_590_, lean_object* v_as_591_, lean_object* v_k_592_, lean_object* v_x_593_, lean_object* v_x_594_, lean_object* v_x_595_){
_start:
{
uint8_t v___x_596_; 
v___x_596_ = l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___redArg(v___y_590_, v_as_591_, v_k_592_, v_x_593_, v_x_594_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___boxed(lean_object* v___y_597_, lean_object* v_as_598_, lean_object* v_k_599_, lean_object* v_x_600_, lean_object* v_x_601_, lean_object* v_x_602_){
_start:
{
uint8_t v_res_603_; lean_object* v_r_604_; 
v_res_603_ = l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1(v___y_597_, v_as_598_, v_k_599_, v_x_600_, v_x_601_, v_x_602_);
lean_dec(v_k_599_);
lean_dec_ref(v_as_598_);
lean_dec(v___y_597_);
v_r_604_ = lean_box(v_res_603_);
return v_r_604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrderedTagAttribute_getAllEntries_spec__0(lean_object* v_as_605_, size_t v_i_606_, size_t v_stop_607_, lean_object* v_b_608_){
_start:
{
uint8_t v___x_609_; 
v___x_609_ = lean_usize_dec_eq(v_i_606_, v_stop_607_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; lean_object* v___x_611_; size_t v___x_612_; size_t v___x_613_; 
v___x_610_ = lean_array_uget_borrowed(v_as_605_, v_i_606_);
v___x_611_ = l_Array_append___redArg(v_b_608_, v___x_610_);
v___x_612_ = ((size_t)1ULL);
v___x_613_ = lean_usize_add(v_i_606_, v___x_612_);
v_i_606_ = v___x_613_;
v_b_608_ = v___x_611_;
goto _start;
}
else
{
return v_b_608_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrderedTagAttribute_getAllEntries_spec__0___boxed(lean_object* v_as_615_, lean_object* v_i_616_, lean_object* v_stop_617_, lean_object* v_b_618_){
_start:
{
size_t v_i_boxed_619_; size_t v_stop_boxed_620_; lean_object* v_res_621_; 
v_i_boxed_619_ = lean_unbox_usize(v_i_616_);
lean_dec(v_i_616_);
v_stop_boxed_620_ = lean_unbox_usize(v_stop_617_);
lean_dec(v_stop_617_);
v_res_621_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrderedTagAttribute_getAllEntries_spec__0(v_as_615_, v_i_boxed_619_, v_stop_boxed_620_, v_b_618_);
lean_dec_ref(v_as_615_);
return v_res_621_;
}
}
static lean_object* _init_l_Lake_OrderedTagAttribute_getAllEntries___closed__0(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = lean_obj_once(&l_Lake_OrderedTagAttribute_hasTag___closed__0, &l_Lake_OrderedTagAttribute_hasTag___closed__0_once, _init_l_Lake_OrderedTagAttribute_hasTag___closed__0);
v___x_623_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrderedTagAttribute_getAllEntries(lean_object* v_attr_624_, lean_object* v_env_625_){
_start:
{
lean_object* v_ext_626_; lean_object* v_toEnvExtension_627_; lean_object* v_asyncMode_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v_s_631_; lean_object* v___y_633_; lean_object* v_importedEntries_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v_ext_626_ = lean_ctor_get(v_attr_624_, 1);
v_toEnvExtension_627_ = lean_ctor_get(v_ext_626_, 0);
v_asyncMode_628_ = lean_ctor_get(v_toEnvExtension_627_, 2);
v___x_629_ = lean_obj_once(&l_Lake_OrderedTagAttribute_getAllEntries___closed__0, &l_Lake_OrderedTagAttribute_getAllEntries___closed__0_once, _init_l_Lake_OrderedTagAttribute_getAllEntries___closed__0);
v___x_630_ = lean_box(0);
v_s_631_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_629_, v_toEnvExtension_627_, v_env_625_, v_asyncMode_628_, v___x_630_);
v_importedEntries_636_ = lean_ctor_get(v_s_631_, 0);
lean_inc_ref(v_importedEntries_636_);
v___x_637_ = lean_unsigned_to_nat(0u);
v___x_638_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___closed__4));
v___x_639_ = lean_array_get_size(v_importedEntries_636_);
v___x_640_ = lean_nat_dec_lt(v___x_637_, v___x_639_);
if (v___x_640_ == 0)
{
lean_dec_ref(v_importedEntries_636_);
v___y_633_ = v___x_638_;
goto v___jp_632_;
}
else
{
size_t v___x_641_; size_t v___x_642_; lean_object* v___x_643_; 
v___x_641_ = ((size_t)0ULL);
v___x_642_ = lean_usize_of_nat(v___x_639_);
v___x_643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrderedTagAttribute_getAllEntries_spec__0(v_importedEntries_636_, v___x_641_, v___x_642_, v___x_638_);
lean_dec_ref(v_importedEntries_636_);
v___y_633_ = v___x_643_;
goto v___jp_632_;
}
v___jp_632_:
{
lean_object* v_state_634_; lean_object* v___x_635_; 
v_state_634_ = lean_ctor_get(v_s_631_, 1);
lean_inc(v_state_634_);
lean_dec(v_s_631_);
v___x_635_ = l_Array_append___redArg(v___y_633_, v_state_634_);
lean_dec(v_state_634_);
return v___x_635_;
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
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_OrderedTagAttribute(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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

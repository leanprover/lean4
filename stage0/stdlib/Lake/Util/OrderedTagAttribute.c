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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_instInhabitedEnvExtension_default___redArg();
lean_object* l_Array_instInhabited___redArg();
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
extern lean_object* l_Lean_instInhabitedAttributeImpl_default;
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___redArg(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
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
static const lean_string_object l_Lake_registerOrderedTagAttribute___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l_Lake_registerOrderedTagAttribute___lam__4___closed__0 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___lam__4___closed__0_value;
static lean_once_cell_t l_Lake_registerOrderedTagAttribute___lam__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_registerOrderedTagAttribute___lam__4___closed__1;
static const lean_string_object l_Lake_registerOrderedTagAttribute___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l_Lake_registerOrderedTagAttribute___lam__4___closed__2 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___lam__4___closed__2_value;
static lean_once_cell_t l_Lake_registerOrderedTagAttribute___lam__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_registerOrderedTagAttribute___lam__4___closed__3;
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__6(lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__7(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lake_registerOrderedTagAttribute___lam__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_registerOrderedTagAttribute___lam__8___closed__0;
static lean_once_cell_t l_Lake_registerOrderedTagAttribute___lam__8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_registerOrderedTagAttribute___lam__8___closed__1;
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lake_registerOrderedTagAttribute___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_registerOrderedTagAttribute___lam__5___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lake_registerOrderedTagAttribute___closed__4_value)} };
static const lean_object* l_Lake_registerOrderedTagAttribute___closed__5 = (const lean_object*)&l_Lake_registerOrderedTagAttribute___closed__5_value;
static const lean_closure_object l_Lake_registerOrderedTagAttribute___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_registerOrderedTagAttribute___lam__6___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lake_registerOrderedTagAttribute___closed__4_value)} };
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
v___x_36_ = l_Lean_instInhabitedEnvExtension_default___redArg();
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
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_158_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__0);
v___x_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1);
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
lean_ctor_set(v___x_163_, 2, v___x_162_);
lean_ctor_set(v___x_163_, 3, v___x_162_);
lean_ctor_set(v___x_163_, 4, v___x_161_);
lean_ctor_set(v___x_163_, 5, v___x_161_);
lean_ctor_set(v___x_163_, 6, v___x_161_);
lean_ctor_set(v___x_163_, 7, v___x_161_);
lean_ctor_set(v___x_163_, 8, v___x_161_);
lean_ctor_set(v___x_163_, 9, v___x_161_);
lean_ctor_set(v___x_163_, 10, v___x_161_);
return v___x_163_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_164_ = lean_unsigned_to_nat(32u);
v___x_165_ = lean_mk_empty_array_with_capacity(v___x_164_);
v___x_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_167_ = ((size_t)5ULL);
v___x_168_ = lean_unsigned_to_nat(0u);
v___x_169_ = lean_unsigned_to_nat(32u);
v___x_170_ = lean_mk_empty_array_with_capacity(v___x_169_);
v___x_171_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__3);
v___x_172_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_172_, 0, v___x_171_);
lean_ctor_set(v___x_172_, 1, v___x_170_);
lean_ctor_set(v___x_172_, 2, v___x_168_);
lean_ctor_set(v___x_172_, 3, v___x_168_);
lean_ctor_set_usize(v___x_172_, 4, v___x_167_);
return v___x_172_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_173_ = lean_box(1);
v___x_174_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__4);
v___x_175_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1);
v___x_176_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v___x_174_);
lean_ctor_set(v___x_176_, 2, v___x_173_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0(lean_object* v_msgData_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v___x_181_; lean_object* v_toCold_182_; lean_object* v_env_183_; lean_object* v_options_184_; uint8_t v___x_185_; lean_object* v_env_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_181_ = lean_st_ref_get(v___y_179_);
v_toCold_182_ = lean_ctor_get(v___y_178_, 0);
v_env_183_ = lean_ctor_get(v___x_181_, 0);
lean_inc_ref(v_env_183_);
lean_dec(v___x_181_);
v_options_184_ = lean_ctor_get(v_toCold_182_, 2);
v___x_185_ = 0;
v_env_186_ = l_Lean_Environment_setRecordingDeps(v_env_183_, v___x_185_);
v___x_187_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__2);
v___x_188_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_184_);
v___x_189_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_189_, 0, v_env_186_);
lean_ctor_set(v___x_189_, 1, v___x_187_);
lean_ctor_set(v___x_189_, 2, v___x_188_);
lean_ctor_set(v___x_189_, 3, v_options_184_);
v___x_190_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set(v___x_190_, 1, v_msgData_177_);
v___x_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___boxed(lean_object* v_msgData_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0(v_msgData_192_, v___y_193_, v___y_194_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg(lean_object* v_msg_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_ref_201_; lean_object* v___x_202_; lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_211_; 
v_ref_201_ = lean_ctor_get(v___y_198_, 2);
v___x_202_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0(v_msg_197_, v___y_198_, v___y_199_);
v_a_203_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_211_ == 0)
{
v___x_205_ = v___x_202_;
v_isShared_206_ = v_isSharedCheck_211_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_202_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_211_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_207_; lean_object* v___x_209_; 
lean_inc(v_ref_201_);
v___x_207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_207_, 0, v_ref_201_);
lean_ctor_set(v___x_207_, 1, v_a_203_);
if (v_isShared_206_ == 0)
{
lean_ctor_set_tag(v___x_205_, 1);
lean_ctor_set(v___x_205_, 0, v___x_207_);
v___x_209_ = v___x_205_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_207_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg___boxed(lean_object* v_msg_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg(v_msg_212_, v___y_213_, v___y_214_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
return v_res_216_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___lam__4___closed__1(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___lam__4___closed__0));
v___x_219_ = l_Lean_stringToMessageData(v___x_218_);
return v___x_219_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___lam__4___closed__3(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___lam__4___closed__2));
v___x_222_ = l_Lean_stringToMessageData(v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__4(lean_object* v_name_223_, lean_object* v_decl_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_228_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___lam__4___closed__1, &l_Lake_registerOrderedTagAttribute___lam__4___closed__1_once, _init_l_Lake_registerOrderedTagAttribute___lam__4___closed__1);
v___x_229_ = l_Lean_MessageData_ofName(v_name_223_);
v___x_230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_228_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___lam__4___closed__3, &l_Lake_registerOrderedTagAttribute___lam__4___closed__3_once, _init_l_Lake_registerOrderedTagAttribute___lam__4___closed__3);
v___x_232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_230_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
v___x_233_ = l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg(v___x_232_, v___y_225_, v___y_226_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__4___boxed(lean_object* v_name_234_, lean_object* v_decl_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lake_registerOrderedTagAttribute___lam__4(v_name_234_, v_decl_235_, v___y_236_, v___y_237_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
lean_dec(v_decl_235_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__5(lean_object* v___x_240_, lean_object* v_x_241_, lean_object* v_x_242_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_244_, 0, v___x_240_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__5___boxed(lean_object* v___x_245_, lean_object* v_x_246_, lean_object* v_x_247_, lean_object* v___y_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lake_registerOrderedTagAttribute___lam__5(v___x_245_, v_x_246_, v_x_247_);
lean_dec_ref(v_x_247_);
lean_dec_ref(v_x_246_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__6(lean_object* v___x_250_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_250_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__6___boxed(lean_object* v___x_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lake_registerOrderedTagAttribute___lam__6(v___x_253_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__7(lean_object* v_a_256_, lean_object* v_decl_257_, lean_object* v_s_258_){
_start:
{
lean_object* v_addEntryFn_259_; lean_object* v_importedEntries_260_; lean_object* v_state_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_269_; 
v_addEntryFn_259_ = lean_ctor_get(v_a_256_, 3);
lean_inc(v_addEntryFn_259_);
lean_dec_ref(v_a_256_);
v_importedEntries_260_ = lean_ctor_get(v_s_258_, 0);
v_state_261_ = lean_ctor_get(v_s_258_, 1);
v_isSharedCheck_269_ = !lean_is_exclusive(v_s_258_);
if (v_isSharedCheck_269_ == 0)
{
v___x_263_ = v_s_258_;
v_isShared_264_ = v_isSharedCheck_269_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_state_261_);
lean_inc(v_importedEntries_260_);
lean_dec(v_s_258_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_269_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v_state_265_; lean_object* v___x_267_; 
v_state_265_ = lean_apply_2(v_addEntryFn_259_, v_state_261_, v_decl_257_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 1, v_state_265_);
v___x_267_ = v___x_263_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_importedEntries_260_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v_state_265_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__0));
v___x_272_ = l_Lean_stringToMessageData(v___x_271_);
return v___x_272_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__2));
v___x_275_ = l_Lean_stringToMessageData(v___x_274_);
return v___x_275_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__4));
v___x_278_ = l_Lean_stringToMessageData(v___x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg(lean_object* v_name_282_, uint8_t v_kind_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___y_293_; 
v___x_287_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__1);
v___x_288_ = l_Lean_MessageData_ofName(v_name_282_);
v___x_289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_287_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
v___x_290_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__3);
v___x_291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_289_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
switch(v_kind_283_)
{
case 0:
{
lean_object* v___x_300_; 
v___x_300_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__6));
v___y_293_ = v___x_300_;
goto v___jp_292_;
}
case 1:
{
lean_object* v___x_301_; 
v___x_301_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__7));
v___y_293_ = v___x_301_;
goto v___jp_292_;
}
default: 
{
lean_object* v___x_302_; 
v___x_302_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__8));
v___y_293_ = v___x_302_;
goto v___jp_292_;
}
}
v___jp_292_:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
lean_inc_ref(v___y_293_);
v___x_294_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_294_, 0, v___y_293_);
v___x_295_ = l_Lean_MessageData_ofFormat(v___x_294_);
v___x_296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_291_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__5);
v___x_298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_296_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v___x_299_ = l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg(v___x_298_, v___y_284_, v___y_285_);
return v___x_299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___boxed(lean_object* v_name_303_, lean_object* v_kind_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
uint8_t v_kind_boxed_308_; lean_object* v_res_309_; 
v_kind_boxed_308_ = lean_unbox(v_kind_304_);
v_res_309_ = l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg(v_name_303_, v_kind_boxed_308_, v___y_305_, v___y_306_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
return v_res_309_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__0));
v___x_312_ = l_Lean_stringToMessageData(v___x_311_);
return v___x_312_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__2));
v___x_315_ = l_Lean_stringToMessageData(v___x_314_);
return v___x_315_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__4));
v___x_318_ = l_Lean_stringToMessageData(v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg(lean_object* v_attrName_319_, lean_object* v_declName_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; uint8_t v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_324_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__1);
v___x_325_ = l_Lean_MessageData_ofName(v_attrName_319_);
v___x_326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_324_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
v___x_327_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__3);
v___x_328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_326_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = 0;
v___x_330_ = l_Lean_MessageData_ofConstName(v_declName_320_, v___x_329_);
v___x_331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_328_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
v___x_332_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__5);
v___x_333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_331_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
v___x_334_ = l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg(v___x_333_, v___y_321_, v___y_322_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___boxed(lean_object* v_attrName_335_, lean_object* v_declName_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg(v_attrName_335_, v_declName_336_, v___y_337_, v___y_338_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
return v_res_340_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___lam__8___closed__0(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__0);
v___x_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
return v___x_342_;
}
}
static lean_object* _init_l_Lake_registerOrderedTagAttribute___lam__8___closed__1(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___lam__8___closed__0, &l_Lake_registerOrderedTagAttribute___lam__8___closed__0_once, _init_l_Lake_registerOrderedTagAttribute___lam__8___closed__0);
v___x_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__8(lean_object* v_a_345_, lean_object* v_validate_346_, lean_object* v_name_347_, lean_object* v_decl_348_, lean_object* v_stx_349_, uint8_t v_kind_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v___y_355_; lean_object* v_nextMacroScope_356_; lean_object* v_ngen_357_; lean_object* v_auxDeclNGen_358_; lean_object* v_traceState_359_; lean_object* v_recordedDeps_360_; lean_object* v_messages_361_; lean_object* v_infoState_362_; lean_object* v_snapshotTasks_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___f_370_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___x_399_; 
lean_inc(v_decl_348_);
lean_inc_ref(v_a_345_);
v___f_370_ = lean_alloc_closure((void*)(l_Lake_registerOrderedTagAttribute___lam__7), 3, 2);
lean_closure_set(v___f_370_, 0, v_a_345_);
lean_closure_set(v___f_370_, 1, v_decl_348_);
v___x_399_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_349_, v___y_351_, v___y_352_);
if (lean_obj_tag(v___x_399_) == 0)
{
uint8_t v___x_400_; uint8_t v___x_401_; 
lean_dec_ref_known(v___x_399_, 1);
v___x_400_ = 0;
v___x_401_ = l_Lean_instBEqAttributeKind_beq(v_kind_350_, v___x_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; 
lean_dec_ref(v___f_370_);
lean_dec(v_decl_348_);
lean_dec_ref(v_validate_346_);
lean_dec_ref(v_a_345_);
v___x_402_ = l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg(v_name_347_, v_kind_350_, v___y_351_, v___y_352_);
return v___x_402_;
}
else
{
goto v___jp_394_;
}
}
else
{
lean_dec_ref(v___f_370_);
lean_dec(v_decl_348_);
lean_dec(v_name_347_);
lean_dec_ref(v_validate_346_);
lean_dec_ref(v_a_345_);
return v___x_399_;
}
v___jp_354_:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_366_ = lean_obj_once(&l_Lake_registerOrderedTagAttribute___lam__8___closed__1, &l_Lake_registerOrderedTagAttribute___lam__8___closed__1_once, _init_l_Lake_registerOrderedTagAttribute___lam__8___closed__1);
v___x_367_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_367_, 0, v___y_365_);
lean_ctor_set(v___x_367_, 1, v_nextMacroScope_356_);
lean_ctor_set(v___x_367_, 2, v_ngen_357_);
lean_ctor_set(v___x_367_, 3, v_auxDeclNGen_358_);
lean_ctor_set(v___x_367_, 4, v_traceState_359_);
lean_ctor_set(v___x_367_, 5, v___x_366_);
lean_ctor_set(v___x_367_, 6, v_recordedDeps_360_);
lean_ctor_set(v___x_367_, 7, v_messages_361_);
lean_ctor_set(v___x_367_, 8, v_infoState_362_);
lean_ctor_set(v___x_367_, 9, v_snapshotTasks_363_);
v___x_368_ = lean_st_ref_put(v___y_364_, v___x_367_);
v___x_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_369_, 0, v___y_355_);
return v___x_369_;
}
v___jp_371_:
{
lean_object* v___x_374_; 
lean_inc(v___y_373_);
lean_inc_ref(v___y_372_);
v___x_374_ = lean_apply_4(v_validate_346_, v_decl_348_, v___y_372_, v___y_373_, lean_box(0));
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v___x_375_; lean_object* v_toEnvExtension_376_; lean_object* v_env_377_; lean_object* v_nextMacroScope_378_; lean_object* v_ngen_379_; lean_object* v_auxDeclNGen_380_; lean_object* v_traceState_381_; lean_object* v_recordedDeps_382_; lean_object* v_messages_383_; lean_object* v_infoState_384_; lean_object* v_snapshotTasks_385_; lean_object* v_asyncMode_386_; uint8_t v_logWrites_387_; lean_object* v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
lean_dec_ref_known(v___x_374_, 1);
v___x_375_ = lean_st_ref_take(v___y_373_);
v_toEnvExtension_376_ = lean_ctor_get(v_a_345_, 0);
lean_inc_ref(v_toEnvExtension_376_);
lean_dec_ref(v_a_345_);
v_env_377_ = lean_ctor_get(v___x_375_, 0);
lean_inc_ref(v_env_377_);
v_nextMacroScope_378_ = lean_ctor_get(v___x_375_, 1);
lean_inc(v_nextMacroScope_378_);
v_ngen_379_ = lean_ctor_get(v___x_375_, 2);
lean_inc_ref(v_ngen_379_);
v_auxDeclNGen_380_ = lean_ctor_get(v___x_375_, 3);
lean_inc_ref(v_auxDeclNGen_380_);
v_traceState_381_ = lean_ctor_get(v___x_375_, 4);
lean_inc_ref(v_traceState_381_);
v_recordedDeps_382_ = lean_ctor_get(v___x_375_, 6);
lean_inc_ref(v_recordedDeps_382_);
v_messages_383_ = lean_ctor_get(v___x_375_, 7);
lean_inc_ref(v_messages_383_);
v_infoState_384_ = lean_ctor_get(v___x_375_, 8);
lean_inc_ref(v_infoState_384_);
v_snapshotTasks_385_ = lean_ctor_get(v___x_375_, 9);
lean_inc_ref(v_snapshotTasks_385_);
lean_dec(v___x_375_);
v_asyncMode_386_ = lean_ctor_get(v_toEnvExtension_376_, 2);
lean_inc(v_asyncMode_386_);
v_logWrites_387_ = lean_ctor_get_uint8(v_toEnvExtension_376_, sizeof(void*)*6);
v___x_388_ = lean_box(0);
v___x_389_ = lean_box(0);
v___x_390_ = 1;
if (v_logWrites_387_ == 0)
{
lean_object* v___x_391_; 
v___x_391_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_376_, v_env_377_, v___f_370_, v_asyncMode_386_, v___x_389_, v___x_390_);
lean_dec(v_asyncMode_386_);
v___y_355_ = v___x_388_;
v_nextMacroScope_356_ = v_nextMacroScope_378_;
v_ngen_357_ = v_ngen_379_;
v_auxDeclNGen_358_ = v_auxDeclNGen_380_;
v_traceState_359_ = v_traceState_381_;
v_recordedDeps_360_ = v_recordedDeps_382_;
v_messages_361_ = v_messages_383_;
v_infoState_362_ = v_infoState_384_;
v_snapshotTasks_363_ = v_snapshotTasks_385_;
v___y_364_ = v___y_373_;
v___y_365_ = v___x_391_;
goto v___jp_354_;
}
else
{
lean_object* v___x_392_; lean_object* v___x_393_; 
lean_inc_ref(v_toEnvExtension_376_);
v___x_392_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_376_, v_env_377_);
lean_dec_ref(v_env_377_);
v___x_393_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_376_, v___x_392_, v___f_370_, v_asyncMode_386_, v___x_389_, v___x_390_);
lean_dec(v_asyncMode_386_);
v___y_355_ = v___x_388_;
v_nextMacroScope_356_ = v_nextMacroScope_378_;
v_ngen_357_ = v_ngen_379_;
v_auxDeclNGen_358_ = v_auxDeclNGen_380_;
v_traceState_359_ = v_traceState_381_;
v_recordedDeps_360_ = v_recordedDeps_382_;
v_messages_361_ = v_messages_383_;
v_infoState_362_ = v_infoState_384_;
v_snapshotTasks_363_ = v_snapshotTasks_385_;
v___y_364_ = v___y_373_;
v___y_365_ = v___x_393_;
goto v___jp_354_;
}
}
else
{
lean_dec_ref(v___f_370_);
lean_dec_ref(v_a_345_);
return v___x_374_;
}
}
v___jp_394_:
{
lean_object* v___x_395_; lean_object* v_env_396_; lean_object* v___x_397_; 
v___x_395_ = lean_st_ref_get(v___y_352_);
v_env_396_ = lean_ctor_get(v___x_395_, 0);
lean_inc_ref(v_env_396_);
lean_dec(v___x_395_);
v___x_397_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_396_, v_decl_348_);
lean_dec_ref(v_env_396_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_dec(v_name_347_);
v___y_372_ = v___y_351_;
v___y_373_ = v___y_352_;
goto v___jp_371_;
}
else
{
lean_object* v___x_398_; 
lean_dec_ref_known(v___x_397_, 1);
lean_dec_ref(v___f_370_);
lean_dec_ref(v_validate_346_);
lean_dec_ref(v_a_345_);
v___x_398_ = l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg(v_name_347_, v_decl_348_, v___y_351_, v___y_352_);
return v___x_398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___lam__8___boxed(lean_object* v_a_403_, lean_object* v_validate_404_, lean_object* v_name_405_, lean_object* v_decl_406_, lean_object* v_stx_407_, lean_object* v_kind_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
uint8_t v_kind_boxed_412_; lean_object* v_res_413_; 
v_kind_boxed_412_ = lean_unbox(v_kind_408_);
v_res_413_ = l_Lake_registerOrderedTagAttribute___lam__8(v_a_403_, v_validate_404_, v_name_405_, v_decl_406_, v_stx_407_, v_kind_boxed_412_, v___y_409_, v___y_410_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute(lean_object* v_name_424_, lean_object* v_descr_425_, lean_object* v_validate_426_, lean_object* v_ref_427_){
_start:
{
lean_object* v___f_429_; lean_object* v___f_430_; lean_object* v___f_431_; lean_object* v___f_432_; lean_object* v___f_433_; lean_object* v___f_434_; lean_object* v___f_435_; lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___f_429_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___closed__0));
v___f_430_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___closed__1));
v___f_431_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___closed__2));
v___f_432_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___closed__3));
lean_inc(v_name_424_);
v___f_433_ = lean_alloc_closure((void*)(l_Lake_registerOrderedTagAttribute___lam__4___boxed), 5, 1);
lean_closure_set(v___f_433_, 0, v_name_424_);
v___f_434_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___closed__5));
v___f_435_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___closed__6));
v___x_436_ = lean_box(2);
v___x_437_ = lean_box(0);
v___x_438_ = 0;
lean_inc(v_ref_427_);
v___x_439_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_439_, 0, v_ref_427_);
lean_ctor_set(v___x_439_, 1, v___f_435_);
lean_ctor_set(v___x_439_, 2, v___f_434_);
lean_ctor_set(v___x_439_, 3, v___f_432_);
lean_ctor_set(v___x_439_, 4, v___f_431_);
lean_ctor_set(v___x_439_, 5, v___f_430_);
lean_ctor_set(v___x_439_, 6, v___x_436_);
lean_ctor_set(v___x_439_, 7, v___x_437_);
lean_ctor_set_uint8(v___x_439_, sizeof(void*)*8, v___x_438_);
lean_ctor_set_uint8(v___x_439_, sizeof(void*)*8 + 1, v___x_438_);
v___x_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
lean_ctor_set(v___x_440_, 1, v___f_429_);
v___x_441_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_440_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; lean_object* v___f_443_; uint8_t v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc_n(v_a_442_, 2);
lean_dec_ref_known(v___x_441_, 1);
lean_inc(v_name_424_);
v___f_443_ = lean_alloc_closure((void*)(l_Lake_registerOrderedTagAttribute___lam__8___boxed), 9, 3);
lean_closure_set(v___f_443_, 0, v_a_442_);
lean_closure_set(v___f_443_, 1, v_validate_426_);
lean_closure_set(v___f_443_, 2, v_name_424_);
v___x_444_ = 0;
v___x_445_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_445_, 0, v_ref_427_);
lean_ctor_set(v___x_445_, 1, v_name_424_);
lean_ctor_set(v___x_445_, 2, v_descr_425_);
lean_ctor_set_uint8(v___x_445_, sizeof(void*)*3, v___x_444_);
v___x_446_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
lean_ctor_set(v___x_446_, 1, v___f_443_);
lean_ctor_set(v___x_446_, 2, v___f_433_);
lean_inc_ref(v___x_446_);
v___x_447_ = l_Lean_registerBuiltinAttribute(v___x_446_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_455_; 
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_455_ == 0)
{
lean_object* v_unused_456_; 
v_unused_456_ = lean_ctor_get(v___x_447_, 0);
lean_dec(v_unused_456_);
v___x_449_ = v___x_447_;
v_isShared_450_ = v_isSharedCheck_455_;
goto v_resetjp_448_;
}
else
{
lean_dec(v___x_447_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_455_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; lean_object* v___x_453_; 
v___x_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_446_);
lean_ctor_set(v___x_451_, 1, v_a_442_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_451_);
v___x_453_ = v___x_449_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_451_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
else
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
lean_dec_ref_known(v___x_446_, 3);
lean_dec(v_a_442_);
v_a_457_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_447_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_447_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_dec_ref(v___f_433_);
lean_dec(v_ref_427_);
lean_dec_ref(v_validate_426_);
lean_dec_ref(v_descr_425_);
lean_dec(v_name_424_);
v_a_465_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_441_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_441_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_registerOrderedTagAttribute___boxed(lean_object* v_name_473_, lean_object* v_descr_474_, lean_object* v_validate_475_, lean_object* v_ref_476_, lean_object* v_a_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lake_registerOrderedTagAttribute(v_name_473_, v_descr_474_, v_validate_475_, v_ref_476_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0(lean_object* v_00_u03b1_479_, lean_object* v_msg_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg(v_msg_480_, v___y_481_, v___y_482_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___boxed(lean_object* v_00_u03b1_485_, lean_object* v_msg_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0(v_00_u03b1_485_, v_msg_486_, v___y_487_, v___y_488_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1(lean_object* v_00_u03b1_491_, lean_object* v_attrName_492_, lean_object* v_declName_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg(v_attrName_492_, v_declName_493_, v___y_494_, v___y_495_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___boxed(lean_object* v_00_u03b1_498_, lean_object* v_attrName_499_, lean_object* v_declName_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1(v_00_u03b1_498_, v_attrName_499_, v_declName_500_, v___y_501_, v___y_502_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2(lean_object* v_00_u03b1_505_, lean_object* v_name_506_, uint8_t v_kind_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg(v_name_506_, v_kind_507_, v___y_508_, v___y_509_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___boxed(lean_object* v_00_u03b1_512_, lean_object* v_name_513_, lean_object* v_kind_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
uint8_t v_kind_boxed_518_; lean_object* v_res_519_; 
v_kind_boxed_518_ = lean_unbox(v_kind_514_);
v_res_519_ = l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2(v_00_u03b1_512_, v_name_513_, v_kind_boxed_518_, v___y_515_, v___y_516_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
return v_res_519_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0_spec__0(lean_object* v_a_520_, lean_object* v_as_521_, size_t v_i_522_, size_t v_stop_523_){
_start:
{
uint8_t v___x_524_; 
v___x_524_ = lean_usize_dec_eq(v_i_522_, v_stop_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_525_ = lean_array_uget_borrowed(v_as_521_, v_i_522_);
v___x_526_ = lean_name_eq(v_a_520_, v___x_525_);
if (v___x_526_ == 0)
{
size_t v___x_527_; size_t v___x_528_; 
v___x_527_ = ((size_t)1ULL);
v___x_528_ = lean_usize_add(v_i_522_, v___x_527_);
v_i_522_ = v___x_528_;
goto _start;
}
else
{
return v___x_526_;
}
}
else
{
uint8_t v___x_530_; 
v___x_530_ = 0;
return v___x_530_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0_spec__0___boxed(lean_object* v_a_531_, lean_object* v_as_532_, lean_object* v_i_533_, lean_object* v_stop_534_){
_start:
{
size_t v_i_boxed_535_; size_t v_stop_boxed_536_; uint8_t v_res_537_; lean_object* v_r_538_; 
v_i_boxed_535_ = lean_unbox_usize(v_i_533_);
lean_dec(v_i_533_);
v_stop_boxed_536_ = lean_unbox_usize(v_stop_534_);
lean_dec(v_stop_534_);
v_res_537_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0_spec__0(v_a_531_, v_as_532_, v_i_boxed_535_, v_stop_boxed_536_);
lean_dec_ref(v_as_532_);
lean_dec(v_a_531_);
v_r_538_ = lean_box(v_res_537_);
return v_r_538_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0(lean_object* v_as_539_, lean_object* v_a_540_){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_541_ = lean_unsigned_to_nat(0u);
v___x_542_ = lean_array_get_size(v_as_539_);
v___x_543_ = lean_nat_dec_lt(v___x_541_, v___x_542_);
if (v___x_543_ == 0)
{
return v___x_543_;
}
else
{
if (v___x_543_ == 0)
{
return v___x_543_;
}
else
{
size_t v___x_544_; size_t v___x_545_; uint8_t v___x_546_; 
v___x_544_ = ((size_t)0ULL);
v___x_545_ = lean_usize_of_nat(v___x_542_);
v___x_546_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0_spec__0(v_a_540_, v_as_539_, v___x_544_, v___x_545_);
return v___x_546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0___boxed(lean_object* v_as_547_, lean_object* v_a_548_){
_start:
{
uint8_t v_res_549_; lean_object* v_r_550_; 
v_res_549_ = l_Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0(v_as_547_, v_a_548_);
lean_dec(v_a_548_);
lean_dec_ref(v_as_547_);
v_r_550_ = lean_box(v_res_549_);
return v_r_550_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___redArg(lean_object* v___y_551_, lean_object* v_as_552_, lean_object* v_k_553_, lean_object* v_x_554_, lean_object* v_x_555_){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v_m_558_; lean_object* v_a_559_; uint8_t v___x_560_; 
v___x_556_ = lean_nat_add(v_x_554_, v_x_555_);
v___x_557_ = lean_unsigned_to_nat(1u);
v_m_558_ = lean_nat_shiftr(v___x_556_, v___x_557_);
lean_dec(v___x_556_);
v_a_559_ = lean_array_fget_borrowed(v_as_552_, v_m_558_);
v___x_560_ = l_Lean_Name_quickLt(v_a_559_, v_k_553_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; uint8_t v___x_562_; 
lean_dec(v_x_555_);
v___x_561_ = lean_unsigned_to_nat(0u);
v___x_562_ = l_Lean_Name_quickLt(v_k_553_, v_a_559_);
if (v___x_562_ == 0)
{
uint8_t v___x_563_; 
lean_dec(v_m_558_);
lean_dec(v_x_554_);
v___x_563_ = lean_nat_dec_le(v___x_561_, v___y_551_);
return v___x_563_;
}
else
{
uint8_t v___x_564_; 
v___x_564_ = lean_nat_dec_eq(v_m_558_, v___x_561_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_565_ = lean_nat_sub(v_m_558_, v___x_557_);
lean_dec(v_m_558_);
v___x_566_ = lean_nat_dec_lt(v___x_565_, v_x_554_);
if (v___x_566_ == 0)
{
v_x_555_ = v___x_565_;
goto _start;
}
else
{
lean_dec(v___x_565_);
lean_dec(v_x_554_);
return v___x_564_;
}
}
else
{
lean_dec(v_m_558_);
lean_dec(v_x_554_);
return v___x_560_;
}
}
}
else
{
lean_object* v___x_568_; uint8_t v___x_569_; 
lean_dec(v_x_554_);
v___x_568_ = lean_nat_add(v_m_558_, v___x_557_);
lean_dec(v_m_558_);
v___x_569_ = lean_nat_dec_le(v___x_568_, v_x_555_);
if (v___x_569_ == 0)
{
lean_dec(v___x_568_);
lean_dec(v_x_555_);
return v___x_569_;
}
else
{
v_x_554_ = v___x_568_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___redArg___boxed(lean_object* v___y_571_, lean_object* v_as_572_, lean_object* v_k_573_, lean_object* v_x_574_, lean_object* v_x_575_){
_start:
{
uint8_t v_res_576_; lean_object* v_r_577_; 
v_res_576_ = l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___redArg(v___y_571_, v_as_572_, v_k_573_, v_x_574_, v_x_575_);
lean_dec(v_k_573_);
lean_dec_ref(v_as_572_);
lean_dec(v___y_571_);
v_r_577_ = lean_box(v_res_576_);
return v_r_577_;
}
}
static lean_object* _init_l_Lake_OrderedTagAttribute_hasTag___closed__0(void){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Array_instInhabited___redArg();
return v___x_578_;
}
}
LEAN_EXPORT uint8_t l_Lake_OrderedTagAttribute_hasTag(lean_object* v_attr_579_, lean_object* v_env_580_, lean_object* v_decl_581_){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = lean_obj_once(&l_Lake_OrderedTagAttribute_hasTag___closed__0, &l_Lake_OrderedTagAttribute_hasTag___closed__0_once, _init_l_Lake_OrderedTagAttribute_hasTag___closed__0);
v___x_583_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_580_, v_decl_581_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_ext_584_; lean_object* v_toEnvExtension_585_; lean_object* v_asyncMode_586_; lean_object* v___x_587_; uint8_t v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v_ext_584_ = lean_ctor_get(v_attr_579_, 1);
v_toEnvExtension_585_ = lean_ctor_get(v_ext_584_, 0);
v_asyncMode_586_ = lean_ctor_get(v_toEnvExtension_585_, 2);
v___x_587_ = lean_box(0);
v___x_588_ = 0;
v___x_589_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_582_, v_ext_584_, v_env_580_, v_asyncMode_586_, v___x_587_, v___x_588_);
v___x_590_ = l_Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0(v___x_589_, v_decl_581_);
lean_dec(v___x_589_);
return v___x_590_;
}
else
{
lean_object* v_val_591_; lean_object* v_ext_592_; uint8_t v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; uint8_t v___x_597_; 
v_val_591_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_val_591_);
lean_dec_ref_known(v___x_583_, 1);
v_ext_592_ = lean_ctor_get(v_attr_579_, 1);
v___x_593_ = 0;
v___x_594_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_582_, v_ext_592_, v_env_580_, v_val_591_, v___x_593_);
lean_dec(v_val_591_);
lean_dec_ref(v_env_580_);
v___x_595_ = lean_unsigned_to_nat(0u);
v___x_596_ = lean_array_get_size(v___x_594_);
v___x_597_ = lean_nat_dec_lt(v___x_595_, v___x_596_);
if (v___x_597_ == 0)
{
lean_dec_ref(v___x_594_);
return v___x_597_;
}
else
{
lean_object* v___x_598_; lean_object* v___x_599_; uint8_t v___x_600_; 
v___x_598_ = lean_unsigned_to_nat(1u);
v___x_599_ = lean_nat_sub(v___x_596_, v___x_598_);
v___x_600_ = lean_nat_dec_le(v___x_595_, v___x_599_);
if (v___x_600_ == 0)
{
lean_dec(v___x_599_);
lean_dec_ref(v___x_594_);
return v___x_600_;
}
else
{
uint8_t v___x_601_; 
lean_inc(v___x_599_);
v___x_601_ = l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___redArg(v___x_599_, v___x_594_, v_decl_581_, v___x_595_, v___x_599_);
lean_dec_ref(v___x_594_);
lean_dec(v___x_599_);
return v___x_601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrderedTagAttribute_hasTag___boxed(lean_object* v_attr_602_, lean_object* v_env_603_, lean_object* v_decl_604_){
_start:
{
uint8_t v_res_605_; lean_object* v_r_606_; 
v_res_605_ = l_Lake_OrderedTagAttribute_hasTag(v_attr_602_, v_env_603_, v_decl_604_);
lean_dec(v_decl_604_);
lean_dec_ref(v_attr_602_);
v_r_606_ = lean_box(v_res_605_);
return v_r_606_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1(lean_object* v___y_607_, lean_object* v_as_608_, lean_object* v_k_609_, lean_object* v_x_610_, lean_object* v_x_611_, lean_object* v_x_612_){
_start:
{
uint8_t v___x_613_; 
v___x_613_ = l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___redArg(v___y_607_, v_as_608_, v_k_609_, v_x_610_, v_x_611_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___boxed(lean_object* v___y_614_, lean_object* v_as_615_, lean_object* v_k_616_, lean_object* v_x_617_, lean_object* v_x_618_, lean_object* v_x_619_){
_start:
{
uint8_t v_res_620_; lean_object* v_r_621_; 
v_res_620_ = l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1(v___y_614_, v_as_615_, v_k_616_, v_x_617_, v_x_618_, v_x_619_);
lean_dec(v_k_616_);
lean_dec_ref(v_as_615_);
lean_dec(v___y_614_);
v_r_621_ = lean_box(v_res_620_);
return v_r_621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrderedTagAttribute_getAllEntries_spec__0(lean_object* v_as_622_, size_t v_i_623_, size_t v_stop_624_, lean_object* v_b_625_){
_start:
{
uint8_t v___x_626_; 
v___x_626_ = lean_usize_dec_eq(v_i_623_, v_stop_624_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; lean_object* v___x_628_; size_t v___x_629_; size_t v___x_630_; 
v___x_627_ = lean_array_uget_borrowed(v_as_622_, v_i_623_);
v___x_628_ = l_Array_append___redArg(v_b_625_, v___x_627_);
v___x_629_ = ((size_t)1ULL);
v___x_630_ = lean_usize_add(v_i_623_, v___x_629_);
v_i_623_ = v___x_630_;
v_b_625_ = v___x_628_;
goto _start;
}
else
{
return v_b_625_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrderedTagAttribute_getAllEntries_spec__0___boxed(lean_object* v_as_632_, lean_object* v_i_633_, lean_object* v_stop_634_, lean_object* v_b_635_){
_start:
{
size_t v_i_boxed_636_; size_t v_stop_boxed_637_; lean_object* v_res_638_; 
v_i_boxed_636_ = lean_unbox_usize(v_i_633_);
lean_dec(v_i_633_);
v_stop_boxed_637_ = lean_unbox_usize(v_stop_634_);
lean_dec(v_stop_634_);
v_res_638_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrderedTagAttribute_getAllEntries_spec__0(v_as_632_, v_i_boxed_636_, v_stop_boxed_637_, v_b_635_);
lean_dec_ref(v_as_632_);
return v_res_638_;
}
}
static lean_object* _init_l_Lake_OrderedTagAttribute_getAllEntries___closed__0(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_obj_once(&l_Lake_OrderedTagAttribute_hasTag___closed__0, &l_Lake_OrderedTagAttribute_hasTag___closed__0_once, _init_l_Lake_OrderedTagAttribute_hasTag___closed__0);
v___x_640_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrderedTagAttribute_getAllEntries(lean_object* v_attr_641_, lean_object* v_env_642_){
_start:
{
lean_object* v_ext_643_; lean_object* v_toEnvExtension_644_; lean_object* v_asyncMode_645_; lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; lean_object* v_s_649_; lean_object* v___y_651_; lean_object* v_importedEntries_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v_ext_643_ = lean_ctor_get(v_attr_641_, 1);
v_toEnvExtension_644_ = lean_ctor_get(v_ext_643_, 0);
v_asyncMode_645_ = lean_ctor_get(v_toEnvExtension_644_, 2);
v___x_646_ = lean_obj_once(&l_Lake_OrderedTagAttribute_getAllEntries___closed__0, &l_Lake_OrderedTagAttribute_getAllEntries___closed__0_once, _init_l_Lake_OrderedTagAttribute_getAllEntries___closed__0);
v___x_647_ = lean_box(0);
v___x_648_ = 0;
v_s_649_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_646_, v_toEnvExtension_644_, v_env_642_, v_asyncMode_645_, v___x_647_, v___x_648_);
v_importedEntries_654_ = lean_ctor_get(v_s_649_, 0);
v___x_655_ = lean_unsigned_to_nat(0u);
v___x_656_ = ((lean_object*)(l_Lake_registerOrderedTagAttribute___closed__4));
v___x_657_ = lean_array_get_size(v_importedEntries_654_);
v___x_658_ = lean_nat_dec_lt(v___x_655_, v___x_657_);
if (v___x_658_ == 0)
{
v___y_651_ = v___x_656_;
goto v___jp_650_;
}
else
{
size_t v___x_659_; size_t v___x_660_; lean_object* v___x_661_; 
v___x_659_ = ((size_t)0ULL);
v___x_660_ = lean_usize_of_nat(v___x_657_);
v___x_661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrderedTagAttribute_getAllEntries_spec__0(v_importedEntries_654_, v___x_659_, v___x_660_, v___x_656_);
v___y_651_ = v___x_661_;
goto v___jp_650_;
}
v___jp_650_:
{
lean_object* v_state_652_; lean_object* v___x_653_; 
v_state_652_ = lean_ctor_get(v_s_649_, 1);
lean_inc(v_state_652_);
lean_dec(v_s_649_);
v___x_653_ = l_Array_append___redArg(v___y_651_, v_state_652_);
lean_dec(v_state_652_);
return v___x_653_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrderedTagAttribute_getAllEntries___boxed(lean_object* v_attr_662_, lean_object* v_env_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_662_, v_env_663_);
lean_dec_ref(v_attr_662_);
return v_res_664_;
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

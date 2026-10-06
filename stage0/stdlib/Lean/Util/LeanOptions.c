// Lean compiler output
// Module: Lean.Util.LeanOptions
// Imports: public import Lean.Data.Json.FromToJson.Basic
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
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_NameMap_fromJson_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_NameMap_toJson___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ofString_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ofString_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ofBool_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ofBool_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ofNat_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ofNat_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_instInhabitedLeanOptionValue_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_instInhabitedLeanOptionValue_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedLeanOptionValue_default___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedLeanOptionValue_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedLeanOptionValue_default___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedLeanOptionValue_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedLeanOptionValue_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedLeanOptionValue_default = (const lean_object*)&l_Lean_instInhabitedLeanOptionValue_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedLeanOptionValue = (const lean_object*)&l_Lean_instInhabitedLeanOptionValue_default___closed__1_value;
static const lean_string_object l_Lean_instReprLeanOptionValue_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.LeanOptionValue.ofString"};
static const lean_object* l_Lean_instReprLeanOptionValue_repr___closed__0 = (const lean_object*)&l_Lean_instReprLeanOptionValue_repr___closed__0_value;
static const lean_ctor_object l_Lean_instReprLeanOptionValue_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLeanOptionValue_repr___closed__0_value)}};
static const lean_object* l_Lean_instReprLeanOptionValue_repr___closed__1 = (const lean_object*)&l_Lean_instReprLeanOptionValue_repr___closed__1_value;
static const lean_ctor_object l_Lean_instReprLeanOptionValue_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprLeanOptionValue_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprLeanOptionValue_repr___closed__2 = (const lean_object*)&l_Lean_instReprLeanOptionValue_repr___closed__2_value;
static lean_once_cell_t l_Lean_instReprLeanOptionValue_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprLeanOptionValue_repr___closed__3;
static lean_once_cell_t l_Lean_instReprLeanOptionValue_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprLeanOptionValue_repr___closed__4;
static const lean_string_object l_Lean_instReprLeanOptionValue_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.LeanOptionValue.ofBool"};
static const lean_object* l_Lean_instReprLeanOptionValue_repr___closed__5 = (const lean_object*)&l_Lean_instReprLeanOptionValue_repr___closed__5_value;
static const lean_ctor_object l_Lean_instReprLeanOptionValue_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLeanOptionValue_repr___closed__5_value)}};
static const lean_object* l_Lean_instReprLeanOptionValue_repr___closed__6 = (const lean_object*)&l_Lean_instReprLeanOptionValue_repr___closed__6_value;
static const lean_ctor_object l_Lean_instReprLeanOptionValue_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprLeanOptionValue_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprLeanOptionValue_repr___closed__7 = (const lean_object*)&l_Lean_instReprLeanOptionValue_repr___closed__7_value;
static const lean_string_object l_Lean_instReprLeanOptionValue_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.LeanOptionValue.ofNat"};
static const lean_object* l_Lean_instReprLeanOptionValue_repr___closed__8 = (const lean_object*)&l_Lean_instReprLeanOptionValue_repr___closed__8_value;
static const lean_ctor_object l_Lean_instReprLeanOptionValue_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLeanOptionValue_repr___closed__8_value)}};
static const lean_object* l_Lean_instReprLeanOptionValue_repr___closed__9 = (const lean_object*)&l_Lean_instReprLeanOptionValue_repr___closed__9_value;
static const lean_ctor_object l_Lean_instReprLeanOptionValue_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprLeanOptionValue_repr___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprLeanOptionValue_repr___closed__10 = (const lean_object*)&l_Lean_instReprLeanOptionValue_repr___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_instReprLeanOptionValue_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprLeanOptionValue_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprLeanOptionValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprLeanOptionValue_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprLeanOptionValue___closed__0 = (const lean_object*)&l_Lean_instReprLeanOptionValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprLeanOptionValue = (const lean_object*)&l_Lean_instReprLeanOptionValue___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ofDataValue_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_toDataValue(lean_object*);
static const lean_closure_object l_Lean_instValueLeanOptionValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LeanOptionValue_toDataValue, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instValueLeanOptionValue___closed__0 = (const lean_object*)&l_Lean_instValueLeanOptionValue___closed__0_value;
static const lean_closure_object l_Lean_instValueLeanOptionValue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LeanOptionValue_ofDataValue_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instValueLeanOptionValue___closed__1 = (const lean_object*)&l_Lean_instValueLeanOptionValue___closed__1_value;
static const lean_ctor_object l_Lean_instValueLeanOptionValue___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instValueLeanOptionValue___closed__0_value),((lean_object*)&l_Lean_instValueLeanOptionValue___closed__1_value)}};
static const lean_object* l_Lean_instValueLeanOptionValue___closed__2 = (const lean_object*)&l_Lean_instValueLeanOptionValue___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_instValueLeanOptionValue = (const lean_object*)&l_Lean_instValueLeanOptionValue___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_instCoeStringLeanOptionValue___lam__0(lean_object*);
static const lean_closure_object l_Lean_instCoeStringLeanOptionValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instCoeStringLeanOptionValue___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instCoeStringLeanOptionValue___closed__0 = (const lean_object*)&l_Lean_instCoeStringLeanOptionValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instCoeStringLeanOptionValue = (const lean_object*)&l_Lean_instCoeStringLeanOptionValue___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instCoeBoolLeanOptionValue___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_instCoeBoolLeanOptionValue___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instCoeBoolLeanOptionValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instCoeBoolLeanOptionValue___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instCoeBoolLeanOptionValue___closed__0 = (const lean_object*)&l_Lean_instCoeBoolLeanOptionValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instCoeBoolLeanOptionValue = (const lean_object*)&l_Lean_instCoeBoolLeanOptionValue___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instCoeNatLeanOptionValue___lam__0(lean_object*);
static const lean_closure_object l_Lean_instCoeNatLeanOptionValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instCoeNatLeanOptionValue___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instCoeNatLeanOptionValue___closed__0 = (const lean_object*)&l_Lean_instCoeNatLeanOptionValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instCoeNatLeanOptionValue = (const lean_object*)&l_Lean_instCoeNatLeanOptionValue___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instOfNatLeanOptionValue(lean_object*);
static const lean_string_object l_Lean_instFromJsonLeanOptionValue___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "invalid LeanOptionValue type"};
static const lean_object* l_Lean_instFromJsonLeanOptionValue___lam__0___closed__0 = (const lean_object*)&l_Lean_instFromJsonLeanOptionValue___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instFromJsonLeanOptionValue___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instFromJsonLeanOptionValue___lam__0___closed__0_value)}};
static const lean_object* l_Lean_instFromJsonLeanOptionValue___lam__0___closed__1 = (const lean_object*)&l_Lean_instFromJsonLeanOptionValue___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_instFromJsonLeanOptionValue___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonLeanOptionValue___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_instFromJsonLeanOptionValue___lam__0(lean_object*);
static const lean_closure_object l_Lean_instFromJsonLeanOptionValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonLeanOptionValue___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonLeanOptionValue___closed__0 = (const lean_object*)&l_Lean_instFromJsonLeanOptionValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonLeanOptionValue = (const lean_object*)&l_Lean_instFromJsonLeanOptionValue___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonLeanOptionValue___lam__0(lean_object*);
static const lean_closure_object l_Lean_instToJsonLeanOptionValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonLeanOptionValue___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonLeanOptionValue___closed__0 = (const lean_object*)&l_Lean_instToJsonLeanOptionValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonLeanOptionValue = (const lean_object*)&l_Lean_instToJsonLeanOptionValue___closed__0_value;
static const lean_string_object l_Lean_LeanOptionValue_asCliFlagValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\""};
static const lean_object* l_Lean_LeanOptionValue_asCliFlagValue___closed__0 = (const lean_object*)&l_Lean_LeanOptionValue_asCliFlagValue___closed__0_value;
static const lean_string_object l_Lean_LeanOptionValue_asCliFlagValue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_LeanOptionValue_asCliFlagValue___closed__1 = (const lean_object*)&l_Lean_LeanOptionValue_asCliFlagValue___closed__1_value;
static const lean_string_object l_Lean_LeanOptionValue_asCliFlagValue___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_LeanOptionValue_asCliFlagValue___closed__2 = (const lean_object*)&l_Lean_LeanOptionValue_asCliFlagValue___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_asCliFlagValue(lean_object*);
static const lean_ctor_object l_Lean_instInhabitedLeanOption_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instInhabitedLeanOptionValue_default___closed__1_value)}};
static const lean_object* l_Lean_instInhabitedLeanOption_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedLeanOption_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedLeanOption_default = (const lean_object*)&l_Lean_instInhabitedLeanOption_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedLeanOption = (const lean_object*)&l_Lean_instInhabitedLeanOption_default___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprLeanOption_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_instReprLeanOption_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_instReprLeanOption_repr___redArg___closed__0 = (const lean_object*)&l_Lean_instReprLeanOption_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_instReprLeanOption_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_instReprLeanOption_repr___redArg___closed__1 = (const lean_object*)&l_Lean_instReprLeanOption_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_instReprLeanOption_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLeanOption_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_instReprLeanOption_repr___redArg___closed__2 = (const lean_object*)&l_Lean_instReprLeanOption_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_instReprLeanOption_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprLeanOption_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_instReprLeanOption_repr___redArg___closed__3 = (const lean_object*)&l_Lean_instReprLeanOption_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_instReprLeanOption_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_instReprLeanOption_repr___redArg___closed__4 = (const lean_object*)&l_Lean_instReprLeanOption_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_instReprLeanOption_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLeanOption_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_instReprLeanOption_repr___redArg___closed__5 = (const lean_object*)&l_Lean_instReprLeanOption_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_instReprLeanOption_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprLeanOption_repr___redArg___closed__3_value),((lean_object*)&l_Lean_instReprLeanOption_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_instReprLeanOption_repr___redArg___closed__6 = (const lean_object*)&l_Lean_instReprLeanOption_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_instReprLeanOption_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprLeanOption_repr___redArg___closed__7;
static const lean_string_object l_Lean_instReprLeanOption_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_instReprLeanOption_repr___redArg___closed__8 = (const lean_object*)&l_Lean_instReprLeanOption_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_instReprLeanOption_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLeanOption_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_instReprLeanOption_repr___redArg___closed__9 = (const lean_object*)&l_Lean_instReprLeanOption_repr___redArg___closed__9_value;
static const lean_string_object l_Lean_instReprLeanOption_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "value"};
static const lean_object* l_Lean_instReprLeanOption_repr___redArg___closed__10 = (const lean_object*)&l_Lean_instReprLeanOption_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lean_instReprLeanOption_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLeanOption_repr___redArg___closed__10_value)}};
static const lean_object* l_Lean_instReprLeanOption_repr___redArg___closed__11 = (const lean_object*)&l_Lean_instReprLeanOption_repr___redArg___closed__11_value;
static lean_once_cell_t l_Lean_instReprLeanOption_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprLeanOption_repr___redArg___closed__12;
static const lean_string_object l_Lean_instReprLeanOption_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_instReprLeanOption_repr___redArg___closed__13 = (const lean_object*)&l_Lean_instReprLeanOption_repr___redArg___closed__13_value;
static lean_once_cell_t l_Lean_instReprLeanOption_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprLeanOption_repr___redArg___closed__14;
static lean_once_cell_t l_Lean_instReprLeanOption_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprLeanOption_repr___redArg___closed__15;
static const lean_ctor_object l_Lean_instReprLeanOption_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLeanOption_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_instReprLeanOption_repr___redArg___closed__16 = (const lean_object*)&l_Lean_instReprLeanOption_repr___redArg___closed__16_value;
static const lean_ctor_object l_Lean_instReprLeanOption_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLeanOption_repr___redArg___closed__13_value)}};
static const lean_object* l_Lean_instReprLeanOption_repr___redArg___closed__17 = (const lean_object*)&l_Lean_instReprLeanOption_repr___redArg___closed__17_value;
LEAN_EXPORT lean_object* l_Lean_instReprLeanOption_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprLeanOption_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprLeanOption_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprLeanOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprLeanOption_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprLeanOption___closed__0 = (const lean_object*)&l_Lean_instReprLeanOption___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprLeanOption = (const lean_object*)&l_Lean_instReprLeanOption___closed__0_value;
static const lean_string_object l_Lean_LeanOption_asCliArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-D"};
static const lean_object* l_Lean_LeanOption_asCliArg___closed__0 = (const lean_object*)&l_Lean_LeanOption_asCliArg___closed__0_value;
static const lean_string_object l_Lean_LeanOption_asCliArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "="};
static const lean_object* l_Lean_LeanOption_asCliArg___closed__1 = (const lean_object*)&l_Lean_LeanOption_asCliArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_LeanOption_asCliArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedLeanOptions_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedLeanOptions;
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1_spec__2(lean_object*, lean_object*);
static const lean_string_object l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__0 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprLeanOption_repr___redArg___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__1 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__1_value;
static const lean_string_object l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__2 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__3;
static lean_once_cell_t l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__4;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__5 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__5_value;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__2_value)}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__6 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__2(lean_object*, lean_object*);
static const lean_string_object l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__0 = (const lean_object*)&l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__0_value)}};
static const lean_object* l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__1 = (const lean_object*)&l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__1_value;
static const lean_string_object l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__2 = (const lean_object*)&l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__2_value;
static const lean_string_object l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__3 = (const lean_object*)&l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__3_value;
static lean_once_cell_t l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__4;
static lean_once_cell_t l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__5;
static const lean_ctor_object l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__2_value)}};
static const lean_object* l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__6 = (const lean_object*)&l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__6_value;
static const lean_ctor_object l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__3_value)}};
static const lean_object* l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__7 = (const lean_object*)&l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__7_value;
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprLeanOptions_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprLeanOptions_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_instReprLeanOptions_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "values"};
static const lean_object* l_Lean_instReprLeanOptions_repr___redArg___closed__0 = (const lean_object*)&l_Lean_instReprLeanOptions_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_instReprLeanOptions_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLeanOptions_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_instReprLeanOptions_repr___redArg___closed__1 = (const lean_object*)&l_Lean_instReprLeanOptions_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_instReprLeanOptions_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprLeanOptions_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_instReprLeanOptions_repr___redArg___closed__2 = (const lean_object*)&l_Lean_instReprLeanOptions_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_instReprLeanOptions_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprLeanOptions_repr___redArg___closed__2_value),((lean_object*)&l_Lean_instReprLeanOption_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_instReprLeanOptions_repr___redArg___closed__3 = (const lean_object*)&l_Lean_instReprLeanOptions_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lean_instReprLeanOptions_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprLeanOptions_repr___redArg___closed__4;
static const lean_string_object l_Lean_instReprLeanOptions_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.TreeMap.ofList "};
static const lean_object* l_Lean_instReprLeanOptions_repr___redArg___closed__5 = (const lean_object*)&l_Lean_instReprLeanOptions_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_instReprLeanOptions_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLeanOptions_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_instReprLeanOptions_repr___redArg___closed__6 = (const lean_object*)&l_Lean_instReprLeanOptions_repr___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_instReprLeanOptions_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprLeanOptions_repr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprLeanOptions_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprLeanOptions_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprLeanOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprLeanOptions_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprLeanOptions___closed__0 = (const lean_object*)&l_Lean_instReprLeanOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprLeanOptions = (const lean_object*)&l_Lean_instReprLeanOptions___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLeanOptions;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LeanOptions_ofArray_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LeanOptions_ofArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LeanOptions_ofArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LeanOptions_ofArray___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LeanOptions_append_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LeanOptions_append_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LeanOptions_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LeanOptions_append_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LeanOptions_append_spec__1(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instAppendLeanOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LeanOptions_append, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instAppendLeanOptions___closed__0 = (const lean_object*)&l_Lean_instAppendLeanOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instAppendLeanOptions = (const lean_object*)&l_Lean_instAppendLeanOptions___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_LeanOptions_appendArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LeanOptions_appendArray___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instHAppendLeanOptionsArrayLeanOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LeanOptions_appendArray___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instHAppendLeanOptionsArrayLeanOption___closed__0 = (const lean_object*)&l_Lean_instHAppendLeanOptionsArrayLeanOption___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instHAppendLeanOptionsArrayLeanOption = (const lean_object*)&l_Lean_instHAppendLeanOptionsArrayLeanOption___closed__0_value;
static const lean_string_object l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_LeanOptions_toOptions_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LeanOptions_toOptions(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_LeanOptions_fromOptions_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_LeanOptions_fromOptions_x3f_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LeanOptions_fromOptions_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_LeanOptions_fromOptions_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonLeanOptions___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instFromJsonLeanOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonLeanOptions___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_instFromJsonLeanOptionValue___closed__0_value)} };
static const lean_object* l_Lean_instFromJsonLeanOptions___closed__0 = (const lean_object*)&l_Lean_instFromJsonLeanOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonLeanOptions = (const lean_object*)&l_Lean_instFromJsonLeanOptions___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonLeanOptions___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instToJsonLeanOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonLeanOptions___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_instToJsonLeanOptionValue___closed__0_value)} };
static const lean_object* l_Lean_instToJsonLeanOptions___closed__0 = (const lean_object*)&l_Lean_instToJsonLeanOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonLeanOptions = (const lean_object*)&l_Lean_instToJsonLeanOptions___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_LeanOptionValue_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
switch(lean_obj_tag(v_t_5_))
{
case 0:
{
lean_object* v_s_7_; lean_object* v___x_8_; 
v_s_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_s_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_s_7_);
return v___x_8_;
}
case 1:
{
uint8_t v_b_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_b_9_ = lean_ctor_get_uint8(v_t_5_, 0);
lean_dec_ref_known(v_t_5_, 0);
v___x_10_ = lean_box(v_b_9_);
v___x_11_ = lean_apply_1(v_k_6_, v___x_10_);
return v___x_11_;
}
default: 
{
lean_object* v_n_12_; lean_object* v___x_13_; 
v_n_12_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_n_12_);
lean_dec_ref_known(v_t_5_, 1);
v___x_13_ = lean_apply_1(v_k_6_, v_n_12_);
return v___x_13_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ctorElim(lean_object* v_motive_14_, lean_object* v_ctorIdx_15_, lean_object* v_t_16_, lean_object* v_h_17_, lean_object* v_k_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_LeanOptionValue_ctorElim___redArg(v_t_16_, v_k_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ctorElim___boxed(lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_LeanOptionValue_ctorElim(v_motive_20_, v_ctorIdx_21_, v_t_22_, v_h_23_, v_k_24_);
lean_dec(v_ctorIdx_21_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ofString_elim___redArg(lean_object* v_t_26_, lean_object* v_ofString_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Lean_LeanOptionValue_ctorElim___redArg(v_t_26_, v_ofString_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ofString_elim(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_ofString_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_LeanOptionValue_ctorElim___redArg(v_t_30_, v_ofString_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ofBool_elim___redArg(lean_object* v_t_34_, lean_object* v_ofBool_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_LeanOptionValue_ctorElim___redArg(v_t_34_, v_ofBool_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ofBool_elim(lean_object* v_motive_37_, lean_object* v_t_38_, lean_object* v_h_39_, lean_object* v_ofBool_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_LeanOptionValue_ctorElim___redArg(v_t_38_, v_ofBool_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ofNat_elim___redArg(lean_object* v_t_42_, lean_object* v_ofNat_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lean_LeanOptionValue_ctorElim___redArg(v_t_42_, v_ofNat_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ofNat_elim(lean_object* v_motive_45_, lean_object* v_t_46_, lean_object* v_h_47_, lean_object* v_ofNat_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lean_LeanOptionValue_ctorElim___redArg(v_t_46_, v_ofNat_48_);
return v___x_49_;
}
}
static lean_object* _init_l_Lean_instReprLeanOptionValue_repr___closed__3(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_unsigned_to_nat(2u);
v___x_62_ = lean_nat_to_int(v___x_61_);
return v___x_62_;
}
}
static lean_object* _init_l_Lean_instReprLeanOptionValue_repr___closed__4(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = lean_unsigned_to_nat(1u);
v___x_64_ = lean_nat_to_int(v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLeanOptionValue_repr(lean_object* v_x_77_, lean_object* v_prec_78_){
_start:
{
switch(lean_obj_tag(v_x_77_))
{
case 0:
{
lean_object* v_s_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_99_; 
v_s_79_ = lean_ctor_get(v_x_77_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v_x_77_);
if (v_isSharedCheck_99_ == 0)
{
v___x_81_ = v_x_77_;
v_isShared_82_ = v_isSharedCheck_99_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_s_79_);
lean_dec(v_x_77_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_99_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___y_84_; lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_95_ = lean_unsigned_to_nat(1024u);
v___x_96_ = lean_nat_dec_le(v___x_95_, v_prec_78_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; 
v___x_97_ = lean_obj_once(&l_Lean_instReprLeanOptionValue_repr___closed__3, &l_Lean_instReprLeanOptionValue_repr___closed__3_once, _init_l_Lean_instReprLeanOptionValue_repr___closed__3);
v___y_84_ = v___x_97_;
goto v___jp_83_;
}
else
{
lean_object* v___x_98_; 
v___x_98_ = lean_obj_once(&l_Lean_instReprLeanOptionValue_repr___closed__4, &l_Lean_instReprLeanOptionValue_repr___closed__4_once, _init_l_Lean_instReprLeanOptionValue_repr___closed__4);
v___y_84_ = v___x_98_;
goto v___jp_83_;
}
v___jp_83_:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_88_; 
v___x_85_ = ((lean_object*)(l_Lean_instReprLeanOptionValue_repr___closed__2));
v___x_86_ = l_String_quote(v_s_79_);
if (v_isShared_82_ == 0)
{
lean_ctor_set_tag(v___x_81_, 3);
lean_ctor_set(v___x_81_, 0, v___x_86_);
v___x_88_ = v___x_81_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_86_);
v___x_88_ = v_reuseFailAlloc_94_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_89_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_85_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
lean_inc(v___y_84_);
v___x_90_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_90_, 0, v___y_84_);
lean_ctor_set(v___x_90_, 1, v___x_89_);
v___x_91_ = 0;
v___x_92_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_92_, 0, v___x_90_);
lean_ctor_set_uint8(v___x_92_, sizeof(void*)*1, v___x_91_);
v___x_93_ = l_Repr_addAppParen(v___x_92_, v_prec_78_);
return v___x_93_;
}
}
}
}
case 1:
{
uint8_t v_b_100_; lean_object* v___y_102_; lean_object* v___x_110_; uint8_t v___x_111_; 
v_b_100_ = lean_ctor_get_uint8(v_x_77_, 0);
lean_dec_ref_known(v_x_77_, 0);
v___x_110_ = lean_unsigned_to_nat(1024u);
v___x_111_ = lean_nat_dec_le(v___x_110_, v_prec_78_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; 
v___x_112_ = lean_obj_once(&l_Lean_instReprLeanOptionValue_repr___closed__3, &l_Lean_instReprLeanOptionValue_repr___closed__3_once, _init_l_Lean_instReprLeanOptionValue_repr___closed__3);
v___y_102_ = v___x_112_;
goto v___jp_101_;
}
else
{
lean_object* v___x_113_; 
v___x_113_ = lean_obj_once(&l_Lean_instReprLeanOptionValue_repr___closed__4, &l_Lean_instReprLeanOptionValue_repr___closed__4_once, _init_l_Lean_instReprLeanOptionValue_repr___closed__4);
v___y_102_ = v___x_113_;
goto v___jp_101_;
}
v___jp_101_:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_103_ = ((lean_object*)(l_Lean_instReprLeanOptionValue_repr___closed__7));
v___x_104_ = l_Bool_repr___redArg(v_b_100_);
v___x_105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_103_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
lean_inc(v___y_102_);
v___x_106_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_106_, 0, v___y_102_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
v___x_107_ = 0;
v___x_108_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_108_, 0, v___x_106_);
lean_ctor_set_uint8(v___x_108_, sizeof(void*)*1, v___x_107_);
v___x_109_ = l_Repr_addAppParen(v___x_108_, v_prec_78_);
return v___x_109_;
}
}
default: 
{
lean_object* v_n_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_134_; 
v_n_114_ = lean_ctor_get(v_x_77_, 0);
v_isSharedCheck_134_ = !lean_is_exclusive(v_x_77_);
if (v_isSharedCheck_134_ == 0)
{
v___x_116_ = v_x_77_;
v_isShared_117_ = v_isSharedCheck_134_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_n_114_);
lean_dec(v_x_77_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_134_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___y_119_; lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_130_ = lean_unsigned_to_nat(1024u);
v___x_131_ = lean_nat_dec_le(v___x_130_, v_prec_78_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; 
v___x_132_ = lean_obj_once(&l_Lean_instReprLeanOptionValue_repr___closed__3, &l_Lean_instReprLeanOptionValue_repr___closed__3_once, _init_l_Lean_instReprLeanOptionValue_repr___closed__3);
v___y_119_ = v___x_132_;
goto v___jp_118_;
}
else
{
lean_object* v___x_133_; 
v___x_133_ = lean_obj_once(&l_Lean_instReprLeanOptionValue_repr___closed__4, &l_Lean_instReprLeanOptionValue_repr___closed__4_once, _init_l_Lean_instReprLeanOptionValue_repr___closed__4);
v___y_119_ = v___x_133_;
goto v___jp_118_;
}
v___jp_118_:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_123_; 
v___x_120_ = ((lean_object*)(l_Lean_instReprLeanOptionValue_repr___closed__10));
v___x_121_ = l_Nat_reprFast(v_n_114_);
if (v_isShared_117_ == 0)
{
lean_ctor_set_tag(v___x_116_, 3);
lean_ctor_set(v___x_116_, 0, v___x_121_);
v___x_123_ = v___x_116_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_121_);
v___x_123_ = v_reuseFailAlloc_129_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_124_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_124_, 0, v___x_120_);
lean_ctor_set(v___x_124_, 1, v___x_123_);
lean_inc(v___y_119_);
v___x_125_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_125_, 0, v___y_119_);
lean_ctor_set(v___x_125_, 1, v___x_124_);
v___x_126_ = 0;
v___x_127_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_127_, 0, v___x_125_);
lean_ctor_set_uint8(v___x_127_, sizeof(void*)*1, v___x_126_);
v___x_128_ = l_Repr_addAppParen(v___x_127_, v_prec_78_);
return v___x_128_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLeanOptionValue_repr___boxed(lean_object* v_x_135_, lean_object* v_prec_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lean_instReprLeanOptionValue_repr(v_x_135_, v_prec_136_);
lean_dec(v_prec_136_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ofDataValue_x3f(lean_object* v_x_140_){
_start:
{
switch(lean_obj_tag(v_x_140_))
{
case 0:
{
lean_object* v_v_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_149_; 
v_v_141_ = lean_ctor_get(v_x_140_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v_x_140_);
if (v_isSharedCheck_149_ == 0)
{
v___x_143_ = v_x_140_;
v_isShared_144_ = v_isSharedCheck_149_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_v_141_);
lean_dec(v_x_140_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_149_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_144_ == 0)
{
v___x_146_ = v___x_143_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_v_141_);
v___x_146_ = v_reuseFailAlloc_148_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v___x_147_; 
v___x_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
return v___x_147_;
}
}
}
case 1:
{
uint8_t v_v_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_158_; 
v_v_150_ = lean_ctor_get_uint8(v_x_140_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v_x_140_);
if (v_isSharedCheck_158_ == 0)
{
v___x_152_ = v_x_140_;
v_isShared_153_ = v_isSharedCheck_158_;
goto v_resetjp_151_;
}
else
{
lean_dec(v_x_140_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_158_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_155_; 
if (v_isShared_153_ == 0)
{
v___x_155_ = v___x_152_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_157_, 0, v_v_150_);
v___x_155_ = v_reuseFailAlloc_157_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
lean_object* v___x_156_; 
v___x_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
return v___x_156_;
}
}
}
case 3:
{
lean_object* v_v_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_167_; 
v_v_159_ = lean_ctor_get(v_x_140_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v_x_140_);
if (v_isSharedCheck_167_ == 0)
{
v___x_161_ = v_x_140_;
v_isShared_162_ = v_isSharedCheck_167_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_v_159_);
lean_dec(v_x_140_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_167_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_164_; 
if (v_isShared_162_ == 0)
{
lean_ctor_set_tag(v___x_161_, 2);
v___x_164_ = v___x_161_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_v_159_);
v___x_164_ = v_reuseFailAlloc_166_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
lean_object* v___x_165_; 
v___x_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
return v___x_165_;
}
}
}
default: 
{
lean_object* v___x_168_; 
lean_dec_ref(v_x_140_);
v___x_168_ = lean_box(0);
return v___x_168_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_toDataValue(lean_object* v_x_169_){
_start:
{
switch(lean_obj_tag(v_x_169_))
{
case 0:
{
lean_object* v_s_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_177_; 
v_s_170_ = lean_ctor_get(v_x_169_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v_x_169_);
if (v_isSharedCheck_177_ == 0)
{
v___x_172_ = v_x_169_;
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_s_170_);
lean_dec(v_x_169_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_175_; 
if (v_isShared_173_ == 0)
{
v___x_175_ = v___x_172_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_s_170_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
case 1:
{
uint8_t v_b_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_185_; 
v_b_178_ = lean_ctor_get_uint8(v_x_169_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v_x_169_);
if (v_isSharedCheck_185_ == 0)
{
v___x_180_ = v_x_169_;
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
else
{
lean_dec(v_x_169_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_183_; 
if (v_isShared_181_ == 0)
{
v___x_183_ = v___x_180_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_184_, 0, v_b_178_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
default: 
{
lean_object* v_n_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_193_; 
v_n_186_ = lean_ctor_get(v_x_169_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v_x_169_);
if (v_isSharedCheck_193_ == 0)
{
v___x_188_ = v_x_169_;
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_n_186_);
lean_dec(v_x_169_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
if (v_isShared_189_ == 0)
{
lean_ctor_set_tag(v___x_188_, 3);
v___x_191_ = v___x_188_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_n_186_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeStringLeanOptionValue___lam__0(lean_object* v_s_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_201_, 0, v_s_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeBoolLeanOptionValue___lam__0(uint8_t v_b_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_205_, 0, v_b_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeBoolLeanOptionValue___lam__0___boxed(lean_object* v_b_206_){
_start:
{
uint8_t v_b_boxed_207_; lean_object* v_res_208_; 
v_b_boxed_207_ = lean_unbox(v_b_206_);
v_res_208_ = l_Lean_instCoeBoolLeanOptionValue___lam__0(v_b_boxed_207_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeNatLeanOptionValue___lam__0(lean_object* v_n_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_212_, 0, v_n_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_instOfNatLeanOptionValue(lean_object* v_n_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_216_, 0, v_n_215_);
return v___x_216_;
}
}
static lean_object* _init_l_Lean_instFromJsonLeanOptionValue___lam__0___closed__2(void){
_start:
{
lean_object* v_natZero_220_; lean_object* v_intZero_221_; 
v_natZero_220_ = lean_unsigned_to_nat(0u);
v_intZero_221_ = lean_nat_to_int(v_natZero_220_);
return v_intZero_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonLeanOptionValue___lam__0(lean_object* v_x_222_){
_start:
{
switch(lean_obj_tag(v_x_222_))
{
case 3:
{
lean_object* v_s_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_233_; 
v_s_225_ = lean_ctor_get(v_x_222_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v_x_222_);
if (v_isSharedCheck_233_ == 0)
{
v___x_227_ = v_x_222_;
v_isShared_228_ = v_isSharedCheck_233_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_s_225_);
lean_dec(v_x_222_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_233_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_230_; 
if (v_isShared_228_ == 0)
{
lean_ctor_set_tag(v___x_227_, 0);
v___x_230_ = v___x_227_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_s_225_);
v___x_230_ = v_reuseFailAlloc_232_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v___x_231_; 
v___x_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
return v___x_231_;
}
}
}
case 1:
{
uint8_t v_b_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_242_; 
v_b_234_ = lean_ctor_get_uint8(v_x_222_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v_x_222_);
if (v_isSharedCheck_242_ == 0)
{
v___x_236_ = v_x_222_;
v_isShared_237_ = v_isSharedCheck_242_;
goto v_resetjp_235_;
}
else
{
lean_dec(v_x_222_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_242_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_241_, 0, v_b_234_);
v___x_239_ = v_reuseFailAlloc_241_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
lean_object* v___x_240_; 
v___x_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
return v___x_240_;
}
}
}
case 2:
{
lean_object* v_n_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_258_; 
v_n_243_ = lean_ctor_get(v_x_222_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v_x_222_);
if (v_isSharedCheck_258_ == 0)
{
v___x_245_ = v_x_222_;
v_isShared_246_ = v_isSharedCheck_258_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_n_243_);
lean_dec(v_x_222_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_258_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v_mantissa_247_; lean_object* v_exponent_248_; lean_object* v_natZero_249_; lean_object* v_intZero_250_; uint8_t v_isNeg_251_; 
v_mantissa_247_ = lean_ctor_get(v_n_243_, 0);
lean_inc(v_mantissa_247_);
v_exponent_248_ = lean_ctor_get(v_n_243_, 1);
lean_inc(v_exponent_248_);
lean_dec_ref(v_n_243_);
v_natZero_249_ = lean_unsigned_to_nat(0u);
v_intZero_250_ = lean_obj_once(&l_Lean_instFromJsonLeanOptionValue___lam__0___closed__2, &l_Lean_instFromJsonLeanOptionValue___lam__0___closed__2_once, _init_l_Lean_instFromJsonLeanOptionValue___lam__0___closed__2);
v_isNeg_251_ = lean_int_dec_lt(v_mantissa_247_, v_intZero_250_);
if (v_isNeg_251_ == 0)
{
uint8_t v___x_252_; 
v___x_252_ = lean_nat_dec_eq(v_exponent_248_, v_natZero_249_);
lean_dec(v_exponent_248_);
if (v___x_252_ == 0)
{
lean_dec(v_mantissa_247_);
lean_del_object(v___x_245_);
goto v___jp_223_;
}
else
{
lean_object* v_a_253_; lean_object* v___x_255_; 
v_a_253_ = lean_nat_abs(v_mantissa_247_);
lean_dec(v_mantissa_247_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v_a_253_);
v___x_255_ = v___x_245_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_a_253_);
v___x_255_ = v_reuseFailAlloc_257_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
lean_object* v___x_256_; 
v___x_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
return v___x_256_;
}
}
}
else
{
lean_dec(v_exponent_248_);
lean_dec(v_mantissa_247_);
lean_del_object(v___x_245_);
goto v___jp_223_;
}
}
}
default: 
{
lean_dec(v_x_222_);
goto v___jp_223_;
}
}
v___jp_223_:
{
lean_object* v___x_224_; 
v___x_224_ = ((lean_object*)(l_Lean_instFromJsonLeanOptionValue___lam__0___closed__1));
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonLeanOptionValue___lam__0(lean_object* v_x_261_){
_start:
{
switch(lean_obj_tag(v_x_261_))
{
case 0:
{
lean_object* v_s_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_269_; 
v_s_262_ = lean_ctor_get(v_x_261_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v_x_261_);
if (v_isSharedCheck_269_ == 0)
{
v___x_264_ = v_x_261_;
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_s_262_);
lean_dec(v_x_261_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
if (v_isShared_265_ == 0)
{
lean_ctor_set_tag(v___x_264_, 3);
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_s_262_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
case 1:
{
uint8_t v_b_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
v_b_270_ = lean_ctor_get_uint8(v_x_261_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v_x_261_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v_x_261_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_dec(v_x_261_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_276_, 0, v_b_270_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
default: 
{
lean_object* v_n_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_286_; 
v_n_278_ = lean_ctor_get(v_x_261_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v_x_261_);
if (v_isSharedCheck_286_ == 0)
{
v___x_280_ = v_x_261_;
v_isShared_281_ = v_isSharedCheck_286_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_n_278_);
lean_dec(v_x_261_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_286_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_282_; lean_object* v___x_284_; 
v___x_282_ = l_Lean_JsonNumber_fromNat(v_n_278_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v___x_282_);
v___x_284_ = v___x_280_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_282_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_asCliFlagValue(lean_object* v_x_292_){
_start:
{
switch(lean_obj_tag(v_x_292_))
{
case 0:
{
lean_object* v_s_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v_s_293_ = lean_ctor_get(v_x_292_, 0);
lean_inc_ref(v_s_293_);
lean_dec_ref_known(v_x_292_, 1);
v___x_294_ = ((lean_object*)(l_Lean_LeanOptionValue_asCliFlagValue___closed__0));
v___x_295_ = lean_string_append(v___x_294_, v_s_293_);
lean_dec_ref(v_s_293_);
v___x_296_ = lean_string_append(v___x_295_, v___x_294_);
return v___x_296_;
}
case 1:
{
uint8_t v_b_297_; 
v_b_297_ = lean_ctor_get_uint8(v_x_292_, 0);
lean_dec_ref_known(v_x_292_, 0);
if (v_b_297_ == 0)
{
lean_object* v___x_298_; 
v___x_298_ = ((lean_object*)(l_Lean_LeanOptionValue_asCliFlagValue___closed__1));
return v___x_298_;
}
else
{
lean_object* v___x_299_; 
v___x_299_ = ((lean_object*)(l_Lean_LeanOptionValue_asCliFlagValue___closed__2));
return v___x_299_;
}
}
default: 
{
lean_object* v_n_300_; lean_object* v___x_301_; 
v_n_300_ = lean_ctor_get(v_x_292_, 0);
lean_inc(v_n_300_);
lean_dec_ref_known(v_x_292_, 1);
v___x_301_ = l_Nat_reprFast(v_n_300_);
return v___x_301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprLeanOption_repr_spec__0(lean_object* v_a_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = lean_nat_to_int(v_a_307_);
return v___x_308_;
}
}
static lean_object* _init_l_Lean_instReprLeanOption_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = lean_unsigned_to_nat(8u);
v___x_323_ = lean_nat_to_int(v___x_322_);
return v___x_323_;
}
}
static lean_object* _init_l_Lean_instReprLeanOption_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = lean_unsigned_to_nat(9u);
v___x_331_ = lean_nat_to_int(v___x_330_);
return v___x_331_;
}
}
static lean_object* _init_l_Lean_instReprLeanOption_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = ((lean_object*)(l_Lean_instReprLeanOption_repr___redArg___closed__0));
v___x_334_ = lean_string_length(v___x_333_);
return v___x_334_;
}
}
static lean_object* _init_l_Lean_instReprLeanOption_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_obj_once(&l_Lean_instReprLeanOption_repr___redArg___closed__14, &l_Lean_instReprLeanOption_repr___redArg___closed__14_once, _init_l_Lean_instReprLeanOption_repr___redArg___closed__14);
v___x_336_ = lean_nat_to_int(v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLeanOption_repr___redArg(lean_object* v_x_341_){
_start:
{
lean_object* v_name_342_; lean_object* v_value_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_377_; 
v_name_342_ = lean_ctor_get(v_x_341_, 0);
v_value_343_ = lean_ctor_get(v_x_341_, 1);
v_isSharedCheck_377_ = !lean_is_exclusive(v_x_341_);
if (v_isSharedCheck_377_ == 0)
{
v___x_345_ = v_x_341_;
v_isShared_346_ = v_isSharedCheck_377_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_value_343_);
lean_inc(v_name_342_);
lean_dec(v_x_341_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_377_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_353_; 
v___x_347_ = ((lean_object*)(l_Lean_instReprLeanOption_repr___redArg___closed__5));
v___x_348_ = ((lean_object*)(l_Lean_instReprLeanOption_repr___redArg___closed__6));
v___x_349_ = lean_obj_once(&l_Lean_instReprLeanOption_repr___redArg___closed__7, &l_Lean_instReprLeanOption_repr___redArg___closed__7_once, _init_l_Lean_instReprLeanOption_repr___redArg___closed__7);
v___x_350_ = lean_unsigned_to_nat(0u);
v___x_351_ = l_Lean_Name_reprPrec(v_name_342_, v___x_350_);
if (v_isShared_346_ == 0)
{
lean_ctor_set_tag(v___x_345_, 4);
lean_ctor_set(v___x_345_, 1, v___x_351_);
lean_ctor_set(v___x_345_, 0, v___x_349_);
v___x_353_ = v___x_345_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_349_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v___x_351_);
v___x_353_ = v_reuseFailAlloc_376_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
uint8_t v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_354_ = 0;
v___x_355_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_355_, 0, v___x_353_);
lean_ctor_set_uint8(v___x_355_, sizeof(void*)*1, v___x_354_);
v___x_356_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_348_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v___x_357_ = ((lean_object*)(l_Lean_instReprLeanOption_repr___redArg___closed__9));
v___x_358_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_356_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
v___x_359_ = lean_box(1);
v___x_360_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_358_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v___x_361_ = ((lean_object*)(l_Lean_instReprLeanOption_repr___redArg___closed__11));
v___x_362_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_360_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
lean_ctor_set(v___x_363_, 1, v___x_347_);
v___x_364_ = lean_obj_once(&l_Lean_instReprLeanOption_repr___redArg___closed__12, &l_Lean_instReprLeanOption_repr___redArg___closed__12_once, _init_l_Lean_instReprLeanOption_repr___redArg___closed__12);
v___x_365_ = l_Lean_instReprLeanOptionValue_repr(v_value_343_, v___x_350_);
v___x_366_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_364_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
v___x_367_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_367_, 0, v___x_366_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*1, v___x_354_);
v___x_368_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_363_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
v___x_369_ = lean_obj_once(&l_Lean_instReprLeanOption_repr___redArg___closed__15, &l_Lean_instReprLeanOption_repr___redArg___closed__15_once, _init_l_Lean_instReprLeanOption_repr___redArg___closed__15);
v___x_370_ = ((lean_object*)(l_Lean_instReprLeanOption_repr___redArg___closed__16));
v___x_371_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
lean_ctor_set(v___x_371_, 1, v___x_368_);
v___x_372_ = ((lean_object*)(l_Lean_instReprLeanOption_repr___redArg___closed__17));
v___x_373_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_371_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
v___x_374_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_369_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
v___x_375_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_375_, 0, v___x_374_);
lean_ctor_set_uint8(v___x_375_, sizeof(void*)*1, v___x_354_);
return v___x_375_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLeanOption_repr(lean_object* v_x_378_, lean_object* v_prec_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_instReprLeanOption_repr___redArg(v_x_378_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLeanOption_repr___boxed(lean_object* v_x_381_, lean_object* v_prec_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_instReprLeanOption_repr(v_x_381_, v_prec_382_);
lean_dec(v_prec_382_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOption_asCliArg(lean_object* v_o_388_){
_start:
{
lean_object* v_name_389_; lean_object* v_value_390_; lean_object* v___x_391_; uint8_t v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v_name_389_ = lean_ctor_get(v_o_388_, 0);
lean_inc(v_name_389_);
v_value_390_ = lean_ctor_get(v_o_388_, 1);
lean_inc_ref(v_value_390_);
lean_dec_ref(v_o_388_);
v___x_391_ = ((lean_object*)(l_Lean_LeanOption_asCliArg___closed__0));
v___x_392_ = 1;
v___x_393_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_389_, v___x_392_);
v___x_394_ = lean_string_append(v___x_391_, v___x_393_);
lean_dec_ref(v___x_393_);
v___x_395_ = ((lean_object*)(l_Lean_LeanOption_asCliArg___closed__1));
v___x_396_ = lean_string_append(v___x_394_, v___x_395_);
v___x_397_ = l_Lean_LeanOptionValue_asCliFlagValue(v_value_390_);
v___x_398_ = lean_string_append(v___x_396_, v___x_397_);
lean_dec_ref(v___x_397_);
return v___x_398_;
}
}
static lean_object* _init_l_Lean_instInhabitedLeanOptions_default(void){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = lean_box(1);
return v___x_399_;
}
}
static lean_object* _init_l_Lean_instInhabitedLeanOptions(void){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = lean_box(1);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1_spec__2_spec__3(lean_object* v_x_401_, lean_object* v_x_402_, lean_object* v_x_403_){
_start:
{
if (lean_obj_tag(v_x_403_) == 0)
{
lean_dec(v_x_401_);
return v_x_402_;
}
else
{
lean_object* v_head_404_; lean_object* v_tail_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_414_; 
v_head_404_ = lean_ctor_get(v_x_403_, 0);
v_tail_405_ = lean_ctor_get(v_x_403_, 1);
v_isSharedCheck_414_ = !lean_is_exclusive(v_x_403_);
if (v_isSharedCheck_414_ == 0)
{
v___x_407_ = v_x_403_;
v_isShared_408_ = v_isSharedCheck_414_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_tail_405_);
lean_inc(v_head_404_);
lean_dec(v_x_403_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_414_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
lean_inc(v_x_401_);
if (v_isShared_408_ == 0)
{
lean_ctor_set_tag(v___x_407_, 5);
lean_ctor_set(v___x_407_, 1, v_x_401_);
lean_ctor_set(v___x_407_, 0, v_x_402_);
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_x_402_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_x_401_);
v___x_410_ = v_reuseFailAlloc_413_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
lean_object* v___x_411_; 
v___x_411_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set(v___x_411_, 1, v_head_404_);
v_x_402_ = v___x_411_;
v_x_403_ = v_tail_405_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1_spec__2(lean_object* v_x_415_, lean_object* v_x_416_){
_start:
{
if (lean_obj_tag(v_x_415_) == 0)
{
lean_object* v___x_417_; 
lean_dec(v_x_416_);
v___x_417_ = lean_box(0);
return v___x_417_;
}
else
{
lean_object* v_tail_418_; 
v_tail_418_ = lean_ctor_get(v_x_415_, 1);
if (lean_obj_tag(v_tail_418_) == 0)
{
lean_object* v_head_419_; 
lean_dec(v_x_416_);
v_head_419_ = lean_ctor_get(v_x_415_, 0);
lean_inc(v_head_419_);
lean_dec_ref_known(v_x_415_, 2);
return v_head_419_;
}
else
{
lean_object* v_head_420_; lean_object* v___x_421_; 
lean_inc(v_tail_418_);
v_head_420_ = lean_ctor_get(v_x_415_, 0);
lean_inc(v_head_420_);
lean_dec_ref_known(v_x_415_, 2);
v___x_421_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1_spec__2_spec__3(v_x_416_, v_head_420_, v_tail_418_);
return v___x_421_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__0));
v___x_428_ = lean_string_length(v___x_427_);
return v___x_428_;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__3, &l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__3_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__3);
v___x_430_ = lean_nat_to_int(v___x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg(lean_object* v_x_435_){
_start:
{
lean_object* v_fst_436_; lean_object* v_snd_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_460_; 
v_fst_436_ = lean_ctor_get(v_x_435_, 0);
v_snd_437_ = lean_ctor_get(v_x_435_, 1);
v_isSharedCheck_460_ = !lean_is_exclusive(v_x_435_);
if (v_isSharedCheck_460_ == 0)
{
v___x_439_ = v_x_435_;
v_isShared_440_ = v_isSharedCheck_460_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_snd_437_);
lean_inc(v_fst_436_);
lean_dec(v_x_435_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_460_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_445_; 
v___x_441_ = lean_unsigned_to_nat(0u);
v___x_442_ = l_Lean_Name_reprPrec(v_fst_436_, v___x_441_);
v___x_443_ = lean_box(0);
if (v_isShared_440_ == 0)
{
lean_ctor_set_tag(v___x_439_, 1);
lean_ctor_set(v___x_439_, 1, v___x_443_);
lean_ctor_set(v___x_439_, 0, v___x_442_);
v___x_445_ = v___x_439_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v___x_443_);
v___x_445_ = v_reuseFailAlloc_459_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; lean_object* v___x_458_; 
v___x_446_ = l_Lean_instReprLeanOptionValue_repr(v_snd_437_, v___x_441_);
v___x_447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
lean_ctor_set(v___x_447_, 1, v___x_445_);
v___x_448_ = l_List_reverse___redArg(v___x_447_);
v___x_449_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__1));
v___x_450_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1_spec__2(v___x_448_, v___x_449_);
v___x_451_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__4, &l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__4_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__4);
v___x_452_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__5));
v___x_453_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
lean_ctor_set(v___x_453_, 1, v___x_450_);
v___x_454_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__6));
v___x_455_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_453_);
lean_ctor_set(v___x_455_, 1, v___x_454_);
v___x_456_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_451_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
v___x_457_ = 0;
v___x_458_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_458_, 0, v___x_456_);
lean_ctor_set_uint8(v___x_458_, sizeof(void*)*1, v___x_457_);
return v___x_458_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__2_spec__4_spec__6(lean_object* v_x_461_, lean_object* v_x_462_, lean_object* v_x_463_){
_start:
{
if (lean_obj_tag(v_x_463_) == 0)
{
lean_dec(v_x_461_);
return v_x_462_;
}
else
{
lean_object* v_head_464_; lean_object* v_tail_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_475_; 
v_head_464_ = lean_ctor_get(v_x_463_, 0);
v_tail_465_ = lean_ctor_get(v_x_463_, 1);
v_isSharedCheck_475_ = !lean_is_exclusive(v_x_463_);
if (v_isSharedCheck_475_ == 0)
{
v___x_467_ = v_x_463_;
v_isShared_468_ = v_isSharedCheck_475_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_tail_465_);
lean_inc(v_head_464_);
lean_dec(v_x_463_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_475_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
lean_inc(v_x_461_);
if (v_isShared_468_ == 0)
{
lean_ctor_set_tag(v___x_467_, 5);
lean_ctor_set(v___x_467_, 1, v_x_461_);
lean_ctor_set(v___x_467_, 0, v_x_462_);
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_x_462_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_x_461_);
v___x_470_ = v_reuseFailAlloc_474_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg(v_head_464_);
v___x_472_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_470_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
v_x_462_ = v___x_472_;
v_x_463_ = v_tail_465_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__2_spec__4(lean_object* v_x_476_, lean_object* v_x_477_, lean_object* v_x_478_){
_start:
{
if (lean_obj_tag(v_x_478_) == 0)
{
lean_dec(v_x_476_);
return v_x_477_;
}
else
{
lean_object* v_head_479_; lean_object* v_tail_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_490_; 
v_head_479_ = lean_ctor_get(v_x_478_, 0);
v_tail_480_ = lean_ctor_get(v_x_478_, 1);
v_isSharedCheck_490_ = !lean_is_exclusive(v_x_478_);
if (v_isSharedCheck_490_ == 0)
{
v___x_482_ = v_x_478_;
v_isShared_483_ = v_isSharedCheck_490_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_tail_480_);
lean_inc(v_head_479_);
lean_dec(v_x_478_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_490_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
lean_inc(v_x_476_);
if (v_isShared_483_ == 0)
{
lean_ctor_set_tag(v___x_482_, 5);
lean_ctor_set(v___x_482_, 1, v_x_476_);
lean_ctor_set(v___x_482_, 0, v_x_477_);
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_x_477_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v_x_476_);
v___x_485_ = v_reuseFailAlloc_489_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_486_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg(v_head_479_);
v___x_487_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_485_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
v___x_488_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__2_spec__4_spec__6(v_x_476_, v___x_487_, v_tail_480_);
return v___x_488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__2(lean_object* v_x_491_, lean_object* v_x_492_){
_start:
{
if (lean_obj_tag(v_x_491_) == 0)
{
lean_object* v___x_493_; 
lean_dec(v_x_492_);
v___x_493_ = lean_box(0);
return v___x_493_;
}
else
{
lean_object* v_tail_494_; 
v_tail_494_ = lean_ctor_get(v_x_491_, 1);
if (lean_obj_tag(v_tail_494_) == 0)
{
lean_object* v_head_495_; lean_object* v___x_496_; 
lean_dec(v_x_492_);
v_head_495_ = lean_ctor_get(v_x_491_, 0);
lean_inc(v_head_495_);
lean_dec_ref_known(v_x_491_, 2);
v___x_496_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg(v_head_495_);
return v___x_496_;
}
else
{
lean_object* v_head_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
lean_inc(v_tail_494_);
v_head_497_ = lean_ctor_get(v_x_491_, 0);
lean_inc(v_head_497_);
lean_dec_ref_known(v_x_491_, 2);
v___x_498_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg(v_head_497_);
v___x_499_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__2_spec__4(v_x_492_, v___x_498_, v_tail_494_);
return v___x_499_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = ((lean_object*)(l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__2));
v___x_506_ = lean_string_length(v___x_505_);
return v___x_506_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = lean_obj_once(&l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__4, &l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__4_once, _init_l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__4);
v___x_508_ = lean_nat_to_int(v___x_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg(lean_object* v_a_513_){
_start:
{
if (lean_obj_tag(v_a_513_) == 0)
{
lean_object* v___x_514_; 
v___x_514_ = ((lean_object*)(l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__1));
return v___x_514_;
}
else
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; lean_object* v___x_524_; 
v___x_515_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__1));
v___x_516_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__2(v_a_513_, v___x_515_);
v___x_517_ = lean_obj_once(&l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__5, &l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__5_once, _init_l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__5);
v___x_518_ = ((lean_object*)(l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__6));
v___x_519_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
lean_ctor_set(v___x_519_, 1, v___x_516_);
v___x_520_ = ((lean_object*)(l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__7));
v___x_521_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_519_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v___x_522_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_517_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
v___x_523_ = 0;
v___x_524_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_524_, 0, v___x_522_);
lean_ctor_set_uint8(v___x_524_, sizeof(void*)*1, v___x_523_);
return v___x_524_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprLeanOptions_repr_spec__0(lean_object* v_init_525_, lean_object* v_x_526_){
_start:
{
if (lean_obj_tag(v_x_526_) == 0)
{
lean_object* v_k_527_; lean_object* v_v_528_; lean_object* v_l_529_; lean_object* v_r_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v_k_527_ = lean_ctor_get(v_x_526_, 1);
v_v_528_ = lean_ctor_get(v_x_526_, 2);
v_l_529_ = lean_ctor_get(v_x_526_, 3);
v_r_530_ = lean_ctor_get(v_x_526_, 4);
v___x_531_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprLeanOptions_repr_spec__0(v_init_525_, v_r_530_);
lean_inc(v_v_528_);
lean_inc(v_k_527_);
v___x_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_532_, 0, v_k_527_);
lean_ctor_set(v___x_532_, 1, v_v_528_);
v___x_533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
lean_ctor_set(v___x_533_, 1, v___x_531_);
v_init_525_ = v___x_533_;
v_x_526_ = v_l_529_;
goto _start;
}
else
{
return v_init_525_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprLeanOptions_repr_spec__0___boxed(lean_object* v_init_535_, lean_object* v_x_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprLeanOptions_repr_spec__0(v_init_535_, v_x_536_);
lean_dec(v_x_536_);
return v_res_537_;
}
}
static lean_object* _init_l_Lean_instReprLeanOptions_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_unsigned_to_nat(10u);
v___x_548_ = lean_nat_to_int(v___x_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLeanOptions_repr___redArg(lean_object* v_x_552_){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_553_ = ((lean_object*)(l_Lean_instReprLeanOptions_repr___redArg___closed__3));
v___x_554_ = lean_obj_once(&l_Lean_instReprLeanOptions_repr___redArg___closed__4, &l_Lean_instReprLeanOptions_repr___redArg___closed__4_once, _init_l_Lean_instReprLeanOptions_repr___redArg___closed__4);
v___x_555_ = lean_unsigned_to_nat(0u);
v___x_556_ = ((lean_object*)(l_Lean_instReprLeanOptions_repr___redArg___closed__6));
v___x_557_ = lean_box(0);
v___x_558_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprLeanOptions_repr_spec__0(v___x_557_, v_x_552_);
v___x_559_ = l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg(v___x_558_);
v___x_560_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_556_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
v___x_561_ = l_Repr_addAppParen(v___x_560_, v___x_555_);
v___x_562_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_554_);
lean_ctor_set(v___x_562_, 1, v___x_561_);
v___x_563_ = 0;
v___x_564_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_564_, 0, v___x_562_);
lean_ctor_set_uint8(v___x_564_, sizeof(void*)*1, v___x_563_);
v___x_565_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_553_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
v___x_566_ = lean_obj_once(&l_Lean_instReprLeanOption_repr___redArg___closed__15, &l_Lean_instReprLeanOption_repr___redArg___closed__15_once, _init_l_Lean_instReprLeanOption_repr___redArg___closed__15);
v___x_567_ = ((lean_object*)(l_Lean_instReprLeanOption_repr___redArg___closed__16));
v___x_568_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
lean_ctor_set(v___x_568_, 1, v___x_565_);
v___x_569_ = ((lean_object*)(l_Lean_instReprLeanOption_repr___redArg___closed__17));
v___x_570_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_568_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_566_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
v___x_572_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_572_, 0, v___x_571_);
lean_ctor_set_uint8(v___x_572_, sizeof(void*)*1, v___x_563_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLeanOptions_repr___redArg___boxed(lean_object* v_x_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lean_instReprLeanOptions_repr___redArg(v_x_573_);
lean_dec(v_x_573_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLeanOptions_repr(lean_object* v_x_575_, lean_object* v_prec_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Lean_instReprLeanOptions_repr___redArg(v_x_575_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLeanOptions_repr___boxed(lean_object* v_x_578_, lean_object* v_prec_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_instReprLeanOptions_repr(v_x_578_, v_prec_579_);
lean_dec(v_prec_579_);
lean_dec(v_x_578_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1(lean_object* v_a_581_, lean_object* v_n_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg(v_a_581_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___boxed(lean_object* v_a_584_, lean_object* v_n_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1(v_a_584_, v_n_585_);
lean_dec(v_n_585_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1(lean_object* v_x_587_, lean_object* v_x_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg(v_x_587_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___boxed(lean_object* v_x_590_, lean_object* v_x_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1(v_x_590_, v_x_591_);
lean_dec(v_x_591_);
return v_res_592_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionLeanOptions(void){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = lean_box(1);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LeanOptions_ofArray_spec__0(lean_object* v_as_596_, size_t v_i_597_, size_t v_stop_598_, lean_object* v_b_599_){
_start:
{
uint8_t v___x_600_; 
v___x_600_ = lean_usize_dec_eq(v_i_597_, v_stop_598_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; lean_object* v_name_602_; lean_object* v_value_603_; lean_object* v___x_604_; size_t v___x_605_; size_t v___x_606_; 
v___x_601_ = lean_array_uget_borrowed(v_as_596_, v_i_597_);
v_name_602_ = lean_ctor_get(v___x_601_, 0);
v_value_603_ = lean_ctor_get(v___x_601_, 1);
lean_inc_ref(v_value_603_);
lean_inc(v_name_602_);
v___x_604_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_602_, v_value_603_, v_b_599_);
v___x_605_ = ((size_t)1ULL);
v___x_606_ = lean_usize_add(v_i_597_, v___x_605_);
v_i_597_ = v___x_606_;
v_b_599_ = v___x_604_;
goto _start;
}
else
{
return v_b_599_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LeanOptions_ofArray_spec__0___boxed(lean_object* v_as_608_, lean_object* v_i_609_, lean_object* v_stop_610_, lean_object* v_b_611_){
_start:
{
size_t v_i_boxed_612_; size_t v_stop_boxed_613_; lean_object* v_res_614_; 
v_i_boxed_612_ = lean_unbox_usize(v_i_609_);
lean_dec(v_i_609_);
v_stop_boxed_613_ = lean_unbox_usize(v_stop_610_);
lean_dec(v_stop_610_);
v_res_614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LeanOptions_ofArray_spec__0(v_as_608_, v_i_boxed_612_, v_stop_boxed_613_, v_b_611_);
lean_dec_ref(v_as_608_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptions_ofArray(lean_object* v_opts_615_){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_616_ = lean_box(1);
v___x_617_ = lean_unsigned_to_nat(0u);
v___x_618_ = lean_array_get_size(v_opts_615_);
v___x_619_ = lean_nat_dec_lt(v___x_617_, v___x_618_);
if (v___x_619_ == 0)
{
return v___x_616_;
}
else
{
uint8_t v___x_620_; 
v___x_620_ = lean_nat_dec_le(v___x_618_, v___x_618_);
if (v___x_620_ == 0)
{
if (v___x_619_ == 0)
{
return v___x_616_;
}
else
{
size_t v___x_621_; size_t v___x_622_; lean_object* v___x_623_; 
v___x_621_ = ((size_t)0ULL);
v___x_622_ = lean_usize_of_nat(v___x_618_);
v___x_623_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LeanOptions_ofArray_spec__0(v_opts_615_, v___x_621_, v___x_622_, v___x_616_);
return v___x_623_;
}
}
else
{
size_t v___x_624_; size_t v___x_625_; lean_object* v___x_626_; 
v___x_624_ = ((size_t)0ULL);
v___x_625_ = lean_usize_of_nat(v___x_618_);
v___x_626_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LeanOptions_ofArray_spec__0(v_opts_615_, v___x_624_, v___x_625_, v___x_616_);
return v___x_626_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptions_ofArray___boxed(lean_object* v_opts_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lean_LeanOptions_ofArray(v_opts_627_);
lean_dec_ref(v_opts_627_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LeanOptions_append_spec__0___redArg(lean_object* v_b_u2082_629_, lean_object* v_k_630_, lean_object* v_t_631_){
_start:
{
if (lean_obj_tag(v_t_631_) == 0)
{
lean_object* v_size_632_; lean_object* v_k_633_; lean_object* v_v_634_; lean_object* v_l_635_; lean_object* v_r_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_648_; 
v_size_632_ = lean_ctor_get(v_t_631_, 0);
v_k_633_ = lean_ctor_get(v_t_631_, 1);
v_v_634_ = lean_ctor_get(v_t_631_, 2);
v_l_635_ = lean_ctor_get(v_t_631_, 3);
v_r_636_ = lean_ctor_get(v_t_631_, 4);
v_isSharedCheck_648_ = !lean_is_exclusive(v_t_631_);
if (v_isSharedCheck_648_ == 0)
{
v___x_638_ = v_t_631_;
v_isShared_639_ = v_isSharedCheck_648_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_r_636_);
lean_inc(v_l_635_);
lean_inc(v_v_634_);
lean_inc(v_k_633_);
lean_inc(v_size_632_);
lean_dec(v_t_631_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_648_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
uint8_t v___x_640_; 
v___x_640_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_630_, v_k_633_);
switch(v___x_640_)
{
case 0:
{
lean_object* v_impl_641_; lean_object* v___x_642_; 
lean_del_object(v___x_638_);
lean_dec(v_size_632_);
v_impl_641_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LeanOptions_append_spec__0___redArg(v_b_u2082_629_, v_k_630_, v_l_635_);
v___x_642_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_633_, v_v_634_, v_impl_641_, v_r_636_);
return v___x_642_;
}
case 1:
{
lean_object* v___x_644_; 
lean_dec(v_v_634_);
lean_dec(v_k_633_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 2, v_b_u2082_629_);
lean_ctor_set(v___x_638_, 1, v_k_630_);
v___x_644_ = v___x_638_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_size_632_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v_k_630_);
lean_ctor_set(v_reuseFailAlloc_645_, 2, v_b_u2082_629_);
lean_ctor_set(v_reuseFailAlloc_645_, 3, v_l_635_);
lean_ctor_set(v_reuseFailAlloc_645_, 4, v_r_636_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
default: 
{
lean_object* v_impl_646_; lean_object* v___x_647_; 
lean_del_object(v___x_638_);
lean_dec(v_size_632_);
v_impl_646_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LeanOptions_append_spec__0___redArg(v_b_u2082_629_, v_k_630_, v_r_636_);
v___x_647_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_633_, v_v_634_, v_l_635_, v_impl_646_);
return v___x_647_;
}
}
}
}
else
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_unsigned_to_nat(1u);
v___x_650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
lean_ctor_set(v___x_650_, 1, v_k_630_);
lean_ctor_set(v___x_650_, 2, v_b_u2082_629_);
lean_ctor_set(v___x_650_, 3, v_t_631_);
lean_ctor_set(v___x_650_, 4, v_t_631_);
return v___x_650_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LeanOptions_append_spec__1_spec__1(lean_object* v_init_651_, lean_object* v_x_652_){
_start:
{
if (lean_obj_tag(v_x_652_) == 0)
{
lean_object* v_k_653_; lean_object* v_v_654_; lean_object* v_l_655_; lean_object* v_r_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v_k_653_ = lean_ctor_get(v_x_652_, 1);
lean_inc(v_k_653_);
v_v_654_ = lean_ctor_get(v_x_652_, 2);
lean_inc(v_v_654_);
v_l_655_ = lean_ctor_get(v_x_652_, 3);
lean_inc(v_l_655_);
v_r_656_ = lean_ctor_get(v_x_652_, 4);
lean_inc(v_r_656_);
lean_dec_ref_known(v_x_652_, 5);
v___x_657_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LeanOptions_append_spec__1_spec__1(v_init_651_, v_l_655_);
v___x_658_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LeanOptions_append_spec__0___redArg(v_v_654_, v_k_653_, v___x_657_);
v_init_651_ = v___x_658_;
v_x_652_ = v_r_656_;
goto _start;
}
else
{
return v_init_651_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptions_append(lean_object* v_self_660_, lean_object* v_new_661_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LeanOptions_append_spec__1_spec__1(v_self_660_, v_new_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LeanOptions_append_spec__0(lean_object* v_b_u2082_663_, lean_object* v_k_664_, lean_object* v_t_665_, lean_object* v_hl_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LeanOptions_append_spec__0___redArg(v_b_u2082_663_, v_k_664_, v_t_665_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LeanOptions_append_spec__1(lean_object* v_init_668_, lean_object* v_t_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LeanOptions_append_spec__1_spec__1(v_init_668_, v_t_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptions_appendArray(lean_object* v_self_673_, lean_object* v_new_674_){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
v___x_675_ = lean_unsigned_to_nat(0u);
v___x_676_ = lean_array_get_size(v_new_674_);
v___x_677_ = lean_nat_dec_lt(v___x_675_, v___x_676_);
if (v___x_677_ == 0)
{
return v_self_673_;
}
else
{
uint8_t v___x_678_; 
v___x_678_ = lean_nat_dec_le(v___x_676_, v___x_676_);
if (v___x_678_ == 0)
{
if (v___x_677_ == 0)
{
return v_self_673_;
}
else
{
size_t v___x_679_; size_t v___x_680_; lean_object* v___x_681_; 
v___x_679_ = ((size_t)0ULL);
v___x_680_ = lean_usize_of_nat(v___x_676_);
v___x_681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LeanOptions_ofArray_spec__0(v_new_674_, v___x_679_, v___x_680_, v_self_673_);
return v___x_681_;
}
}
else
{
size_t v___x_682_; size_t v___x_683_; lean_object* v___x_684_; 
v___x_682_ = ((size_t)0ULL);
v___x_683_ = lean_usize_of_nat(v___x_676_);
v___x_684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LeanOptions_ofArray_spec__0(v_new_674_, v___x_682_, v___x_683_, v_self_673_);
return v___x_684_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptions_appendArray___boxed(lean_object* v_self_685_, lean_object* v_new_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_LeanOptions_appendArray(v_self_685_, v_new_686_);
lean_dec_ref(v_new_686_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0(lean_object* v_o_693_, lean_object* v_k_694_, lean_object* v_v_695_){
_start:
{
lean_object* v_map_696_; uint8_t v_hasTrace_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_710_; 
v_map_696_ = lean_ctor_get(v_o_693_, 0);
v_hasTrace_697_ = lean_ctor_get_uint8(v_o_693_, sizeof(void*)*1);
v_isSharedCheck_710_ = !lean_is_exclusive(v_o_693_);
if (v_isSharedCheck_710_ == 0)
{
v___x_699_ = v_o_693_;
v_isShared_700_ = v_isSharedCheck_710_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_map_696_);
lean_dec(v_o_693_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_710_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; 
lean_inc(v_k_694_);
v___x_701_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_694_, v_v_695_, v_map_696_);
if (v_hasTrace_697_ == 0)
{
lean_object* v___x_702_; uint8_t v___x_703_; lean_object* v___x_705_; 
v___x_702_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0___closed__1));
v___x_703_ = l_Lean_Name_isPrefixOf(v___x_702_, v_k_694_);
lean_dec(v_k_694_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 0, v___x_701_);
v___x_705_ = v___x_699_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_701_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
lean_ctor_set_uint8(v___x_705_, sizeof(void*)*1, v___x_703_);
return v___x_705_;
}
}
else
{
lean_object* v___x_708_; 
lean_dec(v_k_694_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 0, v___x_701_);
v___x_708_ = v___x_699_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_701_);
lean_ctor_set_uint8(v_reuseFailAlloc_709_, sizeof(void*)*1, v_hasTrace_697_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_LeanOptions_toOptions_spec__1(lean_object* v_init_711_, lean_object* v_x_712_){
_start:
{
if (lean_obj_tag(v_x_712_) == 0)
{
lean_object* v_k_713_; lean_object* v_v_714_; lean_object* v_l_715_; lean_object* v_r_716_; lean_object* v___x_717_; lean_object* v_a_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v_k_713_ = lean_ctor_get(v_x_712_, 1);
lean_inc(v_k_713_);
v_v_714_ = lean_ctor_get(v_x_712_, 2);
lean_inc(v_v_714_);
v_l_715_ = lean_ctor_get(v_x_712_, 3);
lean_inc(v_l_715_);
v_r_716_ = lean_ctor_get(v_x_712_, 4);
lean_inc(v_r_716_);
lean_dec_ref_known(v_x_712_, 5);
v___x_717_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_LeanOptions_toOptions_spec__1(v_init_711_, v_l_715_);
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
lean_dec_ref(v___x_717_);
v___x_719_ = l_Lean_LeanOptionValue_toDataValue(v_v_714_);
v___x_720_ = l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0(v_a_718_, v_k_713_, v___x_719_);
v_init_711_ = v___x_720_;
v_x_712_ = v_r_716_;
goto _start;
}
else
{
lean_object* v___x_722_; 
v___x_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_722_, 0, v_init_711_);
return v___x_722_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptions_toOptions(lean_object* v_leanOptions_723_){
_start:
{
lean_object* v_options_724_; lean_object* v___x_725_; lean_object* v_a_726_; 
v_options_724_ = l_Lean_Options_empty;
v___x_725_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_LeanOptions_toOptions_spec__1(v_options_724_, v_leanOptions_723_);
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref(v___x_725_);
return v_a_726_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_LeanOptions_fromOptions_x3f_spec__0___redArg(lean_object* v_k_727_, lean_object* v_v_728_, lean_object* v_t_729_){
_start:
{
if (lean_obj_tag(v_t_729_) == 0)
{
lean_object* v_size_730_; lean_object* v_k_731_; lean_object* v_v_732_; lean_object* v_l_733_; lean_object* v_r_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_1014_; 
v_size_730_ = lean_ctor_get(v_t_729_, 0);
v_k_731_ = lean_ctor_get(v_t_729_, 1);
v_v_732_ = lean_ctor_get(v_t_729_, 2);
v_l_733_ = lean_ctor_get(v_t_729_, 3);
v_r_734_ = lean_ctor_get(v_t_729_, 4);
v_isSharedCheck_1014_ = !lean_is_exclusive(v_t_729_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_736_ = v_t_729_;
v_isShared_737_ = v_isSharedCheck_1014_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_r_734_);
lean_inc(v_l_733_);
lean_inc(v_v_732_);
lean_inc(v_k_731_);
lean_inc(v_size_730_);
lean_dec(v_t_729_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_1014_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
uint8_t v___x_738_; 
v___x_738_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_727_, v_k_731_);
switch(v___x_738_)
{
case 0:
{
lean_object* v_impl_739_; lean_object* v___x_740_; 
lean_dec(v_size_730_);
v_impl_739_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_LeanOptions_fromOptions_x3f_spec__0___redArg(v_k_727_, v_v_728_, v_l_733_);
v___x_740_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_734_) == 0)
{
lean_object* v_size_741_; lean_object* v_size_742_; lean_object* v_k_743_; lean_object* v_v_744_; lean_object* v_l_745_; lean_object* v_r_746_; lean_object* v___x_747_; lean_object* v___x_748_; uint8_t v___x_749_; 
v_size_741_ = lean_ctor_get(v_r_734_, 0);
v_size_742_ = lean_ctor_get(v_impl_739_, 0);
v_k_743_ = lean_ctor_get(v_impl_739_, 1);
v_v_744_ = lean_ctor_get(v_impl_739_, 2);
v_l_745_ = lean_ctor_get(v_impl_739_, 3);
v_r_746_ = lean_ctor_get(v_impl_739_, 4);
lean_inc(v_r_746_);
v___x_747_ = lean_unsigned_to_nat(3u);
v___x_748_ = lean_nat_mul(v___x_747_, v_size_741_);
v___x_749_ = lean_nat_dec_lt(v___x_748_, v_size_742_);
lean_dec(v___x_748_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_753_; 
lean_dec(v_r_746_);
v___x_750_ = lean_nat_add(v___x_740_, v_size_742_);
v___x_751_ = lean_nat_add(v___x_750_, v_size_741_);
lean_dec(v___x_750_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 3, v_impl_739_);
lean_ctor_set(v___x_736_, 0, v___x_751_);
v___x_753_ = v___x_736_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_k_731_);
lean_ctor_set(v_reuseFailAlloc_754_, 2, v_v_732_);
lean_ctor_set(v_reuseFailAlloc_754_, 3, v_impl_739_);
lean_ctor_set(v_reuseFailAlloc_754_, 4, v_r_734_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
else
{
lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_820_; 
lean_inc(v_l_745_);
lean_inc(v_v_744_);
lean_inc(v_k_743_);
lean_inc(v_size_742_);
v_isSharedCheck_820_ = !lean_is_exclusive(v_impl_739_);
if (v_isSharedCheck_820_ == 0)
{
lean_object* v_unused_821_; lean_object* v_unused_822_; lean_object* v_unused_823_; lean_object* v_unused_824_; lean_object* v_unused_825_; 
v_unused_821_ = lean_ctor_get(v_impl_739_, 4);
lean_dec(v_unused_821_);
v_unused_822_ = lean_ctor_get(v_impl_739_, 3);
lean_dec(v_unused_822_);
v_unused_823_ = lean_ctor_get(v_impl_739_, 2);
lean_dec(v_unused_823_);
v_unused_824_ = lean_ctor_get(v_impl_739_, 1);
lean_dec(v_unused_824_);
v_unused_825_ = lean_ctor_get(v_impl_739_, 0);
lean_dec(v_unused_825_);
v___x_756_ = v_impl_739_;
v_isShared_757_ = v_isSharedCheck_820_;
goto v_resetjp_755_;
}
else
{
lean_dec(v_impl_739_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_820_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v_size_758_; lean_object* v_size_759_; lean_object* v_k_760_; lean_object* v_v_761_; lean_object* v_l_762_; lean_object* v_r_763_; lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; 
v_size_758_ = lean_ctor_get(v_l_745_, 0);
v_size_759_ = lean_ctor_get(v_r_746_, 0);
v_k_760_ = lean_ctor_get(v_r_746_, 1);
v_v_761_ = lean_ctor_get(v_r_746_, 2);
v_l_762_ = lean_ctor_get(v_r_746_, 3);
v_r_763_ = lean_ctor_get(v_r_746_, 4);
v___x_764_ = lean_unsigned_to_nat(2u);
v___x_765_ = lean_nat_mul(v___x_764_, v_size_758_);
v___x_766_ = lean_nat_dec_lt(v_size_759_, v___x_765_);
lean_dec(v___x_765_);
if (v___x_766_ == 0)
{
lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_795_; 
lean_inc(v_r_763_);
lean_inc(v_l_762_);
lean_inc(v_v_761_);
lean_inc(v_k_760_);
v_isSharedCheck_795_ = !lean_is_exclusive(v_r_746_);
if (v_isSharedCheck_795_ == 0)
{
lean_object* v_unused_796_; lean_object* v_unused_797_; lean_object* v_unused_798_; lean_object* v_unused_799_; lean_object* v_unused_800_; 
v_unused_796_ = lean_ctor_get(v_r_746_, 4);
lean_dec(v_unused_796_);
v_unused_797_ = lean_ctor_get(v_r_746_, 3);
lean_dec(v_unused_797_);
v_unused_798_ = lean_ctor_get(v_r_746_, 2);
lean_dec(v_unused_798_);
v_unused_799_ = lean_ctor_get(v_r_746_, 1);
lean_dec(v_unused_799_);
v_unused_800_ = lean_ctor_get(v_r_746_, 0);
lean_dec(v_unused_800_);
v___x_768_ = v_r_746_;
v_isShared_769_ = v_isSharedCheck_795_;
goto v_resetjp_767_;
}
else
{
lean_dec(v_r_746_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_795_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___x_783_; lean_object* v___y_785_; 
v___x_770_ = lean_nat_add(v___x_740_, v_size_742_);
lean_dec(v_size_742_);
v___x_771_ = lean_nat_add(v___x_770_, v_size_741_);
lean_dec(v___x_770_);
v___x_783_ = lean_nat_add(v___x_740_, v_size_758_);
if (lean_obj_tag(v_l_762_) == 0)
{
lean_object* v_size_793_; 
v_size_793_ = lean_ctor_get(v_l_762_, 0);
lean_inc(v_size_793_);
v___y_785_ = v_size_793_;
goto v___jp_784_;
}
else
{
lean_object* v___x_794_; 
v___x_794_ = lean_unsigned_to_nat(0u);
v___y_785_ = v___x_794_;
goto v___jp_784_;
}
v___jp_772_:
{
lean_object* v___x_776_; lean_object* v___x_778_; 
v___x_776_ = lean_nat_add(v___y_773_, v___y_775_);
lean_dec(v___y_775_);
lean_dec(v___y_773_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 4, v_r_734_);
lean_ctor_set(v___x_768_, 3, v_r_763_);
lean_ctor_set(v___x_768_, 2, v_v_732_);
lean_ctor_set(v___x_768_, 1, v_k_731_);
lean_ctor_set(v___x_768_, 0, v___x_776_);
v___x_778_ = v___x_768_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_k_731_);
lean_ctor_set(v_reuseFailAlloc_782_, 2, v_v_732_);
lean_ctor_set(v_reuseFailAlloc_782_, 3, v_r_763_);
lean_ctor_set(v_reuseFailAlloc_782_, 4, v_r_734_);
v___x_778_ = v_reuseFailAlloc_782_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
lean_object* v___x_780_; 
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 4, v___x_778_);
lean_ctor_set(v___x_756_, 3, v___y_774_);
lean_ctor_set(v___x_756_, 2, v_v_761_);
lean_ctor_set(v___x_756_, 1, v_k_760_);
lean_ctor_set(v___x_756_, 0, v___x_771_);
v___x_780_ = v___x_756_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_k_760_);
lean_ctor_set(v_reuseFailAlloc_781_, 2, v_v_761_);
lean_ctor_set(v_reuseFailAlloc_781_, 3, v___y_774_);
lean_ctor_set(v_reuseFailAlloc_781_, 4, v___x_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
v___jp_784_:
{
lean_object* v___x_786_; lean_object* v___x_788_; 
v___x_786_ = lean_nat_add(v___x_783_, v___y_785_);
lean_dec(v___y_785_);
lean_dec(v___x_783_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 4, v_l_762_);
lean_ctor_set(v___x_736_, 3, v_l_745_);
lean_ctor_set(v___x_736_, 2, v_v_744_);
lean_ctor_set(v___x_736_, 1, v_k_743_);
lean_ctor_set(v___x_736_, 0, v___x_786_);
v___x_788_ = v___x_736_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_k_743_);
lean_ctor_set(v_reuseFailAlloc_792_, 2, v_v_744_);
lean_ctor_set(v_reuseFailAlloc_792_, 3, v_l_745_);
lean_ctor_set(v_reuseFailAlloc_792_, 4, v_l_762_);
v___x_788_ = v_reuseFailAlloc_792_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
lean_object* v___x_789_; 
v___x_789_ = lean_nat_add(v___x_740_, v_size_741_);
if (lean_obj_tag(v_r_763_) == 0)
{
lean_object* v_size_790_; 
v_size_790_ = lean_ctor_get(v_r_763_, 0);
lean_inc(v_size_790_);
v___y_773_ = v___x_789_;
v___y_774_ = v___x_788_;
v___y_775_ = v_size_790_;
goto v___jp_772_;
}
else
{
lean_object* v___x_791_; 
v___x_791_ = lean_unsigned_to_nat(0u);
v___y_773_ = v___x_789_;
v___y_774_ = v___x_788_;
v___y_775_ = v___x_791_;
goto v___jp_772_;
}
}
}
}
}
else
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_806_; 
lean_del_object(v___x_736_);
v___x_801_ = lean_nat_add(v___x_740_, v_size_742_);
lean_dec(v_size_742_);
v___x_802_ = lean_nat_add(v___x_801_, v_size_741_);
lean_dec(v___x_801_);
v___x_803_ = lean_nat_add(v___x_740_, v_size_741_);
v___x_804_ = lean_nat_add(v___x_803_, v_size_759_);
lean_dec(v___x_803_);
lean_inc_ref(v_r_734_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 4, v_r_734_);
lean_ctor_set(v___x_756_, 3, v_r_746_);
lean_ctor_set(v___x_756_, 2, v_v_732_);
lean_ctor_set(v___x_756_, 1, v_k_731_);
lean_ctor_set(v___x_756_, 0, v___x_804_);
v___x_806_ = v___x_756_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_804_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v_k_731_);
lean_ctor_set(v_reuseFailAlloc_819_, 2, v_v_732_);
lean_ctor_set(v_reuseFailAlloc_819_, 3, v_r_746_);
lean_ctor_set(v_reuseFailAlloc_819_, 4, v_r_734_);
v___x_806_ = v_reuseFailAlloc_819_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
v_isSharedCheck_813_ = !lean_is_exclusive(v_r_734_);
if (v_isSharedCheck_813_ == 0)
{
lean_object* v_unused_814_; lean_object* v_unused_815_; lean_object* v_unused_816_; lean_object* v_unused_817_; lean_object* v_unused_818_; 
v_unused_814_ = lean_ctor_get(v_r_734_, 4);
lean_dec(v_unused_814_);
v_unused_815_ = lean_ctor_get(v_r_734_, 3);
lean_dec(v_unused_815_);
v_unused_816_ = lean_ctor_get(v_r_734_, 2);
lean_dec(v_unused_816_);
v_unused_817_ = lean_ctor_get(v_r_734_, 1);
lean_dec(v_unused_817_);
v_unused_818_ = lean_ctor_get(v_r_734_, 0);
lean_dec(v_unused_818_);
v___x_808_ = v_r_734_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_dec(v_r_734_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 4, v___x_806_);
lean_ctor_set(v___x_808_, 3, v_l_745_);
lean_ctor_set(v___x_808_, 2, v_v_744_);
lean_ctor_set(v___x_808_, 1, v_k_743_);
lean_ctor_set(v___x_808_, 0, v___x_802_);
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_802_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_k_743_);
lean_ctor_set(v_reuseFailAlloc_812_, 2, v_v_744_);
lean_ctor_set(v_reuseFailAlloc_812_, 3, v_l_745_);
lean_ctor_set(v_reuseFailAlloc_812_, 4, v___x_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_826_; 
v_l_826_ = lean_ctor_get(v_impl_739_, 3);
if (lean_obj_tag(v_l_826_) == 0)
{
lean_object* v_r_827_; lean_object* v_k_828_; lean_object* v_v_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_840_; 
lean_inc_ref(v_l_826_);
v_r_827_ = lean_ctor_get(v_impl_739_, 4);
v_k_828_ = lean_ctor_get(v_impl_739_, 1);
v_v_829_ = lean_ctor_get(v_impl_739_, 2);
v_isSharedCheck_840_ = !lean_is_exclusive(v_impl_739_);
if (v_isSharedCheck_840_ == 0)
{
lean_object* v_unused_841_; lean_object* v_unused_842_; 
v_unused_841_ = lean_ctor_get(v_impl_739_, 3);
lean_dec(v_unused_841_);
v_unused_842_ = lean_ctor_get(v_impl_739_, 0);
lean_dec(v_unused_842_);
v___x_831_ = v_impl_739_;
v_isShared_832_ = v_isSharedCheck_840_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_r_827_);
lean_inc(v_v_829_);
lean_inc(v_k_828_);
lean_dec(v_impl_739_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_840_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_833_; lean_object* v___x_835_; 
v___x_833_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_827_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 3, v_r_827_);
lean_ctor_set(v___x_831_, 2, v_v_732_);
lean_ctor_set(v___x_831_, 1, v_k_731_);
lean_ctor_set(v___x_831_, 0, v___x_740_);
v___x_835_ = v___x_831_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_740_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v_k_731_);
lean_ctor_set(v_reuseFailAlloc_839_, 2, v_v_732_);
lean_ctor_set(v_reuseFailAlloc_839_, 3, v_r_827_);
lean_ctor_set(v_reuseFailAlloc_839_, 4, v_r_827_);
v___x_835_ = v_reuseFailAlloc_839_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
lean_object* v___x_837_; 
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 4, v___x_835_);
lean_ctor_set(v___x_736_, 3, v_l_826_);
lean_ctor_set(v___x_736_, 2, v_v_829_);
lean_ctor_set(v___x_736_, 1, v_k_828_);
lean_ctor_set(v___x_736_, 0, v___x_833_);
v___x_837_ = v___x_736_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_833_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v_k_828_);
lean_ctor_set(v_reuseFailAlloc_838_, 2, v_v_829_);
lean_ctor_set(v_reuseFailAlloc_838_, 3, v_l_826_);
lean_ctor_set(v_reuseFailAlloc_838_, 4, v___x_835_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
else
{
lean_object* v_r_843_; 
v_r_843_ = lean_ctor_get(v_impl_739_, 4);
lean_inc(v_r_843_);
if (lean_obj_tag(v_r_843_) == 0)
{
lean_object* v_k_844_; lean_object* v_v_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_868_; 
lean_inc(v_l_826_);
v_k_844_ = lean_ctor_get(v_impl_739_, 1);
v_v_845_ = lean_ctor_get(v_impl_739_, 2);
v_isSharedCheck_868_ = !lean_is_exclusive(v_impl_739_);
if (v_isSharedCheck_868_ == 0)
{
lean_object* v_unused_869_; lean_object* v_unused_870_; lean_object* v_unused_871_; 
v_unused_869_ = lean_ctor_get(v_impl_739_, 4);
lean_dec(v_unused_869_);
v_unused_870_ = lean_ctor_get(v_impl_739_, 3);
lean_dec(v_unused_870_);
v_unused_871_ = lean_ctor_get(v_impl_739_, 0);
lean_dec(v_unused_871_);
v___x_847_ = v_impl_739_;
v_isShared_848_ = v_isSharedCheck_868_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_v_845_);
lean_inc(v_k_844_);
lean_dec(v_impl_739_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_868_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v_k_849_; lean_object* v_v_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_864_; 
v_k_849_ = lean_ctor_get(v_r_843_, 1);
v_v_850_ = lean_ctor_get(v_r_843_, 2);
v_isSharedCheck_864_ = !lean_is_exclusive(v_r_843_);
if (v_isSharedCheck_864_ == 0)
{
lean_object* v_unused_865_; lean_object* v_unused_866_; lean_object* v_unused_867_; 
v_unused_865_ = lean_ctor_get(v_r_843_, 4);
lean_dec(v_unused_865_);
v_unused_866_ = lean_ctor_get(v_r_843_, 3);
lean_dec(v_unused_866_);
v_unused_867_ = lean_ctor_get(v_r_843_, 0);
lean_dec(v_unused_867_);
v___x_852_ = v_r_843_;
v_isShared_853_ = v_isSharedCheck_864_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_v_850_);
lean_inc(v_k_849_);
lean_dec(v_r_843_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_864_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_854_; lean_object* v___x_856_; 
v___x_854_ = lean_unsigned_to_nat(3u);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 4, v_l_826_);
lean_ctor_set(v___x_852_, 3, v_l_826_);
lean_ctor_set(v___x_852_, 2, v_v_845_);
lean_ctor_set(v___x_852_, 1, v_k_844_);
lean_ctor_set(v___x_852_, 0, v___x_740_);
v___x_856_ = v___x_852_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_740_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v_k_844_);
lean_ctor_set(v_reuseFailAlloc_863_, 2, v_v_845_);
lean_ctor_set(v_reuseFailAlloc_863_, 3, v_l_826_);
lean_ctor_set(v_reuseFailAlloc_863_, 4, v_l_826_);
v___x_856_ = v_reuseFailAlloc_863_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v___x_858_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 4, v_l_826_);
lean_ctor_set(v___x_847_, 2, v_v_732_);
lean_ctor_set(v___x_847_, 1, v_k_731_);
lean_ctor_set(v___x_847_, 0, v___x_740_);
v___x_858_ = v___x_847_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_740_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v_k_731_);
lean_ctor_set(v_reuseFailAlloc_862_, 2, v_v_732_);
lean_ctor_set(v_reuseFailAlloc_862_, 3, v_l_826_);
lean_ctor_set(v_reuseFailAlloc_862_, 4, v_l_826_);
v___x_858_ = v_reuseFailAlloc_862_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
lean_object* v___x_860_; 
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 4, v___x_858_);
lean_ctor_set(v___x_736_, 3, v___x_856_);
lean_ctor_set(v___x_736_, 2, v_v_850_);
lean_ctor_set(v___x_736_, 1, v_k_849_);
lean_ctor_set(v___x_736_, 0, v___x_854_);
v___x_860_ = v___x_736_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_854_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_k_849_);
lean_ctor_set(v_reuseFailAlloc_861_, 2, v_v_850_);
lean_ctor_set(v_reuseFailAlloc_861_, 3, v___x_856_);
lean_ctor_set(v_reuseFailAlloc_861_, 4, v___x_858_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
}
}
else
{
lean_object* v___x_872_; lean_object* v___x_874_; 
v___x_872_ = lean_unsigned_to_nat(2u);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 4, v_r_843_);
lean_ctor_set(v___x_736_, 3, v_impl_739_);
lean_ctor_set(v___x_736_, 0, v___x_872_);
v___x_874_ = v___x_736_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_k_731_);
lean_ctor_set(v_reuseFailAlloc_875_, 2, v_v_732_);
lean_ctor_set(v_reuseFailAlloc_875_, 3, v_impl_739_);
lean_ctor_set(v_reuseFailAlloc_875_, 4, v_r_843_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
case 1:
{
lean_object* v___x_877_; 
lean_dec(v_v_732_);
lean_dec(v_k_731_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 2, v_v_728_);
lean_ctor_set(v___x_736_, 1, v_k_727_);
v___x_877_ = v___x_736_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_size_730_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v_k_727_);
lean_ctor_set(v_reuseFailAlloc_878_, 2, v_v_728_);
lean_ctor_set(v_reuseFailAlloc_878_, 3, v_l_733_);
lean_ctor_set(v_reuseFailAlloc_878_, 4, v_r_734_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
default: 
{
lean_object* v_impl_879_; lean_object* v___x_880_; 
lean_dec(v_size_730_);
v_impl_879_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_LeanOptions_fromOptions_x3f_spec__0___redArg(v_k_727_, v_v_728_, v_r_734_);
v___x_880_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_733_) == 0)
{
lean_object* v_size_881_; lean_object* v_size_882_; lean_object* v_k_883_; lean_object* v_v_884_; lean_object* v_l_885_; lean_object* v_r_886_; lean_object* v___x_887_; lean_object* v___x_888_; uint8_t v___x_889_; 
v_size_881_ = lean_ctor_get(v_l_733_, 0);
v_size_882_ = lean_ctor_get(v_impl_879_, 0);
v_k_883_ = lean_ctor_get(v_impl_879_, 1);
v_v_884_ = lean_ctor_get(v_impl_879_, 2);
v_l_885_ = lean_ctor_get(v_impl_879_, 3);
lean_inc(v_l_885_);
v_r_886_ = lean_ctor_get(v_impl_879_, 4);
v___x_887_ = lean_unsigned_to_nat(3u);
v___x_888_ = lean_nat_mul(v___x_887_, v_size_881_);
v___x_889_ = lean_nat_dec_lt(v___x_888_, v_size_882_);
lean_dec(v___x_888_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_893_; 
lean_dec(v_l_885_);
v___x_890_ = lean_nat_add(v___x_880_, v_size_881_);
v___x_891_ = lean_nat_add(v___x_890_, v_size_882_);
lean_dec(v___x_890_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 4, v_impl_879_);
lean_ctor_set(v___x_736_, 0, v___x_891_);
v___x_893_ = v___x_736_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_891_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_k_731_);
lean_ctor_set(v_reuseFailAlloc_894_, 2, v_v_732_);
lean_ctor_set(v_reuseFailAlloc_894_, 3, v_l_733_);
lean_ctor_set(v_reuseFailAlloc_894_, 4, v_impl_879_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
else
{
lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_958_; 
lean_inc(v_r_886_);
lean_inc(v_v_884_);
lean_inc(v_k_883_);
lean_inc(v_size_882_);
v_isSharedCheck_958_ = !lean_is_exclusive(v_impl_879_);
if (v_isSharedCheck_958_ == 0)
{
lean_object* v_unused_959_; lean_object* v_unused_960_; lean_object* v_unused_961_; lean_object* v_unused_962_; lean_object* v_unused_963_; 
v_unused_959_ = lean_ctor_get(v_impl_879_, 4);
lean_dec(v_unused_959_);
v_unused_960_ = lean_ctor_get(v_impl_879_, 3);
lean_dec(v_unused_960_);
v_unused_961_ = lean_ctor_get(v_impl_879_, 2);
lean_dec(v_unused_961_);
v_unused_962_ = lean_ctor_get(v_impl_879_, 1);
lean_dec(v_unused_962_);
v_unused_963_ = lean_ctor_get(v_impl_879_, 0);
lean_dec(v_unused_963_);
v___x_896_ = v_impl_879_;
v_isShared_897_ = v_isSharedCheck_958_;
goto v_resetjp_895_;
}
else
{
lean_dec(v_impl_879_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_958_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v_size_898_; lean_object* v_k_899_; lean_object* v_v_900_; lean_object* v_l_901_; lean_object* v_r_902_; lean_object* v_size_903_; lean_object* v___x_904_; lean_object* v___x_905_; uint8_t v___x_906_; 
v_size_898_ = lean_ctor_get(v_l_885_, 0);
v_k_899_ = lean_ctor_get(v_l_885_, 1);
v_v_900_ = lean_ctor_get(v_l_885_, 2);
v_l_901_ = lean_ctor_get(v_l_885_, 3);
v_r_902_ = lean_ctor_get(v_l_885_, 4);
v_size_903_ = lean_ctor_get(v_r_886_, 0);
v___x_904_ = lean_unsigned_to_nat(2u);
v___x_905_ = lean_nat_mul(v___x_904_, v_size_903_);
v___x_906_ = lean_nat_dec_lt(v_size_898_, v___x_905_);
lean_dec(v___x_905_);
if (v___x_906_ == 0)
{
lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_934_; 
lean_inc(v_r_902_);
lean_inc(v_l_901_);
lean_inc(v_v_900_);
lean_inc(v_k_899_);
v_isSharedCheck_934_ = !lean_is_exclusive(v_l_885_);
if (v_isSharedCheck_934_ == 0)
{
lean_object* v_unused_935_; lean_object* v_unused_936_; lean_object* v_unused_937_; lean_object* v_unused_938_; lean_object* v_unused_939_; 
v_unused_935_ = lean_ctor_get(v_l_885_, 4);
lean_dec(v_unused_935_);
v_unused_936_ = lean_ctor_get(v_l_885_, 3);
lean_dec(v_unused_936_);
v_unused_937_ = lean_ctor_get(v_l_885_, 2);
lean_dec(v_unused_937_);
v_unused_938_ = lean_ctor_get(v_l_885_, 1);
lean_dec(v_unused_938_);
v_unused_939_ = lean_ctor_get(v_l_885_, 0);
lean_dec(v_unused_939_);
v___x_908_ = v_l_885_;
v_isShared_909_ = v_isSharedCheck_934_;
goto v_resetjp_907_;
}
else
{
lean_dec(v_l_885_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_934_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___y_924_; 
v___x_910_ = lean_nat_add(v___x_880_, v_size_881_);
v___x_911_ = lean_nat_add(v___x_910_, v_size_882_);
lean_dec(v_size_882_);
if (lean_obj_tag(v_l_901_) == 0)
{
lean_object* v_size_932_; 
v_size_932_ = lean_ctor_get(v_l_901_, 0);
lean_inc(v_size_932_);
v___y_924_ = v_size_932_;
goto v___jp_923_;
}
else
{
lean_object* v___x_933_; 
v___x_933_ = lean_unsigned_to_nat(0u);
v___y_924_ = v___x_933_;
goto v___jp_923_;
}
v___jp_912_:
{
lean_object* v___x_916_; lean_object* v___x_918_; 
v___x_916_ = lean_nat_add(v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec(v___y_914_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 4, v_r_886_);
lean_ctor_set(v___x_908_, 3, v_r_902_);
lean_ctor_set(v___x_908_, 2, v_v_884_);
lean_ctor_set(v___x_908_, 1, v_k_883_);
lean_ctor_set(v___x_908_, 0, v___x_916_);
v___x_918_ = v___x_908_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_916_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_k_883_);
lean_ctor_set(v_reuseFailAlloc_922_, 2, v_v_884_);
lean_ctor_set(v_reuseFailAlloc_922_, 3, v_r_902_);
lean_ctor_set(v_reuseFailAlloc_922_, 4, v_r_886_);
v___x_918_ = v_reuseFailAlloc_922_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
lean_object* v___x_920_; 
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 4, v___x_918_);
lean_ctor_set(v___x_896_, 3, v___y_913_);
lean_ctor_set(v___x_896_, 2, v_v_900_);
lean_ctor_set(v___x_896_, 1, v_k_899_);
lean_ctor_set(v___x_896_, 0, v___x_911_);
v___x_920_ = v___x_896_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_911_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_k_899_);
lean_ctor_set(v_reuseFailAlloc_921_, 2, v_v_900_);
lean_ctor_set(v_reuseFailAlloc_921_, 3, v___y_913_);
lean_ctor_set(v_reuseFailAlloc_921_, 4, v___x_918_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
v___jp_923_:
{
lean_object* v___x_925_; lean_object* v___x_927_; 
v___x_925_ = lean_nat_add(v___x_910_, v___y_924_);
lean_dec(v___y_924_);
lean_dec(v___x_910_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 4, v_l_901_);
lean_ctor_set(v___x_736_, 0, v___x_925_);
v___x_927_ = v___x_736_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_925_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v_k_731_);
lean_ctor_set(v_reuseFailAlloc_931_, 2, v_v_732_);
lean_ctor_set(v_reuseFailAlloc_931_, 3, v_l_733_);
lean_ctor_set(v_reuseFailAlloc_931_, 4, v_l_901_);
v___x_927_ = v_reuseFailAlloc_931_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
lean_object* v___x_928_; 
v___x_928_ = lean_nat_add(v___x_880_, v_size_903_);
if (lean_obj_tag(v_r_902_) == 0)
{
lean_object* v_size_929_; 
v_size_929_ = lean_ctor_get(v_r_902_, 0);
lean_inc(v_size_929_);
v___y_913_ = v___x_927_;
v___y_914_ = v___x_928_;
v___y_915_ = v_size_929_;
goto v___jp_912_;
}
else
{
lean_object* v___x_930_; 
v___x_930_ = lean_unsigned_to_nat(0u);
v___y_913_ = v___x_927_;
v___y_914_ = v___x_928_;
v___y_915_ = v___x_930_;
goto v___jp_912_;
}
}
}
}
}
else
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_944_; 
lean_del_object(v___x_736_);
v___x_940_ = lean_nat_add(v___x_880_, v_size_881_);
v___x_941_ = lean_nat_add(v___x_940_, v_size_882_);
lean_dec(v_size_882_);
v___x_942_ = lean_nat_add(v___x_940_, v_size_898_);
lean_dec(v___x_940_);
lean_inc_ref(v_l_733_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 4, v_l_885_);
lean_ctor_set(v___x_896_, 3, v_l_733_);
lean_ctor_set(v___x_896_, 2, v_v_732_);
lean_ctor_set(v___x_896_, 1, v_k_731_);
lean_ctor_set(v___x_896_, 0, v___x_942_);
v___x_944_ = v___x_896_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_k_731_);
lean_ctor_set(v_reuseFailAlloc_957_, 2, v_v_732_);
lean_ctor_set(v_reuseFailAlloc_957_, 3, v_l_733_);
lean_ctor_set(v_reuseFailAlloc_957_, 4, v_l_885_);
v___x_944_ = v_reuseFailAlloc_957_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_951_; 
v_isSharedCheck_951_ = !lean_is_exclusive(v_l_733_);
if (v_isSharedCheck_951_ == 0)
{
lean_object* v_unused_952_; lean_object* v_unused_953_; lean_object* v_unused_954_; lean_object* v_unused_955_; lean_object* v_unused_956_; 
v_unused_952_ = lean_ctor_get(v_l_733_, 4);
lean_dec(v_unused_952_);
v_unused_953_ = lean_ctor_get(v_l_733_, 3);
lean_dec(v_unused_953_);
v_unused_954_ = lean_ctor_get(v_l_733_, 2);
lean_dec(v_unused_954_);
v_unused_955_ = lean_ctor_get(v_l_733_, 1);
lean_dec(v_unused_955_);
v_unused_956_ = lean_ctor_get(v_l_733_, 0);
lean_dec(v_unused_956_);
v___x_946_ = v_l_733_;
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
else
{
lean_dec(v_l_733_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 4, v_r_886_);
lean_ctor_set(v___x_946_, 3, v___x_944_);
lean_ctor_set(v___x_946_, 2, v_v_884_);
lean_ctor_set(v___x_946_, 1, v_k_883_);
lean_ctor_set(v___x_946_, 0, v___x_941_);
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_k_883_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_v_884_);
lean_ctor_set(v_reuseFailAlloc_950_, 3, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_950_, 4, v_r_886_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_964_; 
v_l_964_ = lean_ctor_get(v_impl_879_, 3);
lean_inc(v_l_964_);
if (lean_obj_tag(v_l_964_) == 0)
{
lean_object* v_r_965_; lean_object* v_k_966_; lean_object* v_v_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_990_; 
v_r_965_ = lean_ctor_get(v_impl_879_, 4);
v_k_966_ = lean_ctor_get(v_impl_879_, 1);
v_v_967_ = lean_ctor_get(v_impl_879_, 2);
v_isSharedCheck_990_ = !lean_is_exclusive(v_impl_879_);
if (v_isSharedCheck_990_ == 0)
{
lean_object* v_unused_991_; lean_object* v_unused_992_; 
v_unused_991_ = lean_ctor_get(v_impl_879_, 3);
lean_dec(v_unused_991_);
v_unused_992_ = lean_ctor_get(v_impl_879_, 0);
lean_dec(v_unused_992_);
v___x_969_ = v_impl_879_;
v_isShared_970_ = v_isSharedCheck_990_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_r_965_);
lean_inc(v_v_967_);
lean_inc(v_k_966_);
lean_dec(v_impl_879_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_990_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v_k_971_; lean_object* v_v_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_986_; 
v_k_971_ = lean_ctor_get(v_l_964_, 1);
v_v_972_ = lean_ctor_get(v_l_964_, 2);
v_isSharedCheck_986_ = !lean_is_exclusive(v_l_964_);
if (v_isSharedCheck_986_ == 0)
{
lean_object* v_unused_987_; lean_object* v_unused_988_; lean_object* v_unused_989_; 
v_unused_987_ = lean_ctor_get(v_l_964_, 4);
lean_dec(v_unused_987_);
v_unused_988_ = lean_ctor_get(v_l_964_, 3);
lean_dec(v_unused_988_);
v_unused_989_ = lean_ctor_get(v_l_964_, 0);
lean_dec(v_unused_989_);
v___x_974_ = v_l_964_;
v_isShared_975_ = v_isSharedCheck_986_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_v_972_);
lean_inc(v_k_971_);
lean_dec(v_l_964_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_986_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_976_; lean_object* v___x_978_; 
v___x_976_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_965_, 2);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 4, v_r_965_);
lean_ctor_set(v___x_974_, 3, v_r_965_);
lean_ctor_set(v___x_974_, 2, v_v_732_);
lean_ctor_set(v___x_974_, 1, v_k_731_);
lean_ctor_set(v___x_974_, 0, v___x_880_);
v___x_978_ = v___x_974_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_880_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_k_731_);
lean_ctor_set(v_reuseFailAlloc_985_, 2, v_v_732_);
lean_ctor_set(v_reuseFailAlloc_985_, 3, v_r_965_);
lean_ctor_set(v_reuseFailAlloc_985_, 4, v_r_965_);
v___x_978_ = v_reuseFailAlloc_985_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
lean_object* v___x_980_; 
lean_inc(v_r_965_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 3, v_r_965_);
lean_ctor_set(v___x_969_, 0, v___x_880_);
v___x_980_ = v___x_969_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_880_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v_k_966_);
lean_ctor_set(v_reuseFailAlloc_984_, 2, v_v_967_);
lean_ctor_set(v_reuseFailAlloc_984_, 3, v_r_965_);
lean_ctor_set(v_reuseFailAlloc_984_, 4, v_r_965_);
v___x_980_ = v_reuseFailAlloc_984_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v___x_982_; 
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 4, v___x_980_);
lean_ctor_set(v___x_736_, 3, v___x_978_);
lean_ctor_set(v___x_736_, 2, v_v_972_);
lean_ctor_set(v___x_736_, 1, v_k_971_);
lean_ctor_set(v___x_736_, 0, v___x_976_);
v___x_982_ = v___x_736_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_976_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v_k_971_);
lean_ctor_set(v_reuseFailAlloc_983_, 2, v_v_972_);
lean_ctor_set(v_reuseFailAlloc_983_, 3, v___x_978_);
lean_ctor_set(v_reuseFailAlloc_983_, 4, v___x_980_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
}
}
else
{
lean_object* v_r_993_; 
v_r_993_ = lean_ctor_get(v_impl_879_, 4);
lean_inc(v_r_993_);
if (lean_obj_tag(v_r_993_) == 0)
{
lean_object* v_k_994_; lean_object* v_v_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1006_; 
v_k_994_ = lean_ctor_get(v_impl_879_, 1);
v_v_995_ = lean_ctor_get(v_impl_879_, 2);
v_isSharedCheck_1006_ = !lean_is_exclusive(v_impl_879_);
if (v_isSharedCheck_1006_ == 0)
{
lean_object* v_unused_1007_; lean_object* v_unused_1008_; lean_object* v_unused_1009_; 
v_unused_1007_ = lean_ctor_get(v_impl_879_, 4);
lean_dec(v_unused_1007_);
v_unused_1008_ = lean_ctor_get(v_impl_879_, 3);
lean_dec(v_unused_1008_);
v_unused_1009_ = lean_ctor_get(v_impl_879_, 0);
lean_dec(v_unused_1009_);
v___x_997_ = v_impl_879_;
v_isShared_998_ = v_isSharedCheck_1006_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_v_995_);
lean_inc(v_k_994_);
lean_dec(v_impl_879_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1006_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_999_; lean_object* v___x_1001_; 
v___x_999_ = lean_unsigned_to_nat(3u);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 4, v_l_964_);
lean_ctor_set(v___x_997_, 2, v_v_732_);
lean_ctor_set(v___x_997_, 1, v_k_731_);
lean_ctor_set(v___x_997_, 0, v___x_880_);
v___x_1001_ = v___x_997_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_880_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v_k_731_);
lean_ctor_set(v_reuseFailAlloc_1005_, 2, v_v_732_);
lean_ctor_set(v_reuseFailAlloc_1005_, 3, v_l_964_);
lean_ctor_set(v_reuseFailAlloc_1005_, 4, v_l_964_);
v___x_1001_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
lean_object* v___x_1003_; 
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 4, v_r_993_);
lean_ctor_set(v___x_736_, 3, v___x_1001_);
lean_ctor_set(v___x_736_, 2, v_v_995_);
lean_ctor_set(v___x_736_, 1, v_k_994_);
lean_ctor_set(v___x_736_, 0, v___x_999_);
v___x_1003_ = v___x_736_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v___x_999_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v_k_994_);
lean_ctor_set(v_reuseFailAlloc_1004_, 2, v_v_995_);
lean_ctor_set(v_reuseFailAlloc_1004_, 3, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1004_, 4, v_r_993_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
else
{
lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1010_ = lean_unsigned_to_nat(2u);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 4, v_impl_879_);
lean_ctor_set(v___x_736_, 3, v_r_993_);
lean_ctor_set(v___x_736_, 0, v___x_1010_);
v___x_1012_ = v___x_736_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_k_731_);
lean_ctor_set(v_reuseFailAlloc_1013_, 2, v_v_732_);
lean_ctor_set(v_reuseFailAlloc_1013_, 3, v_r_993_);
lean_ctor_set(v_reuseFailAlloc_1013_, 4, v_impl_879_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
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
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = lean_unsigned_to_nat(1u);
v___x_1016_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
lean_ctor_set(v___x_1016_, 1, v_k_727_);
lean_ctor_set(v___x_1016_, 2, v_v_728_);
lean_ctor_set(v___x_1016_, 3, v_t_729_);
lean_ctor_set(v___x_1016_, 4, v_t_729_);
return v___x_1016_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_LeanOptions_fromOptions_x3f_spec__1(lean_object* v_init_1017_, lean_object* v_x_1018_){
_start:
{
if (lean_obj_tag(v_x_1018_) == 0)
{
lean_object* v_k_1019_; lean_object* v_v_1020_; lean_object* v_l_1021_; lean_object* v_r_1022_; lean_object* v___x_1023_; 
v_k_1019_ = lean_ctor_get(v_x_1018_, 1);
lean_inc(v_k_1019_);
v_v_1020_ = lean_ctor_get(v_x_1018_, 2);
lean_inc(v_v_1020_);
v_l_1021_ = lean_ctor_get(v_x_1018_, 3);
lean_inc(v_l_1021_);
v_r_1022_ = lean_ctor_get(v_x_1018_, 4);
lean_inc(v_r_1022_);
lean_dec_ref_known(v_x_1018_, 5);
v___x_1023_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_LeanOptions_fromOptions_x3f_spec__1(v_init_1017_, v_l_1021_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_dec(v_r_1022_);
lean_dec(v_v_1020_);
lean_dec(v_k_1019_);
return v___x_1023_;
}
else
{
lean_object* v_val_1024_; lean_object* v_a_1025_; lean_object* v___x_1026_; 
v_val_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_val_1024_);
lean_dec_ref_known(v___x_1023_, 1);
v_a_1025_ = lean_ctor_get(v_val_1024_, 0);
lean_inc(v_a_1025_);
lean_dec(v_val_1024_);
v___x_1026_ = l_Lean_LeanOptionValue_ofDataValue_x3f(v_v_1020_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v___x_1027_; 
lean_dec(v_a_1025_);
lean_dec(v_r_1022_);
lean_dec(v_k_1019_);
v___x_1027_ = lean_box(0);
return v___x_1027_;
}
else
{
lean_object* v_val_1028_; lean_object* v___x_1029_; 
v_val_1028_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_val_1028_);
lean_dec_ref_known(v___x_1026_, 1);
v___x_1029_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_LeanOptions_fromOptions_x3f_spec__0___redArg(v_k_1019_, v_val_1028_, v_a_1025_);
v_init_1017_ = v___x_1029_;
v_x_1018_ = v_r_1022_;
goto _start;
}
}
}
else
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1031_, 0, v_init_1017_);
v___x_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
return v___x_1032_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptions_fromOptions_x3f(lean_object* v_options_1033_){
_start:
{
lean_object* v_map_1034_; lean_object* v_values_1035_; lean_object* v___x_1036_; 
v_map_1034_ = lean_ctor_get(v_options_1033_, 0);
lean_inc(v_map_1034_);
lean_dec_ref(v_options_1033_);
v_values_1035_ = lean_box(1);
v___x_1036_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_LeanOptions_fromOptions_x3f_spec__1(v_values_1035_, v_map_1034_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v___x_1037_; 
v___x_1037_ = lean_box(0);
return v___x_1037_;
}
else
{
lean_object* v_val_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1046_; 
v_val_1038_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1040_ = v___x_1036_;
v_isShared_1041_ = v_isSharedCheck_1046_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_val_1038_);
lean_dec(v___x_1036_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1046_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v_a_1042_; lean_object* v___x_1044_; 
v_a_1042_ = lean_ctor_get(v_val_1038_, 0);
lean_inc(v_a_1042_);
lean_dec(v_val_1038_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v_a_1042_);
v___x_1044_ = v___x_1040_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_LeanOptions_fromOptions_x3f_spec__0(lean_object* v_00_u03b2_1047_, lean_object* v_k_1048_, lean_object* v_v_1049_, lean_object* v_t_1050_, lean_object* v_hl_1051_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_LeanOptions_fromOptions_x3f_spec__0___redArg(v_k_1048_, v_v_1049_, v_t_1050_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonLeanOptions___lam__0(lean_object* v___f_1053_, lean_object* v_j_1054_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Lean_NameMap_fromJson_x3f___redArg(v___f_1053_, v_j_1054_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1055_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1055_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
v_a_1064_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1055_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1055_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
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
LEAN_EXPORT lean_object* l_Lean_instToJsonLeanOptions___lam__0(lean_object* v___f_1075_, lean_object* v_options_1076_){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Lean_NameMap_toJson___redArg(v___f_1075_, v_options_1076_);
return v___x_1077_;
}
}
lean_object* runtime_initialize_Lean_Data_Json_FromToJson_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_LeanOptions(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_Json_FromToJson_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedLeanOptions_default = _init_l_Lean_instInhabitedLeanOptions_default();
lean_mark_persistent(l_Lean_instInhabitedLeanOptions_default);
l_Lean_instInhabitedLeanOptions = _init_l_Lean_instInhabitedLeanOptions();
lean_mark_persistent(l_Lean_instInhabitedLeanOptions);
l_Lean_instEmptyCollectionLeanOptions = _init_l_Lean_instEmptyCollectionLeanOptions();
lean_mark_persistent(l_Lean_instEmptyCollectionLeanOptions);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_LeanOptions(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Json_FromToJson_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_LeanOptions(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Json_FromToJson_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_LeanOptions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_LeanOptions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_LeanOptions(builtin);
}
#ifdef __cplusplus
}
#endif

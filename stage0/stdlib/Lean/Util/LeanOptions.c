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
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_NameMap_toJson___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
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
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Lean_LeanOptionValue_ctorIdx(v_x_5_);
lean_dec_ref(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ctorElim___redArg(lean_object* v_t_7_, lean_object* v_k_8_){
_start:
{
switch(lean_obj_tag(v_t_7_))
{
case 0:
{
lean_object* v_s_9_; lean_object* v___x_10_; 
v_s_9_ = lean_ctor_get(v_t_7_, 0);
lean_inc_ref(v_s_9_);
lean_dec_ref(v_t_7_);
v___x_10_ = lean_apply_1(v_k_8_, v_s_9_);
return v___x_10_;
}
case 1:
{
uint8_t v_b_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v_b_11_ = lean_ctor_get_uint8(v_t_7_, 0);
lean_dec_ref(v_t_7_);
v___x_12_ = lean_box(v_b_11_);
v___x_13_ = lean_apply_1(v_k_8_, v___x_12_);
return v___x_13_;
}
default: 
{
lean_object* v_n_14_; lean_object* v___x_15_; 
v_n_14_ = lean_ctor_get(v_t_7_, 0);
lean_inc(v_n_14_);
lean_dec_ref(v_t_7_);
v___x_15_ = lean_apply_1(v_k_8_, v_n_14_);
return v___x_15_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Lean_LeanOptionValue_ctorElim___redArg(v_t_18_, v_k_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ctorElim___boxed(lean_object* v_motive_22_, lean_object* v_ctorIdx_23_, lean_object* v_t_24_, lean_object* v_h_25_, lean_object* v_k_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Lean_LeanOptionValue_ctorElim(v_motive_22_, v_ctorIdx_23_, v_t_24_, v_h_25_, v_k_26_);
lean_dec(v_ctorIdx_23_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ofString_elim___redArg(lean_object* v_t_28_, lean_object* v_ofString_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_LeanOptionValue_ctorElim___redArg(v_t_28_, v_ofString_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ofString_elim(lean_object* v_motive_31_, lean_object* v_t_32_, lean_object* v_h_33_, lean_object* v_ofString_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_LeanOptionValue_ctorElim___redArg(v_t_32_, v_ofString_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ofBool_elim___redArg(lean_object* v_t_36_, lean_object* v_ofBool_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_LeanOptionValue_ctorElim___redArg(v_t_36_, v_ofBool_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ofBool_elim(lean_object* v_motive_39_, lean_object* v_t_40_, lean_object* v_h_41_, lean_object* v_ofBool_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lean_LeanOptionValue_ctorElim___redArg(v_t_40_, v_ofBool_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ofNat_elim___redArg(lean_object* v_t_44_, lean_object* v_ofNat_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lean_LeanOptionValue_ctorElim___redArg(v_t_44_, v_ofNat_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ofNat_elim(lean_object* v_motive_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_ofNat_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lean_LeanOptionValue_ctorElim___redArg(v_t_48_, v_ofNat_50_);
return v___x_51_;
}
}
static lean_object* _init_l_Lean_instReprLeanOptionValue_repr___closed__3(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = lean_unsigned_to_nat(2u);
v___x_64_ = lean_nat_to_int(v___x_63_);
return v___x_64_;
}
}
static lean_object* _init_l_Lean_instReprLeanOptionValue_repr___closed__4(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_unsigned_to_nat(1u);
v___x_66_ = lean_nat_to_int(v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLeanOptionValue_repr(lean_object* v_x_79_, lean_object* v_prec_80_){
_start:
{
switch(lean_obj_tag(v_x_79_))
{
case 0:
{
lean_object* v_s_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_101_; 
v_s_81_ = lean_ctor_get(v_x_79_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v_x_79_);
if (v_isSharedCheck_101_ == 0)
{
v___x_83_ = v_x_79_;
v_isShared_84_ = v_isSharedCheck_101_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_s_81_);
lean_dec(v_x_79_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_101_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___y_86_; lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_97_ = lean_unsigned_to_nat(1024u);
v___x_98_ = lean_nat_dec_le(v___x_97_, v_prec_80_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; 
v___x_99_ = lean_obj_once(&l_Lean_instReprLeanOptionValue_repr___closed__3, &l_Lean_instReprLeanOptionValue_repr___closed__3_once, _init_l_Lean_instReprLeanOptionValue_repr___closed__3);
v___y_86_ = v___x_99_;
goto v___jp_85_;
}
else
{
lean_object* v___x_100_; 
v___x_100_ = lean_obj_once(&l_Lean_instReprLeanOptionValue_repr___closed__4, &l_Lean_instReprLeanOptionValue_repr___closed__4_once, _init_l_Lean_instReprLeanOptionValue_repr___closed__4);
v___y_86_ = v___x_100_;
goto v___jp_85_;
}
v___jp_85_:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_90_; 
v___x_87_ = ((lean_object*)(l_Lean_instReprLeanOptionValue_repr___closed__2));
v___x_88_ = l_String_quote(v_s_81_);
if (v_isShared_84_ == 0)
{
lean_ctor_set_tag(v___x_83_, 3);
lean_ctor_set(v___x_83_, 0, v___x_88_);
v___x_90_ = v___x_83_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_88_);
v___x_90_ = v_reuseFailAlloc_96_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_91_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_87_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
lean_inc(v___y_86_);
v___x_92_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_92_, 0, v___y_86_);
lean_ctor_set(v___x_92_, 1, v___x_91_);
v___x_93_ = 0;
v___x_94_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_94_, 0, v___x_92_);
lean_ctor_set_uint8(v___x_94_, sizeof(void*)*1, v___x_93_);
v___x_95_ = l_Repr_addAppParen(v___x_94_, v_prec_80_);
return v___x_95_;
}
}
}
}
case 1:
{
uint8_t v_b_102_; lean_object* v___y_104_; lean_object* v___x_112_; uint8_t v___x_113_; 
v_b_102_ = lean_ctor_get_uint8(v_x_79_, 0);
lean_dec_ref(v_x_79_);
v___x_112_ = lean_unsigned_to_nat(1024u);
v___x_113_ = lean_nat_dec_le(v___x_112_, v_prec_80_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; 
v___x_114_ = lean_obj_once(&l_Lean_instReprLeanOptionValue_repr___closed__3, &l_Lean_instReprLeanOptionValue_repr___closed__3_once, _init_l_Lean_instReprLeanOptionValue_repr___closed__3);
v___y_104_ = v___x_114_;
goto v___jp_103_;
}
else
{
lean_object* v___x_115_; 
v___x_115_ = lean_obj_once(&l_Lean_instReprLeanOptionValue_repr___closed__4, &l_Lean_instReprLeanOptionValue_repr___closed__4_once, _init_l_Lean_instReprLeanOptionValue_repr___closed__4);
v___y_104_ = v___x_115_;
goto v___jp_103_;
}
v___jp_103_:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; uint8_t v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_105_ = ((lean_object*)(l_Lean_instReprLeanOptionValue_repr___closed__7));
v___x_106_ = l_Bool_repr___redArg(v_b_102_);
v___x_107_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_105_);
lean_ctor_set(v___x_107_, 1, v___x_106_);
lean_inc(v___y_104_);
v___x_108_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_108_, 0, v___y_104_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
v___x_109_ = 0;
v___x_110_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_110_, 0, v___x_108_);
lean_ctor_set_uint8(v___x_110_, sizeof(void*)*1, v___x_109_);
v___x_111_ = l_Repr_addAppParen(v___x_110_, v_prec_80_);
return v___x_111_;
}
}
default: 
{
lean_object* v_n_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_136_; 
v_n_116_ = lean_ctor_get(v_x_79_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v_x_79_);
if (v_isSharedCheck_136_ == 0)
{
v___x_118_ = v_x_79_;
v_isShared_119_ = v_isSharedCheck_136_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_n_116_);
lean_dec(v_x_79_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_136_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___y_121_; lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_132_ = lean_unsigned_to_nat(1024u);
v___x_133_ = lean_nat_dec_le(v___x_132_, v_prec_80_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; 
v___x_134_ = lean_obj_once(&l_Lean_instReprLeanOptionValue_repr___closed__3, &l_Lean_instReprLeanOptionValue_repr___closed__3_once, _init_l_Lean_instReprLeanOptionValue_repr___closed__3);
v___y_121_ = v___x_134_;
goto v___jp_120_;
}
else
{
lean_object* v___x_135_; 
v___x_135_ = lean_obj_once(&l_Lean_instReprLeanOptionValue_repr___closed__4, &l_Lean_instReprLeanOptionValue_repr___closed__4_once, _init_l_Lean_instReprLeanOptionValue_repr___closed__4);
v___y_121_ = v___x_135_;
goto v___jp_120_;
}
v___jp_120_:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_125_; 
v___x_122_ = ((lean_object*)(l_Lean_instReprLeanOptionValue_repr___closed__10));
v___x_123_ = l_Nat_reprFast(v_n_116_);
if (v_isShared_119_ == 0)
{
lean_ctor_set_tag(v___x_118_, 3);
lean_ctor_set(v___x_118_, 0, v___x_123_);
v___x_125_ = v___x_118_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_123_);
v___x_125_ = v_reuseFailAlloc_131_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_126_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_122_);
lean_ctor_set(v___x_126_, 1, v___x_125_);
lean_inc(v___y_121_);
v___x_127_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_127_, 0, v___y_121_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
v___x_128_ = 0;
v___x_129_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_129_, 0, v___x_127_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*1, v___x_128_);
v___x_130_ = l_Repr_addAppParen(v___x_129_, v_prec_80_);
return v___x_130_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLeanOptionValue_repr___boxed(lean_object* v_x_137_, lean_object* v_prec_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_instReprLeanOptionValue_repr(v_x_137_, v_prec_138_);
lean_dec(v_prec_138_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_ofDataValue_x3f(lean_object* v_x_142_){
_start:
{
switch(lean_obj_tag(v_x_142_))
{
case 0:
{
lean_object* v_v_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_151_; 
v_v_143_ = lean_ctor_get(v_x_142_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v_x_142_);
if (v_isSharedCheck_151_ == 0)
{
v___x_145_ = v_x_142_;
v_isShared_146_ = v_isSharedCheck_151_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_v_143_);
lean_dec(v_x_142_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_151_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_v_143_);
v___x_148_ = v_reuseFailAlloc_150_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
lean_object* v___x_149_; 
v___x_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
return v___x_149_;
}
}
}
case 1:
{
uint8_t v_v_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_160_; 
v_v_152_ = lean_ctor_get_uint8(v_x_142_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v_x_142_);
if (v_isSharedCheck_160_ == 0)
{
v___x_154_ = v_x_142_;
v_isShared_155_ = v_isSharedCheck_160_;
goto v_resetjp_153_;
}
else
{
lean_dec(v_x_142_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_160_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_157_; 
if (v_isShared_155_ == 0)
{
v___x_157_ = v___x_154_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_159_, 0, v_v_152_);
v___x_157_ = v_reuseFailAlloc_159_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
lean_object* v___x_158_; 
v___x_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
return v___x_158_;
}
}
}
case 3:
{
lean_object* v_v_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_169_; 
v_v_161_ = lean_ctor_get(v_x_142_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v_x_142_);
if (v_isSharedCheck_169_ == 0)
{
v___x_163_ = v_x_142_;
v_isShared_164_ = v_isSharedCheck_169_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_v_161_);
lean_dec(v_x_142_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_169_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_166_; 
if (v_isShared_164_ == 0)
{
lean_ctor_set_tag(v___x_163_, 2);
v___x_166_ = v___x_163_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_v_161_);
v___x_166_ = v_reuseFailAlloc_168_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_167_; 
v___x_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
return v___x_167_;
}
}
}
default: 
{
lean_object* v___x_170_; 
lean_dec_ref(v_x_142_);
v___x_170_ = lean_box(0);
return v___x_170_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_toDataValue(lean_object* v_x_171_){
_start:
{
switch(lean_obj_tag(v_x_171_))
{
case 0:
{
lean_object* v_s_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_179_; 
v_s_172_ = lean_ctor_get(v_x_171_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v_x_171_);
if (v_isSharedCheck_179_ == 0)
{
v___x_174_ = v_x_171_;
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_s_172_);
lean_dec(v_x_171_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_177_; 
if (v_isShared_175_ == 0)
{
v___x_177_ = v___x_174_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_s_172_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
case 1:
{
uint8_t v_b_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_187_; 
v_b_180_ = lean_ctor_get_uint8(v_x_171_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v_x_171_);
if (v_isSharedCheck_187_ == 0)
{
v___x_182_ = v_x_171_;
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
else
{
lean_dec(v_x_171_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_185_; 
if (v_isShared_183_ == 0)
{
v___x_185_ = v___x_182_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_186_, 0, v_b_180_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
default: 
{
lean_object* v_n_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_195_; 
v_n_188_ = lean_ctor_get(v_x_171_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v_x_171_);
if (v_isSharedCheck_195_ == 0)
{
v___x_190_ = v_x_171_;
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_n_188_);
lean_dec(v_x_171_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_193_; 
if (v_isShared_191_ == 0)
{
lean_ctor_set_tag(v___x_190_, 3);
v___x_193_ = v___x_190_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_n_188_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeStringLeanOptionValue___lam__0(lean_object* v_s_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_203_, 0, v_s_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeBoolLeanOptionValue___lam__0(uint8_t v_b_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_207_, 0, v_b_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeBoolLeanOptionValue___lam__0___boxed(lean_object* v_b_208_){
_start:
{
uint8_t v_b_boxed_209_; lean_object* v_res_210_; 
v_b_boxed_209_ = lean_unbox(v_b_208_);
v_res_210_ = l_Lean_instCoeBoolLeanOptionValue___lam__0(v_b_boxed_209_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeNatLeanOptionValue___lam__0(lean_object* v_n_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_214_, 0, v_n_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_instOfNatLeanOptionValue(lean_object* v_n_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_218_, 0, v_n_217_);
return v___x_218_;
}
}
static lean_object* _init_l_Lean_instFromJsonLeanOptionValue___lam__0___closed__2(void){
_start:
{
lean_object* v_natZero_222_; lean_object* v_intZero_223_; 
v_natZero_222_ = lean_unsigned_to_nat(0u);
v_intZero_223_ = lean_nat_to_int(v_natZero_222_);
return v_intZero_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonLeanOptionValue___lam__0(lean_object* v_x_224_){
_start:
{
switch(lean_obj_tag(v_x_224_))
{
case 3:
{
lean_object* v_s_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_235_; 
v_s_227_ = lean_ctor_get(v_x_224_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v_x_224_);
if (v_isSharedCheck_235_ == 0)
{
v___x_229_ = v_x_224_;
v_isShared_230_ = v_isSharedCheck_235_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_s_227_);
lean_dec(v_x_224_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_235_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_232_; 
if (v_isShared_230_ == 0)
{
lean_ctor_set_tag(v___x_229_, 0);
v___x_232_ = v___x_229_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_s_227_);
v___x_232_ = v_reuseFailAlloc_234_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
lean_object* v___x_233_; 
v___x_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
return v___x_233_;
}
}
}
case 1:
{
uint8_t v_b_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_244_; 
v_b_236_ = lean_ctor_get_uint8(v_x_224_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v_x_224_);
if (v_isSharedCheck_244_ == 0)
{
v___x_238_ = v_x_224_;
v_isShared_239_ = v_isSharedCheck_244_;
goto v_resetjp_237_;
}
else
{
lean_dec(v_x_224_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_244_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_241_; 
if (v_isShared_239_ == 0)
{
v___x_241_ = v___x_238_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_243_, 0, v_b_236_);
v___x_241_ = v_reuseFailAlloc_243_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_242_; 
v___x_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
return v___x_242_;
}
}
}
case 2:
{
lean_object* v_n_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_260_; 
v_n_245_ = lean_ctor_get(v_x_224_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v_x_224_);
if (v_isSharedCheck_260_ == 0)
{
v___x_247_ = v_x_224_;
v_isShared_248_ = v_isSharedCheck_260_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_n_245_);
lean_dec(v_x_224_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_260_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v_mantissa_249_; lean_object* v_exponent_250_; lean_object* v_natZero_251_; lean_object* v_intZero_252_; uint8_t v_isNeg_253_; 
v_mantissa_249_ = lean_ctor_get(v_n_245_, 0);
lean_inc(v_mantissa_249_);
v_exponent_250_ = lean_ctor_get(v_n_245_, 1);
lean_inc(v_exponent_250_);
lean_dec_ref(v_n_245_);
v_natZero_251_ = lean_unsigned_to_nat(0u);
v_intZero_252_ = lean_obj_once(&l_Lean_instFromJsonLeanOptionValue___lam__0___closed__2, &l_Lean_instFromJsonLeanOptionValue___lam__0___closed__2_once, _init_l_Lean_instFromJsonLeanOptionValue___lam__0___closed__2);
v_isNeg_253_ = lean_int_dec_lt(v_mantissa_249_, v_intZero_252_);
if (v_isNeg_253_ == 0)
{
uint8_t v___x_254_; 
v___x_254_ = lean_nat_dec_eq(v_exponent_250_, v_natZero_251_);
lean_dec(v_exponent_250_);
if (v___x_254_ == 0)
{
lean_dec(v_mantissa_249_);
lean_del_object(v___x_247_);
goto v___jp_225_;
}
else
{
lean_object* v_a_255_; lean_object* v___x_257_; 
v_a_255_ = lean_nat_abs(v_mantissa_249_);
lean_dec(v_mantissa_249_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v_a_255_);
v___x_257_ = v___x_247_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_255_);
v___x_257_ = v_reuseFailAlloc_259_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_258_; 
v___x_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
return v___x_258_;
}
}
}
else
{
lean_dec(v_exponent_250_);
lean_dec(v_mantissa_249_);
lean_del_object(v___x_247_);
goto v___jp_225_;
}
}
}
default: 
{
lean_dec(v_x_224_);
goto v___jp_225_;
}
}
v___jp_225_:
{
lean_object* v___x_226_; 
v___x_226_ = ((lean_object*)(l_Lean_instFromJsonLeanOptionValue___lam__0___closed__1));
return v___x_226_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonLeanOptionValue___lam__0(lean_object* v_x_263_){
_start:
{
switch(lean_obj_tag(v_x_263_))
{
case 0:
{
lean_object* v_s_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_271_; 
v_s_264_ = lean_ctor_get(v_x_263_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v_x_263_);
if (v_isSharedCheck_271_ == 0)
{
v___x_266_ = v_x_263_;
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_s_264_);
lean_dec(v_x_263_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_269_; 
if (v_isShared_267_ == 0)
{
lean_ctor_set_tag(v___x_266_, 3);
v___x_269_ = v___x_266_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_s_264_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
case 1:
{
uint8_t v_b_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_279_; 
v_b_272_ = lean_ctor_get_uint8(v_x_263_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v_x_263_);
if (v_isSharedCheck_279_ == 0)
{
v___x_274_ = v_x_263_;
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
else
{
lean_dec(v_x_263_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_277_; 
if (v_isShared_275_ == 0)
{
v___x_277_ = v___x_274_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_278_, 0, v_b_272_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
default: 
{
lean_object* v_n_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_288_; 
v_n_280_ = lean_ctor_get(v_x_263_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v_x_263_);
if (v_isSharedCheck_288_ == 0)
{
v___x_282_ = v_x_263_;
v_isShared_283_ = v_isSharedCheck_288_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_n_280_);
lean_dec(v_x_263_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_288_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_284_; lean_object* v___x_286_; 
v___x_284_ = l_Lean_JsonNumber_fromNat(v_n_280_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v___x_284_);
v___x_286_ = v___x_282_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_284_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptionValue_asCliFlagValue(lean_object* v_x_294_){
_start:
{
switch(lean_obj_tag(v_x_294_))
{
case 0:
{
lean_object* v_s_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v_s_295_ = lean_ctor_get(v_x_294_, 0);
lean_inc_ref(v_s_295_);
lean_dec_ref(v_x_294_);
v___x_296_ = ((lean_object*)(l_Lean_LeanOptionValue_asCliFlagValue___closed__0));
v___x_297_ = lean_string_append(v___x_296_, v_s_295_);
lean_dec_ref(v_s_295_);
v___x_298_ = lean_string_append(v___x_297_, v___x_296_);
return v___x_298_;
}
case 1:
{
uint8_t v_b_299_; 
v_b_299_ = lean_ctor_get_uint8(v_x_294_, 0);
lean_dec_ref(v_x_294_);
if (v_b_299_ == 0)
{
lean_object* v___x_300_; 
v___x_300_ = ((lean_object*)(l_Lean_LeanOptionValue_asCliFlagValue___closed__1));
return v___x_300_;
}
else
{
lean_object* v___x_301_; 
v___x_301_ = ((lean_object*)(l_Lean_LeanOptionValue_asCliFlagValue___closed__2));
return v___x_301_;
}
}
default: 
{
lean_object* v_n_302_; lean_object* v___x_303_; 
v_n_302_ = lean_ctor_get(v_x_294_, 0);
lean_inc(v_n_302_);
lean_dec_ref(v_x_294_);
v___x_303_ = l_Nat_reprFast(v_n_302_);
return v___x_303_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprLeanOption_repr_spec__0(lean_object* v_a_309_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = lean_nat_to_int(v_a_309_);
return v___x_310_;
}
}
static lean_object* _init_l_Lean_instReprLeanOption_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = lean_unsigned_to_nat(8u);
v___x_325_ = lean_nat_to_int(v___x_324_);
return v___x_325_;
}
}
static lean_object* _init_l_Lean_instReprLeanOption_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = lean_unsigned_to_nat(9u);
v___x_333_ = lean_nat_to_int(v___x_332_);
return v___x_333_;
}
}
static lean_object* _init_l_Lean_instReprLeanOption_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = ((lean_object*)(l_Lean_instReprLeanOption_repr___redArg___closed__0));
v___x_336_ = lean_string_length(v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l_Lean_instReprLeanOption_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_obj_once(&l_Lean_instReprLeanOption_repr___redArg___closed__14, &l_Lean_instReprLeanOption_repr___redArg___closed__14_once, _init_l_Lean_instReprLeanOption_repr___redArg___closed__14);
v___x_338_ = lean_nat_to_int(v___x_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLeanOption_repr___redArg(lean_object* v_x_343_){
_start:
{
lean_object* v_name_344_; lean_object* v_value_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_379_; 
v_name_344_ = lean_ctor_get(v_x_343_, 0);
v_value_345_ = lean_ctor_get(v_x_343_, 1);
v_isSharedCheck_379_ = !lean_is_exclusive(v_x_343_);
if (v_isSharedCheck_379_ == 0)
{
v___x_347_ = v_x_343_;
v_isShared_348_ = v_isSharedCheck_379_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_value_345_);
lean_inc(v_name_344_);
lean_dec(v_x_343_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_379_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_355_; 
v___x_349_ = ((lean_object*)(l_Lean_instReprLeanOption_repr___redArg___closed__5));
v___x_350_ = ((lean_object*)(l_Lean_instReprLeanOption_repr___redArg___closed__6));
v___x_351_ = lean_obj_once(&l_Lean_instReprLeanOption_repr___redArg___closed__7, &l_Lean_instReprLeanOption_repr___redArg___closed__7_once, _init_l_Lean_instReprLeanOption_repr___redArg___closed__7);
v___x_352_ = lean_unsigned_to_nat(0u);
v___x_353_ = l_Lean_Name_reprPrec(v_name_344_, v___x_352_);
if (v_isShared_348_ == 0)
{
lean_ctor_set_tag(v___x_347_, 4);
lean_ctor_set(v___x_347_, 1, v___x_353_);
lean_ctor_set(v___x_347_, 0, v___x_351_);
v___x_355_ = v___x_347_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_351_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v___x_353_);
v___x_355_ = v_reuseFailAlloc_378_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
uint8_t v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_356_ = 0;
v___x_357_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_357_, 0, v___x_355_);
lean_ctor_set_uint8(v___x_357_, sizeof(void*)*1, v___x_356_);
v___x_358_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_350_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
v___x_359_ = ((lean_object*)(l_Lean_instReprLeanOption_repr___redArg___closed__9));
v___x_360_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_358_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v___x_361_ = lean_box(1);
v___x_362_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_360_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = ((lean_object*)(l_Lean_instReprLeanOption_repr___redArg___closed__11));
v___x_364_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_362_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
v___x_365_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
lean_ctor_set(v___x_365_, 1, v___x_349_);
v___x_366_ = lean_obj_once(&l_Lean_instReprLeanOption_repr___redArg___closed__12, &l_Lean_instReprLeanOption_repr___redArg___closed__12_once, _init_l_Lean_instReprLeanOption_repr___redArg___closed__12);
v___x_367_ = l_Lean_instReprLeanOptionValue_repr(v_value_345_, v___x_352_);
v___x_368_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_366_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
v___x_369_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_369_, 0, v___x_368_);
lean_ctor_set_uint8(v___x_369_, sizeof(void*)*1, v___x_356_);
v___x_370_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_365_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
v___x_371_ = lean_obj_once(&l_Lean_instReprLeanOption_repr___redArg___closed__15, &l_Lean_instReprLeanOption_repr___redArg___closed__15_once, _init_l_Lean_instReprLeanOption_repr___redArg___closed__15);
v___x_372_ = ((lean_object*)(l_Lean_instReprLeanOption_repr___redArg___closed__16));
v___x_373_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
lean_ctor_set(v___x_373_, 1, v___x_370_);
v___x_374_ = ((lean_object*)(l_Lean_instReprLeanOption_repr___redArg___closed__17));
v___x_375_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_373_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
v___x_376_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_371_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
v___x_377_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_377_, 0, v___x_376_);
lean_ctor_set_uint8(v___x_377_, sizeof(void*)*1, v___x_356_);
return v___x_377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLeanOption_repr(lean_object* v_x_380_, lean_object* v_prec_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_instReprLeanOption_repr___redArg(v_x_380_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLeanOption_repr___boxed(lean_object* v_x_383_, lean_object* v_prec_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_instReprLeanOption_repr(v_x_383_, v_prec_384_);
lean_dec(v_prec_384_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOption_asCliArg(lean_object* v_o_390_){
_start:
{
lean_object* v_name_391_; lean_object* v_value_392_; lean_object* v___x_393_; uint8_t v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v_name_391_ = lean_ctor_get(v_o_390_, 0);
lean_inc(v_name_391_);
v_value_392_ = lean_ctor_get(v_o_390_, 1);
lean_inc_ref(v_value_392_);
lean_dec_ref(v_o_390_);
v___x_393_ = ((lean_object*)(l_Lean_LeanOption_asCliArg___closed__0));
v___x_394_ = 1;
v___x_395_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_391_, v___x_394_);
v___x_396_ = lean_string_append(v___x_393_, v___x_395_);
lean_dec_ref(v___x_395_);
v___x_397_ = ((lean_object*)(l_Lean_LeanOption_asCliArg___closed__1));
v___x_398_ = lean_string_append(v___x_396_, v___x_397_);
v___x_399_ = l_Lean_LeanOptionValue_asCliFlagValue(v_value_392_);
v___x_400_ = lean_string_append(v___x_398_, v___x_399_);
lean_dec_ref(v___x_399_);
return v___x_400_;
}
}
static lean_object* _init_l_Lean_instInhabitedLeanOptions_default(void){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = lean_box(1);
return v___x_401_;
}
}
static lean_object* _init_l_Lean_instInhabitedLeanOptions(void){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = lean_box(1);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1_spec__2_spec__3(lean_object* v_x_403_, lean_object* v_x_404_, lean_object* v_x_405_){
_start:
{
if (lean_obj_tag(v_x_405_) == 0)
{
lean_dec(v_x_403_);
return v_x_404_;
}
else
{
lean_object* v_head_406_; lean_object* v_tail_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_416_; 
v_head_406_ = lean_ctor_get(v_x_405_, 0);
v_tail_407_ = lean_ctor_get(v_x_405_, 1);
v_isSharedCheck_416_ = !lean_is_exclusive(v_x_405_);
if (v_isSharedCheck_416_ == 0)
{
v___x_409_ = v_x_405_;
v_isShared_410_ = v_isSharedCheck_416_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_tail_407_);
lean_inc(v_head_406_);
lean_dec(v_x_405_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_416_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
lean_inc(v_x_403_);
if (v_isShared_410_ == 0)
{
lean_ctor_set_tag(v___x_409_, 5);
lean_ctor_set(v___x_409_, 1, v_x_403_);
lean_ctor_set(v___x_409_, 0, v_x_404_);
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_x_404_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v_x_403_);
v___x_412_ = v_reuseFailAlloc_415_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
lean_object* v___x_413_; 
v___x_413_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
lean_ctor_set(v___x_413_, 1, v_head_406_);
v_x_404_ = v___x_413_;
v_x_405_ = v_tail_407_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1_spec__2(lean_object* v_x_417_, lean_object* v_x_418_){
_start:
{
if (lean_obj_tag(v_x_417_) == 0)
{
lean_object* v___x_419_; 
lean_dec(v_x_418_);
v___x_419_ = lean_box(0);
return v___x_419_;
}
else
{
lean_object* v_tail_420_; 
v_tail_420_ = lean_ctor_get(v_x_417_, 1);
if (lean_obj_tag(v_tail_420_) == 0)
{
lean_object* v_head_421_; 
lean_dec(v_x_418_);
v_head_421_ = lean_ctor_get(v_x_417_, 0);
lean_inc(v_head_421_);
lean_dec_ref(v_x_417_);
return v_head_421_;
}
else
{
lean_object* v_head_422_; lean_object* v___x_423_; 
lean_inc(v_tail_420_);
v_head_422_ = lean_ctor_get(v_x_417_, 0);
lean_inc(v_head_422_);
lean_dec_ref(v_x_417_);
v___x_423_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1_spec__2_spec__3(v_x_418_, v_head_422_, v_tail_420_);
return v___x_423_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__0));
v___x_430_ = lean_string_length(v___x_429_);
return v___x_430_;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__3, &l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__3_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__3);
v___x_432_ = lean_nat_to_int(v___x_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg(lean_object* v_x_437_){
_start:
{
lean_object* v_fst_438_; lean_object* v_snd_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_462_; 
v_fst_438_ = lean_ctor_get(v_x_437_, 0);
v_snd_439_ = lean_ctor_get(v_x_437_, 1);
v_isSharedCheck_462_ = !lean_is_exclusive(v_x_437_);
if (v_isSharedCheck_462_ == 0)
{
v___x_441_ = v_x_437_;
v_isShared_442_ = v_isSharedCheck_462_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_snd_439_);
lean_inc(v_fst_438_);
lean_dec(v_x_437_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_462_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_447_; 
v___x_443_ = lean_unsigned_to_nat(0u);
v___x_444_ = l_Lean_Name_reprPrec(v_fst_438_, v___x_443_);
v___x_445_ = lean_box(0);
if (v_isShared_442_ == 0)
{
lean_ctor_set_tag(v___x_441_, 1);
lean_ctor_set(v___x_441_, 1, v___x_445_);
lean_ctor_set(v___x_441_, 0, v___x_444_);
v___x_447_ = v___x_441_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_444_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v___x_445_);
v___x_447_ = v_reuseFailAlloc_461_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; uint8_t v___x_459_; lean_object* v___x_460_; 
v___x_448_ = l_Lean_instReprLeanOptionValue_repr(v_snd_439_, v___x_443_);
v___x_449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
lean_ctor_set(v___x_449_, 1, v___x_447_);
v___x_450_ = l_List_reverse___redArg(v___x_449_);
v___x_451_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__1));
v___x_452_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1_spec__2(v___x_450_, v___x_451_);
v___x_453_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__4, &l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__4_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__4);
v___x_454_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__5));
v___x_455_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
lean_ctor_set(v___x_455_, 1, v___x_452_);
v___x_456_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__6));
v___x_457_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_455_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v___x_458_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_453_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
v___x_459_ = 0;
v___x_460_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_460_, 0, v___x_458_);
lean_ctor_set_uint8(v___x_460_, sizeof(void*)*1, v___x_459_);
return v___x_460_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__2_spec__4_spec__6(lean_object* v_x_463_, lean_object* v_x_464_, lean_object* v_x_465_){
_start:
{
if (lean_obj_tag(v_x_465_) == 0)
{
lean_dec(v_x_463_);
return v_x_464_;
}
else
{
lean_object* v_head_466_; lean_object* v_tail_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_477_; 
v_head_466_ = lean_ctor_get(v_x_465_, 0);
v_tail_467_ = lean_ctor_get(v_x_465_, 1);
v_isSharedCheck_477_ = !lean_is_exclusive(v_x_465_);
if (v_isSharedCheck_477_ == 0)
{
v___x_469_ = v_x_465_;
v_isShared_470_ = v_isSharedCheck_477_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_tail_467_);
lean_inc(v_head_466_);
lean_dec(v_x_465_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_477_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_472_; 
lean_inc(v_x_463_);
if (v_isShared_470_ == 0)
{
lean_ctor_set_tag(v___x_469_, 5);
lean_ctor_set(v___x_469_, 1, v_x_463_);
lean_ctor_set(v___x_469_, 0, v_x_464_);
v___x_472_ = v___x_469_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_x_464_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v_x_463_);
v___x_472_ = v_reuseFailAlloc_476_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg(v_head_466_);
v___x_474_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_472_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
v_x_464_ = v___x_474_;
v_x_465_ = v_tail_467_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__2_spec__4(lean_object* v_x_478_, lean_object* v_x_479_, lean_object* v_x_480_){
_start:
{
if (lean_obj_tag(v_x_480_) == 0)
{
lean_dec(v_x_478_);
return v_x_479_;
}
else
{
lean_object* v_head_481_; lean_object* v_tail_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_492_; 
v_head_481_ = lean_ctor_get(v_x_480_, 0);
v_tail_482_ = lean_ctor_get(v_x_480_, 1);
v_isSharedCheck_492_ = !lean_is_exclusive(v_x_480_);
if (v_isSharedCheck_492_ == 0)
{
v___x_484_ = v_x_480_;
v_isShared_485_ = v_isSharedCheck_492_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_tail_482_);
lean_inc(v_head_481_);
lean_dec(v_x_480_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_492_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
lean_inc(v_x_478_);
if (v_isShared_485_ == 0)
{
lean_ctor_set_tag(v___x_484_, 5);
lean_ctor_set(v___x_484_, 1, v_x_478_);
lean_ctor_set(v___x_484_, 0, v_x_479_);
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_x_479_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_x_478_);
v___x_487_ = v_reuseFailAlloc_491_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_488_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg(v_head_481_);
v___x_489_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_487_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v___x_490_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__2_spec__4_spec__6(v_x_478_, v___x_489_, v_tail_482_);
return v___x_490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__2(lean_object* v_x_493_, lean_object* v_x_494_){
_start:
{
if (lean_obj_tag(v_x_493_) == 0)
{
lean_object* v___x_495_; 
lean_dec(v_x_494_);
v___x_495_ = lean_box(0);
return v___x_495_;
}
else
{
lean_object* v_tail_496_; 
v_tail_496_ = lean_ctor_get(v_x_493_, 1);
if (lean_obj_tag(v_tail_496_) == 0)
{
lean_object* v_head_497_; lean_object* v___x_498_; 
lean_dec(v_x_494_);
v_head_497_ = lean_ctor_get(v_x_493_, 0);
lean_inc(v_head_497_);
lean_dec_ref(v_x_493_);
v___x_498_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg(v_head_497_);
return v___x_498_;
}
else
{
lean_object* v_head_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
lean_inc(v_tail_496_);
v_head_499_ = lean_ctor_get(v_x_493_, 0);
lean_inc(v_head_499_);
lean_dec_ref(v_x_493_);
v___x_500_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg(v_head_499_);
v___x_501_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__2_spec__4(v_x_494_, v___x_500_, v_tail_496_);
return v___x_501_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = ((lean_object*)(l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__2));
v___x_508_ = lean_string_length(v___x_507_);
return v___x_508_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = lean_obj_once(&l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__4, &l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__4_once, _init_l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__4);
v___x_510_ = lean_nat_to_int(v___x_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg(lean_object* v_a_515_){
_start:
{
if (lean_obj_tag(v_a_515_) == 0)
{
lean_object* v___x_516_; 
v___x_516_ = ((lean_object*)(l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__1));
return v___x_516_;
}
else
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; lean_object* v___x_526_; 
v___x_517_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__1));
v___x_518_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__2(v_a_515_, v___x_517_);
v___x_519_ = lean_obj_once(&l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__5, &l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__5_once, _init_l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__5);
v___x_520_ = ((lean_object*)(l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__6));
v___x_521_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
lean_ctor_set(v___x_521_, 1, v___x_518_);
v___x_522_ = ((lean_object*)(l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__7));
v___x_523_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_521_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
v___x_524_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_519_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
v___x_525_ = 0;
v___x_526_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_526_, 0, v___x_524_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*1, v___x_525_);
return v___x_526_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprLeanOptions_repr_spec__0(lean_object* v_init_527_, lean_object* v_x_528_){
_start:
{
if (lean_obj_tag(v_x_528_) == 0)
{
lean_object* v_k_529_; lean_object* v_v_530_; lean_object* v_l_531_; lean_object* v_r_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v_k_529_ = lean_ctor_get(v_x_528_, 1);
v_v_530_ = lean_ctor_get(v_x_528_, 2);
v_l_531_ = lean_ctor_get(v_x_528_, 3);
v_r_532_ = lean_ctor_get(v_x_528_, 4);
v___x_533_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprLeanOptions_repr_spec__0(v_init_527_, v_r_532_);
lean_inc(v_v_530_);
lean_inc(v_k_529_);
v___x_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_534_, 0, v_k_529_);
lean_ctor_set(v___x_534_, 1, v_v_530_);
v___x_535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
lean_ctor_set(v___x_535_, 1, v___x_533_);
v_init_527_ = v___x_535_;
v_x_528_ = v_l_531_;
goto _start;
}
else
{
return v_init_527_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprLeanOptions_repr_spec__0___boxed(lean_object* v_init_537_, lean_object* v_x_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprLeanOptions_repr_spec__0(v_init_537_, v_x_538_);
lean_dec(v_x_538_);
return v_res_539_;
}
}
static lean_object* _init_l_Lean_instReprLeanOptions_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = lean_unsigned_to_nat(10u);
v___x_550_ = lean_nat_to_int(v___x_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLeanOptions_repr___redArg(lean_object* v_x_554_){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_555_ = ((lean_object*)(l_Lean_instReprLeanOptions_repr___redArg___closed__3));
v___x_556_ = lean_obj_once(&l_Lean_instReprLeanOptions_repr___redArg___closed__4, &l_Lean_instReprLeanOptions_repr___redArg___closed__4_once, _init_l_Lean_instReprLeanOptions_repr___redArg___closed__4);
v___x_557_ = lean_unsigned_to_nat(0u);
v___x_558_ = ((lean_object*)(l_Lean_instReprLeanOptions_repr___redArg___closed__6));
v___x_559_ = lean_box(0);
v___x_560_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprLeanOptions_repr_spec__0(v___x_559_, v_x_554_);
v___x_561_ = l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg(v___x_560_);
v___x_562_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_558_);
lean_ctor_set(v___x_562_, 1, v___x_561_);
v___x_563_ = l_Repr_addAppParen(v___x_562_, v___x_557_);
v___x_564_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_556_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
v___x_565_ = 0;
v___x_566_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_566_, 0, v___x_564_);
lean_ctor_set_uint8(v___x_566_, sizeof(void*)*1, v___x_565_);
v___x_567_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_555_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
v___x_568_ = lean_obj_once(&l_Lean_instReprLeanOption_repr___redArg___closed__15, &l_Lean_instReprLeanOption_repr___redArg___closed__15_once, _init_l_Lean_instReprLeanOption_repr___redArg___closed__15);
v___x_569_ = ((lean_object*)(l_Lean_instReprLeanOption_repr___redArg___closed__16));
v___x_570_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
lean_ctor_set(v___x_570_, 1, v___x_567_);
v___x_571_ = ((lean_object*)(l_Lean_instReprLeanOption_repr___redArg___closed__17));
v___x_572_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_570_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v___x_573_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_568_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
v___x_574_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_574_, 0, v___x_573_);
lean_ctor_set_uint8(v___x_574_, sizeof(void*)*1, v___x_565_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLeanOptions_repr___redArg___boxed(lean_object* v_x_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_instReprLeanOptions_repr___redArg(v_x_575_);
lean_dec(v_x_575_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLeanOptions_repr(lean_object* v_x_577_, lean_object* v_prec_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_instReprLeanOptions_repr___redArg(v_x_577_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLeanOptions_repr___boxed(lean_object* v_x_580_, lean_object* v_prec_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Lean_instReprLeanOptions_repr(v_x_580_, v_prec_581_);
lean_dec(v_prec_581_);
lean_dec(v_x_580_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1(lean_object* v_a_583_, lean_object* v_n_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg(v_a_583_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___boxed(lean_object* v_a_586_, lean_object* v_n_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1(v_a_586_, v_n_587_);
lean_dec(v_n_587_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1(lean_object* v_x_589_, lean_object* v_x_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg(v_x_589_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___boxed(lean_object* v_x_592_, lean_object* v_x_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1(v_x_592_, v_x_593_);
lean_dec(v_x_593_);
return v_res_594_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionLeanOptions(void){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = lean_box(1);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LeanOptions_ofArray_spec__0(lean_object* v_as_598_, size_t v_i_599_, size_t v_stop_600_, lean_object* v_b_601_){
_start:
{
uint8_t v___x_602_; 
v___x_602_ = lean_usize_dec_eq(v_i_599_, v_stop_600_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; lean_object* v_name_604_; lean_object* v_value_605_; lean_object* v___x_606_; size_t v___x_607_; size_t v___x_608_; 
v___x_603_ = lean_array_uget_borrowed(v_as_598_, v_i_599_);
v_name_604_ = lean_ctor_get(v___x_603_, 0);
v_value_605_ = lean_ctor_get(v___x_603_, 1);
lean_inc_ref(v_value_605_);
lean_inc(v_name_604_);
v___x_606_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_604_, v_value_605_, v_b_601_);
v___x_607_ = ((size_t)1ULL);
v___x_608_ = lean_usize_add(v_i_599_, v___x_607_);
v_i_599_ = v___x_608_;
v_b_601_ = v___x_606_;
goto _start;
}
else
{
return v_b_601_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LeanOptions_ofArray_spec__0___boxed(lean_object* v_as_610_, lean_object* v_i_611_, lean_object* v_stop_612_, lean_object* v_b_613_){
_start:
{
size_t v_i_boxed_614_; size_t v_stop_boxed_615_; lean_object* v_res_616_; 
v_i_boxed_614_ = lean_unbox_usize(v_i_611_);
lean_dec(v_i_611_);
v_stop_boxed_615_ = lean_unbox_usize(v_stop_612_);
lean_dec(v_stop_612_);
v_res_616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LeanOptions_ofArray_spec__0(v_as_610_, v_i_boxed_614_, v_stop_boxed_615_, v_b_613_);
lean_dec_ref(v_as_610_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptions_ofArray(lean_object* v_opts_617_){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_618_ = lean_box(1);
v___x_619_ = lean_unsigned_to_nat(0u);
v___x_620_ = lean_array_get_size(v_opts_617_);
v___x_621_ = lean_nat_dec_lt(v___x_619_, v___x_620_);
if (v___x_621_ == 0)
{
return v___x_618_;
}
else
{
uint8_t v___x_622_; 
v___x_622_ = lean_nat_dec_le(v___x_620_, v___x_620_);
if (v___x_622_ == 0)
{
if (v___x_621_ == 0)
{
return v___x_618_;
}
else
{
size_t v___x_623_; size_t v___x_624_; lean_object* v___x_625_; 
v___x_623_ = ((size_t)0ULL);
v___x_624_ = lean_usize_of_nat(v___x_620_);
v___x_625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LeanOptions_ofArray_spec__0(v_opts_617_, v___x_623_, v___x_624_, v___x_618_);
return v___x_625_;
}
}
else
{
size_t v___x_626_; size_t v___x_627_; lean_object* v___x_628_; 
v___x_626_ = ((size_t)0ULL);
v___x_627_ = lean_usize_of_nat(v___x_620_);
v___x_628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LeanOptions_ofArray_spec__0(v_opts_617_, v___x_626_, v___x_627_, v___x_618_);
return v___x_628_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptions_ofArray___boxed(lean_object* v_opts_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Lean_LeanOptions_ofArray(v_opts_629_);
lean_dec_ref(v_opts_629_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LeanOptions_append_spec__0___redArg(lean_object* v_b_u2082_631_, lean_object* v_k_632_, lean_object* v_t_633_){
_start:
{
if (lean_obj_tag(v_t_633_) == 0)
{
lean_object* v_size_634_; lean_object* v_k_635_; lean_object* v_v_636_; lean_object* v_l_637_; lean_object* v_r_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_650_; 
v_size_634_ = lean_ctor_get(v_t_633_, 0);
v_k_635_ = lean_ctor_get(v_t_633_, 1);
v_v_636_ = lean_ctor_get(v_t_633_, 2);
v_l_637_ = lean_ctor_get(v_t_633_, 3);
v_r_638_ = lean_ctor_get(v_t_633_, 4);
v_isSharedCheck_650_ = !lean_is_exclusive(v_t_633_);
if (v_isSharedCheck_650_ == 0)
{
v___x_640_ = v_t_633_;
v_isShared_641_ = v_isSharedCheck_650_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_r_638_);
lean_inc(v_l_637_);
lean_inc(v_v_636_);
lean_inc(v_k_635_);
lean_inc(v_size_634_);
lean_dec(v_t_633_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_650_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
uint8_t v___x_642_; 
v___x_642_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_632_, v_k_635_);
switch(v___x_642_)
{
case 0:
{
lean_object* v_impl_643_; lean_object* v___x_644_; 
lean_del_object(v___x_640_);
lean_dec(v_size_634_);
v_impl_643_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LeanOptions_append_spec__0___redArg(v_b_u2082_631_, v_k_632_, v_l_637_);
v___x_644_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_635_, v_v_636_, v_impl_643_, v_r_638_);
return v___x_644_;
}
case 1:
{
lean_object* v___x_646_; 
lean_dec(v_v_636_);
lean_dec(v_k_635_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 2, v_b_u2082_631_);
lean_ctor_set(v___x_640_, 1, v_k_632_);
v___x_646_ = v___x_640_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_size_634_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_k_632_);
lean_ctor_set(v_reuseFailAlloc_647_, 2, v_b_u2082_631_);
lean_ctor_set(v_reuseFailAlloc_647_, 3, v_l_637_);
lean_ctor_set(v_reuseFailAlloc_647_, 4, v_r_638_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
default: 
{
lean_object* v_impl_648_; lean_object* v___x_649_; 
lean_del_object(v___x_640_);
lean_dec(v_size_634_);
v_impl_648_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LeanOptions_append_spec__0___redArg(v_b_u2082_631_, v_k_632_, v_r_638_);
v___x_649_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_635_, v_v_636_, v_l_637_, v_impl_648_);
return v___x_649_;
}
}
}
}
else
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_unsigned_to_nat(1u);
v___x_652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v_k_632_);
lean_ctor_set(v___x_652_, 2, v_b_u2082_631_);
lean_ctor_set(v___x_652_, 3, v_t_633_);
lean_ctor_set(v___x_652_, 4, v_t_633_);
return v___x_652_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LeanOptions_append_spec__1_spec__1(lean_object* v_init_653_, lean_object* v_x_654_){
_start:
{
if (lean_obj_tag(v_x_654_) == 0)
{
lean_object* v_k_655_; lean_object* v_v_656_; lean_object* v_l_657_; lean_object* v_r_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v_k_655_ = lean_ctor_get(v_x_654_, 1);
lean_inc(v_k_655_);
v_v_656_ = lean_ctor_get(v_x_654_, 2);
lean_inc(v_v_656_);
v_l_657_ = lean_ctor_get(v_x_654_, 3);
lean_inc(v_l_657_);
v_r_658_ = lean_ctor_get(v_x_654_, 4);
lean_inc(v_r_658_);
lean_dec_ref(v_x_654_);
v___x_659_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LeanOptions_append_spec__1_spec__1(v_init_653_, v_l_657_);
v___x_660_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LeanOptions_append_spec__0___redArg(v_v_656_, v_k_655_, v___x_659_);
v_init_653_ = v___x_660_;
v_x_654_ = v_r_658_;
goto _start;
}
else
{
return v_init_653_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptions_append(lean_object* v_self_662_, lean_object* v_new_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LeanOptions_append_spec__1_spec__1(v_self_662_, v_new_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LeanOptions_append_spec__0(lean_object* v_b_u2082_665_, lean_object* v_k_666_, lean_object* v_t_667_, lean_object* v_hl_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LeanOptions_append_spec__0___redArg(v_b_u2082_665_, v_k_666_, v_t_667_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LeanOptions_append_spec__1(lean_object* v_init_670_, lean_object* v_t_671_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LeanOptions_append_spec__1_spec__1(v_init_670_, v_t_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptions_appendArray(lean_object* v_self_675_, lean_object* v_new_676_){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; uint8_t v___x_679_; 
v___x_677_ = lean_unsigned_to_nat(0u);
v___x_678_ = lean_array_get_size(v_new_676_);
v___x_679_ = lean_nat_dec_lt(v___x_677_, v___x_678_);
if (v___x_679_ == 0)
{
return v_self_675_;
}
else
{
uint8_t v___x_680_; 
v___x_680_ = lean_nat_dec_le(v___x_678_, v___x_678_);
if (v___x_680_ == 0)
{
if (v___x_679_ == 0)
{
return v_self_675_;
}
else
{
size_t v___x_681_; size_t v___x_682_; lean_object* v___x_683_; 
v___x_681_ = ((size_t)0ULL);
v___x_682_ = lean_usize_of_nat(v___x_678_);
v___x_683_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LeanOptions_ofArray_spec__0(v_new_676_, v___x_681_, v___x_682_, v_self_675_);
return v___x_683_;
}
}
else
{
size_t v___x_684_; size_t v___x_685_; lean_object* v___x_686_; 
v___x_684_ = ((size_t)0ULL);
v___x_685_ = lean_usize_of_nat(v___x_678_);
v___x_686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LeanOptions_ofArray_spec__0(v_new_676_, v___x_684_, v___x_685_, v_self_675_);
return v___x_686_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptions_appendArray___boxed(lean_object* v_self_687_, lean_object* v_new_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_LeanOptions_appendArray(v_self_687_, v_new_688_);
lean_dec_ref(v_new_688_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0(lean_object* v_o_695_, lean_object* v_k_696_, lean_object* v_v_697_){
_start:
{
lean_object* v_map_698_; uint8_t v_hasTrace_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_712_; 
v_map_698_ = lean_ctor_get(v_o_695_, 0);
v_hasTrace_699_ = lean_ctor_get_uint8(v_o_695_, sizeof(void*)*1);
v_isSharedCheck_712_ = !lean_is_exclusive(v_o_695_);
if (v_isSharedCheck_712_ == 0)
{
v___x_701_ = v_o_695_;
v_isShared_702_ = v_isSharedCheck_712_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_map_698_);
lean_dec(v_o_695_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_712_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_703_; 
lean_inc(v_k_696_);
v___x_703_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_696_, v_v_697_, v_map_698_);
if (v_hasTrace_699_ == 0)
{
lean_object* v___x_704_; uint8_t v___x_705_; lean_object* v___x_707_; 
v___x_704_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0___closed__1));
v___x_705_ = l_Lean_Name_isPrefixOf(v___x_704_, v_k_696_);
lean_dec(v_k_696_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v___x_703_);
v___x_707_ = v___x_701_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_703_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_ctor_set_uint8(v___x_707_, sizeof(void*)*1, v___x_705_);
return v___x_707_;
}
}
else
{
lean_object* v___x_710_; 
lean_dec(v_k_696_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v___x_703_);
v___x_710_ = v___x_701_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_703_);
lean_ctor_set_uint8(v_reuseFailAlloc_711_, sizeof(void*)*1, v_hasTrace_699_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_LeanOptions_toOptions_spec__1(lean_object* v_init_713_, lean_object* v_x_714_){
_start:
{
if (lean_obj_tag(v_x_714_) == 0)
{
lean_object* v_k_715_; lean_object* v_v_716_; lean_object* v_l_717_; lean_object* v_r_718_; lean_object* v___x_719_; lean_object* v_a_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v_k_715_ = lean_ctor_get(v_x_714_, 1);
lean_inc(v_k_715_);
v_v_716_ = lean_ctor_get(v_x_714_, 2);
lean_inc(v_v_716_);
v_l_717_ = lean_ctor_get(v_x_714_, 3);
lean_inc(v_l_717_);
v_r_718_ = lean_ctor_get(v_x_714_, 4);
lean_inc(v_r_718_);
lean_dec_ref(v_x_714_);
v___x_719_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_LeanOptions_toOptions_spec__1(v_init_713_, v_l_717_);
v_a_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_a_720_);
lean_dec_ref(v___x_719_);
v___x_721_ = l_Lean_LeanOptionValue_toDataValue(v_v_716_);
v___x_722_ = l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0(v_a_720_, v_k_715_, v___x_721_);
v_init_713_ = v___x_722_;
v_x_714_ = v_r_718_;
goto _start;
}
else
{
lean_object* v___x_724_; 
v___x_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_724_, 0, v_init_713_);
return v___x_724_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptions_toOptions(lean_object* v_leanOptions_725_){
_start:
{
lean_object* v_options_726_; lean_object* v___x_727_; lean_object* v_a_728_; 
v_options_726_ = l_Lean_Options_empty;
v___x_727_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_LeanOptions_toOptions_spec__1(v_options_726_, v_leanOptions_725_);
v_a_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_a_728_);
lean_dec_ref(v___x_727_);
return v_a_728_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_LeanOptions_fromOptions_x3f_spec__0___redArg(lean_object* v_k_729_, lean_object* v_v_730_, lean_object* v_t_731_){
_start:
{
if (lean_obj_tag(v_t_731_) == 0)
{
lean_object* v_size_732_; lean_object* v_k_733_; lean_object* v_v_734_; lean_object* v_l_735_; lean_object* v_r_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_1016_; 
v_size_732_ = lean_ctor_get(v_t_731_, 0);
v_k_733_ = lean_ctor_get(v_t_731_, 1);
v_v_734_ = lean_ctor_get(v_t_731_, 2);
v_l_735_ = lean_ctor_get(v_t_731_, 3);
v_r_736_ = lean_ctor_get(v_t_731_, 4);
v_isSharedCheck_1016_ = !lean_is_exclusive(v_t_731_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_738_ = v_t_731_;
v_isShared_739_ = v_isSharedCheck_1016_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_r_736_);
lean_inc(v_l_735_);
lean_inc(v_v_734_);
lean_inc(v_k_733_);
lean_inc(v_size_732_);
lean_dec(v_t_731_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_1016_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
uint8_t v___x_740_; 
v___x_740_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_729_, v_k_733_);
switch(v___x_740_)
{
case 0:
{
lean_object* v_impl_741_; lean_object* v___x_742_; 
lean_dec(v_size_732_);
v_impl_741_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_LeanOptions_fromOptions_x3f_spec__0___redArg(v_k_729_, v_v_730_, v_l_735_);
v___x_742_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_736_) == 0)
{
lean_object* v_size_743_; lean_object* v_size_744_; lean_object* v_k_745_; lean_object* v_v_746_; lean_object* v_l_747_; lean_object* v_r_748_; lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v_size_743_ = lean_ctor_get(v_r_736_, 0);
v_size_744_ = lean_ctor_get(v_impl_741_, 0);
lean_inc(v_size_744_);
v_k_745_ = lean_ctor_get(v_impl_741_, 1);
lean_inc(v_k_745_);
v_v_746_ = lean_ctor_get(v_impl_741_, 2);
lean_inc(v_v_746_);
v_l_747_ = lean_ctor_get(v_impl_741_, 3);
lean_inc(v_l_747_);
v_r_748_ = lean_ctor_get(v_impl_741_, 4);
lean_inc(v_r_748_);
v___x_749_ = lean_unsigned_to_nat(3u);
v___x_750_ = lean_nat_mul(v___x_749_, v_size_743_);
v___x_751_ = lean_nat_dec_lt(v___x_750_, v_size_744_);
lean_dec(v___x_750_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_755_; 
lean_dec(v_r_748_);
lean_dec(v_l_747_);
lean_dec(v_v_746_);
lean_dec(v_k_745_);
v___x_752_ = lean_nat_add(v___x_742_, v_size_744_);
lean_dec(v_size_744_);
v___x_753_ = lean_nat_add(v___x_752_, v_size_743_);
lean_dec(v___x_752_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 3, v_impl_741_);
lean_ctor_set(v___x_738_, 0, v___x_753_);
v___x_755_ = v___x_738_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_753_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v_k_733_);
lean_ctor_set(v_reuseFailAlloc_756_, 2, v_v_734_);
lean_ctor_set(v_reuseFailAlloc_756_, 3, v_impl_741_);
lean_ctor_set(v_reuseFailAlloc_756_, 4, v_r_736_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
else
{
lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_822_; 
v_isSharedCheck_822_ = !lean_is_exclusive(v_impl_741_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; lean_object* v_unused_824_; lean_object* v_unused_825_; lean_object* v_unused_826_; lean_object* v_unused_827_; 
v_unused_823_ = lean_ctor_get(v_impl_741_, 4);
lean_dec(v_unused_823_);
v_unused_824_ = lean_ctor_get(v_impl_741_, 3);
lean_dec(v_unused_824_);
v_unused_825_ = lean_ctor_get(v_impl_741_, 2);
lean_dec(v_unused_825_);
v_unused_826_ = lean_ctor_get(v_impl_741_, 1);
lean_dec(v_unused_826_);
v_unused_827_ = lean_ctor_get(v_impl_741_, 0);
lean_dec(v_unused_827_);
v___x_758_ = v_impl_741_;
v_isShared_759_ = v_isSharedCheck_822_;
goto v_resetjp_757_;
}
else
{
lean_dec(v_impl_741_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_822_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v_size_760_; lean_object* v_size_761_; lean_object* v_k_762_; lean_object* v_v_763_; lean_object* v_l_764_; lean_object* v_r_765_; lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; 
v_size_760_ = lean_ctor_get(v_l_747_, 0);
v_size_761_ = lean_ctor_get(v_r_748_, 0);
v_k_762_ = lean_ctor_get(v_r_748_, 1);
v_v_763_ = lean_ctor_get(v_r_748_, 2);
v_l_764_ = lean_ctor_get(v_r_748_, 3);
v_r_765_ = lean_ctor_get(v_r_748_, 4);
v___x_766_ = lean_unsigned_to_nat(2u);
v___x_767_ = lean_nat_mul(v___x_766_, v_size_760_);
v___x_768_ = lean_nat_dec_lt(v_size_761_, v___x_767_);
lean_dec(v___x_767_);
if (v___x_768_ == 0)
{
lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_797_; 
lean_inc(v_r_765_);
lean_inc(v_l_764_);
lean_inc(v_v_763_);
lean_inc(v_k_762_);
v_isSharedCheck_797_ = !lean_is_exclusive(v_r_748_);
if (v_isSharedCheck_797_ == 0)
{
lean_object* v_unused_798_; lean_object* v_unused_799_; lean_object* v_unused_800_; lean_object* v_unused_801_; lean_object* v_unused_802_; 
v_unused_798_ = lean_ctor_get(v_r_748_, 4);
lean_dec(v_unused_798_);
v_unused_799_ = lean_ctor_get(v_r_748_, 3);
lean_dec(v_unused_799_);
v_unused_800_ = lean_ctor_get(v_r_748_, 2);
lean_dec(v_unused_800_);
v_unused_801_ = lean_ctor_get(v_r_748_, 1);
lean_dec(v_unused_801_);
v_unused_802_ = lean_ctor_get(v_r_748_, 0);
lean_dec(v_unused_802_);
v___x_770_ = v_r_748_;
v_isShared_771_ = v_isSharedCheck_797_;
goto v_resetjp_769_;
}
else
{
lean_dec(v_r_748_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_797_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v___x_785_; lean_object* v___y_787_; 
v___x_772_ = lean_nat_add(v___x_742_, v_size_744_);
lean_dec(v_size_744_);
v___x_773_ = lean_nat_add(v___x_772_, v_size_743_);
lean_dec(v___x_772_);
v___x_785_ = lean_nat_add(v___x_742_, v_size_760_);
if (lean_obj_tag(v_l_764_) == 0)
{
lean_object* v_size_795_; 
v_size_795_ = lean_ctor_get(v_l_764_, 0);
lean_inc(v_size_795_);
v___y_787_ = v_size_795_;
goto v___jp_786_;
}
else
{
lean_object* v___x_796_; 
v___x_796_ = lean_unsigned_to_nat(0u);
v___y_787_ = v___x_796_;
goto v___jp_786_;
}
v___jp_774_:
{
lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_778_ = lean_nat_add(v___y_775_, v___y_777_);
lean_dec(v___y_777_);
lean_dec(v___y_775_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 4, v_r_736_);
lean_ctor_set(v___x_770_, 3, v_r_765_);
lean_ctor_set(v___x_770_, 2, v_v_734_);
lean_ctor_set(v___x_770_, 1, v_k_733_);
lean_ctor_set(v___x_770_, 0, v___x_778_);
v___x_780_ = v___x_770_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_778_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_k_733_);
lean_ctor_set(v_reuseFailAlloc_784_, 2, v_v_734_);
lean_ctor_set(v_reuseFailAlloc_784_, 3, v_r_765_);
lean_ctor_set(v_reuseFailAlloc_784_, 4, v_r_736_);
v___x_780_ = v_reuseFailAlloc_784_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_782_; 
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 4, v___x_780_);
lean_ctor_set(v___x_758_, 3, v___y_776_);
lean_ctor_set(v___x_758_, 2, v_v_763_);
lean_ctor_set(v___x_758_, 1, v_k_762_);
lean_ctor_set(v___x_758_, 0, v___x_773_);
v___x_782_ = v___x_758_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_773_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_k_762_);
lean_ctor_set(v_reuseFailAlloc_783_, 2, v_v_763_);
lean_ctor_set(v_reuseFailAlloc_783_, 3, v___y_776_);
lean_ctor_set(v_reuseFailAlloc_783_, 4, v___x_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
v___jp_786_:
{
lean_object* v___x_788_; lean_object* v___x_790_; 
v___x_788_ = lean_nat_add(v___x_785_, v___y_787_);
lean_dec(v___y_787_);
lean_dec(v___x_785_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 4, v_l_764_);
lean_ctor_set(v___x_738_, 3, v_l_747_);
lean_ctor_set(v___x_738_, 2, v_v_746_);
lean_ctor_set(v___x_738_, 1, v_k_745_);
lean_ctor_set(v___x_738_, 0, v___x_788_);
v___x_790_ = v___x_738_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_k_745_);
lean_ctor_set(v_reuseFailAlloc_794_, 2, v_v_746_);
lean_ctor_set(v_reuseFailAlloc_794_, 3, v_l_747_);
lean_ctor_set(v_reuseFailAlloc_794_, 4, v_l_764_);
v___x_790_ = v_reuseFailAlloc_794_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_791_; 
v___x_791_ = lean_nat_add(v___x_742_, v_size_743_);
if (lean_obj_tag(v_r_765_) == 0)
{
lean_object* v_size_792_; 
v_size_792_ = lean_ctor_get(v_r_765_, 0);
lean_inc(v_size_792_);
v___y_775_ = v___x_791_;
v___y_776_ = v___x_790_;
v___y_777_ = v_size_792_;
goto v___jp_774_;
}
else
{
lean_object* v___x_793_; 
v___x_793_ = lean_unsigned_to_nat(0u);
v___y_775_ = v___x_791_;
v___y_776_ = v___x_790_;
v___y_777_ = v___x_793_;
goto v___jp_774_;
}
}
}
}
}
else
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_808_; 
lean_del_object(v___x_738_);
v___x_803_ = lean_nat_add(v___x_742_, v_size_744_);
lean_dec(v_size_744_);
v___x_804_ = lean_nat_add(v___x_803_, v_size_743_);
lean_dec(v___x_803_);
v___x_805_ = lean_nat_add(v___x_742_, v_size_743_);
v___x_806_ = lean_nat_add(v___x_805_, v_size_761_);
lean_dec(v___x_805_);
lean_inc_ref(v_r_736_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 4, v_r_736_);
lean_ctor_set(v___x_758_, 3, v_r_748_);
lean_ctor_set(v___x_758_, 2, v_v_734_);
lean_ctor_set(v___x_758_, 1, v_k_733_);
lean_ctor_set(v___x_758_, 0, v___x_806_);
v___x_808_ = v___x_758_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_k_733_);
lean_ctor_set(v_reuseFailAlloc_821_, 2, v_v_734_);
lean_ctor_set(v_reuseFailAlloc_821_, 3, v_r_748_);
lean_ctor_set(v_reuseFailAlloc_821_, 4, v_r_736_);
v___x_808_ = v_reuseFailAlloc_821_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
v_isSharedCheck_815_ = !lean_is_exclusive(v_r_736_);
if (v_isSharedCheck_815_ == 0)
{
lean_object* v_unused_816_; lean_object* v_unused_817_; lean_object* v_unused_818_; lean_object* v_unused_819_; lean_object* v_unused_820_; 
v_unused_816_ = lean_ctor_get(v_r_736_, 4);
lean_dec(v_unused_816_);
v_unused_817_ = lean_ctor_get(v_r_736_, 3);
lean_dec(v_unused_817_);
v_unused_818_ = lean_ctor_get(v_r_736_, 2);
lean_dec(v_unused_818_);
v_unused_819_ = lean_ctor_get(v_r_736_, 1);
lean_dec(v_unused_819_);
v_unused_820_ = lean_ctor_get(v_r_736_, 0);
lean_dec(v_unused_820_);
v___x_810_ = v_r_736_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_dec(v_r_736_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 4, v___x_808_);
lean_ctor_set(v___x_810_, 3, v_l_747_);
lean_ctor_set(v___x_810_, 2, v_v_746_);
lean_ctor_set(v___x_810_, 1, v_k_745_);
lean_ctor_set(v___x_810_, 0, v___x_804_);
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_804_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_k_745_);
lean_ctor_set(v_reuseFailAlloc_814_, 2, v_v_746_);
lean_ctor_set(v_reuseFailAlloc_814_, 3, v_l_747_);
lean_ctor_set(v_reuseFailAlloc_814_, 4, v___x_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_828_; 
v_l_828_ = lean_ctor_get(v_impl_741_, 3);
lean_inc(v_l_828_);
if (lean_obj_tag(v_l_828_) == 0)
{
lean_object* v_r_829_; lean_object* v_k_830_; lean_object* v_v_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_842_; 
v_r_829_ = lean_ctor_get(v_impl_741_, 4);
v_k_830_ = lean_ctor_get(v_impl_741_, 1);
v_v_831_ = lean_ctor_get(v_impl_741_, 2);
v_isSharedCheck_842_ = !lean_is_exclusive(v_impl_741_);
if (v_isSharedCheck_842_ == 0)
{
lean_object* v_unused_843_; lean_object* v_unused_844_; 
v_unused_843_ = lean_ctor_get(v_impl_741_, 3);
lean_dec(v_unused_843_);
v_unused_844_ = lean_ctor_get(v_impl_741_, 0);
lean_dec(v_unused_844_);
v___x_833_ = v_impl_741_;
v_isShared_834_ = v_isSharedCheck_842_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_r_829_);
lean_inc(v_v_831_);
lean_inc(v_k_830_);
lean_dec(v_impl_741_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_842_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_835_; lean_object* v___x_837_; 
v___x_835_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_829_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 3, v_r_829_);
lean_ctor_set(v___x_833_, 2, v_v_734_);
lean_ctor_set(v___x_833_, 1, v_k_733_);
lean_ctor_set(v___x_833_, 0, v___x_742_);
v___x_837_ = v___x_833_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_742_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v_k_733_);
lean_ctor_set(v_reuseFailAlloc_841_, 2, v_v_734_);
lean_ctor_set(v_reuseFailAlloc_841_, 3, v_r_829_);
lean_ctor_set(v_reuseFailAlloc_841_, 4, v_r_829_);
v___x_837_ = v_reuseFailAlloc_841_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
lean_object* v___x_839_; 
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 4, v___x_837_);
lean_ctor_set(v___x_738_, 3, v_l_828_);
lean_ctor_set(v___x_738_, 2, v_v_831_);
lean_ctor_set(v___x_738_, 1, v_k_830_);
lean_ctor_set(v___x_738_, 0, v___x_835_);
v___x_839_ = v___x_738_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_835_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_k_830_);
lean_ctor_set(v_reuseFailAlloc_840_, 2, v_v_831_);
lean_ctor_set(v_reuseFailAlloc_840_, 3, v_l_828_);
lean_ctor_set(v_reuseFailAlloc_840_, 4, v___x_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
else
{
lean_object* v_r_845_; 
v_r_845_ = lean_ctor_get(v_impl_741_, 4);
lean_inc(v_r_845_);
if (lean_obj_tag(v_r_845_) == 0)
{
lean_object* v_k_846_; lean_object* v_v_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_870_; 
v_k_846_ = lean_ctor_get(v_impl_741_, 1);
v_v_847_ = lean_ctor_get(v_impl_741_, 2);
v_isSharedCheck_870_ = !lean_is_exclusive(v_impl_741_);
if (v_isSharedCheck_870_ == 0)
{
lean_object* v_unused_871_; lean_object* v_unused_872_; lean_object* v_unused_873_; 
v_unused_871_ = lean_ctor_get(v_impl_741_, 4);
lean_dec(v_unused_871_);
v_unused_872_ = lean_ctor_get(v_impl_741_, 3);
lean_dec(v_unused_872_);
v_unused_873_ = lean_ctor_get(v_impl_741_, 0);
lean_dec(v_unused_873_);
v___x_849_ = v_impl_741_;
v_isShared_850_ = v_isSharedCheck_870_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_v_847_);
lean_inc(v_k_846_);
lean_dec(v_impl_741_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_870_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v_k_851_; lean_object* v_v_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_866_; 
v_k_851_ = lean_ctor_get(v_r_845_, 1);
v_v_852_ = lean_ctor_get(v_r_845_, 2);
v_isSharedCheck_866_ = !lean_is_exclusive(v_r_845_);
if (v_isSharedCheck_866_ == 0)
{
lean_object* v_unused_867_; lean_object* v_unused_868_; lean_object* v_unused_869_; 
v_unused_867_ = lean_ctor_get(v_r_845_, 4);
lean_dec(v_unused_867_);
v_unused_868_ = lean_ctor_get(v_r_845_, 3);
lean_dec(v_unused_868_);
v_unused_869_ = lean_ctor_get(v_r_845_, 0);
lean_dec(v_unused_869_);
v___x_854_ = v_r_845_;
v_isShared_855_ = v_isSharedCheck_866_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_v_852_);
lean_inc(v_k_851_);
lean_dec(v_r_845_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_866_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_856_ = lean_unsigned_to_nat(3u);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 4, v_l_828_);
lean_ctor_set(v___x_854_, 3, v_l_828_);
lean_ctor_set(v___x_854_, 2, v_v_847_);
lean_ctor_set(v___x_854_, 1, v_k_846_);
lean_ctor_set(v___x_854_, 0, v___x_742_);
v___x_858_ = v___x_854_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_742_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_k_846_);
lean_ctor_set(v_reuseFailAlloc_865_, 2, v_v_847_);
lean_ctor_set(v_reuseFailAlloc_865_, 3, v_l_828_);
lean_ctor_set(v_reuseFailAlloc_865_, 4, v_l_828_);
v___x_858_ = v_reuseFailAlloc_865_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
lean_object* v___x_860_; 
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 4, v_l_828_);
lean_ctor_set(v___x_849_, 2, v_v_734_);
lean_ctor_set(v___x_849_, 1, v_k_733_);
lean_ctor_set(v___x_849_, 0, v___x_742_);
v___x_860_ = v___x_849_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_742_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v_k_733_);
lean_ctor_set(v_reuseFailAlloc_864_, 2, v_v_734_);
lean_ctor_set(v_reuseFailAlloc_864_, 3, v_l_828_);
lean_ctor_set(v_reuseFailAlloc_864_, 4, v_l_828_);
v___x_860_ = v_reuseFailAlloc_864_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_862_; 
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 4, v___x_860_);
lean_ctor_set(v___x_738_, 3, v___x_858_);
lean_ctor_set(v___x_738_, 2, v_v_852_);
lean_ctor_set(v___x_738_, 1, v_k_851_);
lean_ctor_set(v___x_738_, 0, v___x_856_);
v___x_862_ = v___x_738_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_856_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v_k_851_);
lean_ctor_set(v_reuseFailAlloc_863_, 2, v_v_852_);
lean_ctor_set(v_reuseFailAlloc_863_, 3, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_863_, 4, v___x_860_);
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
lean_object* v___x_874_; lean_object* v___x_876_; 
v___x_874_ = lean_unsigned_to_nat(2u);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 4, v_r_845_);
lean_ctor_set(v___x_738_, 3, v_impl_741_);
lean_ctor_set(v___x_738_, 0, v___x_874_);
v___x_876_ = v___x_738_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_k_733_);
lean_ctor_set(v_reuseFailAlloc_877_, 2, v_v_734_);
lean_ctor_set(v_reuseFailAlloc_877_, 3, v_impl_741_);
lean_ctor_set(v_reuseFailAlloc_877_, 4, v_r_845_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
}
case 1:
{
lean_object* v___x_879_; 
lean_dec(v_v_734_);
lean_dec(v_k_733_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 2, v_v_730_);
lean_ctor_set(v___x_738_, 1, v_k_729_);
v___x_879_ = v___x_738_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_size_732_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v_k_729_);
lean_ctor_set(v_reuseFailAlloc_880_, 2, v_v_730_);
lean_ctor_set(v_reuseFailAlloc_880_, 3, v_l_735_);
lean_ctor_set(v_reuseFailAlloc_880_, 4, v_r_736_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
default: 
{
lean_object* v_impl_881_; lean_object* v___x_882_; 
lean_dec(v_size_732_);
v_impl_881_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_LeanOptions_fromOptions_x3f_spec__0___redArg(v_k_729_, v_v_730_, v_r_736_);
v___x_882_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_735_) == 0)
{
lean_object* v_size_883_; lean_object* v_size_884_; lean_object* v_k_885_; lean_object* v_v_886_; lean_object* v_l_887_; lean_object* v_r_888_; lean_object* v___x_889_; lean_object* v___x_890_; uint8_t v___x_891_; 
v_size_883_ = lean_ctor_get(v_l_735_, 0);
v_size_884_ = lean_ctor_get(v_impl_881_, 0);
lean_inc(v_size_884_);
v_k_885_ = lean_ctor_get(v_impl_881_, 1);
lean_inc(v_k_885_);
v_v_886_ = lean_ctor_get(v_impl_881_, 2);
lean_inc(v_v_886_);
v_l_887_ = lean_ctor_get(v_impl_881_, 3);
lean_inc(v_l_887_);
v_r_888_ = lean_ctor_get(v_impl_881_, 4);
lean_inc(v_r_888_);
v___x_889_ = lean_unsigned_to_nat(3u);
v___x_890_ = lean_nat_mul(v___x_889_, v_size_883_);
v___x_891_ = lean_nat_dec_lt(v___x_890_, v_size_884_);
lean_dec(v___x_890_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_895_; 
lean_dec(v_r_888_);
lean_dec(v_l_887_);
lean_dec(v_v_886_);
lean_dec(v_k_885_);
v___x_892_ = lean_nat_add(v___x_882_, v_size_883_);
v___x_893_ = lean_nat_add(v___x_892_, v_size_884_);
lean_dec(v_size_884_);
lean_dec(v___x_892_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 4, v_impl_881_);
lean_ctor_set(v___x_738_, 0, v___x_893_);
v___x_895_ = v___x_738_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_893_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_k_733_);
lean_ctor_set(v_reuseFailAlloc_896_, 2, v_v_734_);
lean_ctor_set(v_reuseFailAlloc_896_, 3, v_l_735_);
lean_ctor_set(v_reuseFailAlloc_896_, 4, v_impl_881_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
else
{
lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_960_; 
v_isSharedCheck_960_ = !lean_is_exclusive(v_impl_881_);
if (v_isSharedCheck_960_ == 0)
{
lean_object* v_unused_961_; lean_object* v_unused_962_; lean_object* v_unused_963_; lean_object* v_unused_964_; lean_object* v_unused_965_; 
v_unused_961_ = lean_ctor_get(v_impl_881_, 4);
lean_dec(v_unused_961_);
v_unused_962_ = lean_ctor_get(v_impl_881_, 3);
lean_dec(v_unused_962_);
v_unused_963_ = lean_ctor_get(v_impl_881_, 2);
lean_dec(v_unused_963_);
v_unused_964_ = lean_ctor_get(v_impl_881_, 1);
lean_dec(v_unused_964_);
v_unused_965_ = lean_ctor_get(v_impl_881_, 0);
lean_dec(v_unused_965_);
v___x_898_ = v_impl_881_;
v_isShared_899_ = v_isSharedCheck_960_;
goto v_resetjp_897_;
}
else
{
lean_dec(v_impl_881_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_960_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v_size_900_; lean_object* v_k_901_; lean_object* v_v_902_; lean_object* v_l_903_; lean_object* v_r_904_; lean_object* v_size_905_; lean_object* v___x_906_; lean_object* v___x_907_; uint8_t v___x_908_; 
v_size_900_ = lean_ctor_get(v_l_887_, 0);
v_k_901_ = lean_ctor_get(v_l_887_, 1);
v_v_902_ = lean_ctor_get(v_l_887_, 2);
v_l_903_ = lean_ctor_get(v_l_887_, 3);
v_r_904_ = lean_ctor_get(v_l_887_, 4);
v_size_905_ = lean_ctor_get(v_r_888_, 0);
v___x_906_ = lean_unsigned_to_nat(2u);
v___x_907_ = lean_nat_mul(v___x_906_, v_size_905_);
v___x_908_ = lean_nat_dec_lt(v_size_900_, v___x_907_);
lean_dec(v___x_907_);
if (v___x_908_ == 0)
{
lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_936_; 
lean_inc(v_r_904_);
lean_inc(v_l_903_);
lean_inc(v_v_902_);
lean_inc(v_k_901_);
v_isSharedCheck_936_ = !lean_is_exclusive(v_l_887_);
if (v_isSharedCheck_936_ == 0)
{
lean_object* v_unused_937_; lean_object* v_unused_938_; lean_object* v_unused_939_; lean_object* v_unused_940_; lean_object* v_unused_941_; 
v_unused_937_ = lean_ctor_get(v_l_887_, 4);
lean_dec(v_unused_937_);
v_unused_938_ = lean_ctor_get(v_l_887_, 3);
lean_dec(v_unused_938_);
v_unused_939_ = lean_ctor_get(v_l_887_, 2);
lean_dec(v_unused_939_);
v_unused_940_ = lean_ctor_get(v_l_887_, 1);
lean_dec(v_unused_940_);
v_unused_941_ = lean_ctor_get(v_l_887_, 0);
lean_dec(v_unused_941_);
v___x_910_ = v_l_887_;
v_isShared_911_ = v_isSharedCheck_936_;
goto v_resetjp_909_;
}
else
{
lean_dec(v_l_887_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_936_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___y_915_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v___y_926_; 
v___x_912_ = lean_nat_add(v___x_882_, v_size_883_);
v___x_913_ = lean_nat_add(v___x_912_, v_size_884_);
lean_dec(v_size_884_);
if (lean_obj_tag(v_l_903_) == 0)
{
lean_object* v_size_934_; 
v_size_934_ = lean_ctor_get(v_l_903_, 0);
lean_inc(v_size_934_);
v___y_926_ = v_size_934_;
goto v___jp_925_;
}
else
{
lean_object* v___x_935_; 
v___x_935_ = lean_unsigned_to_nat(0u);
v___y_926_ = v___x_935_;
goto v___jp_925_;
}
v___jp_914_:
{
lean_object* v___x_918_; lean_object* v___x_920_; 
v___x_918_ = lean_nat_add(v___y_915_, v___y_917_);
lean_dec(v___y_917_);
lean_dec(v___y_915_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 4, v_r_888_);
lean_ctor_set(v___x_910_, 3, v_r_904_);
lean_ctor_set(v___x_910_, 2, v_v_886_);
lean_ctor_set(v___x_910_, 1, v_k_885_);
lean_ctor_set(v___x_910_, 0, v___x_918_);
v___x_920_ = v___x_910_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_918_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v_k_885_);
lean_ctor_set(v_reuseFailAlloc_924_, 2, v_v_886_);
lean_ctor_set(v_reuseFailAlloc_924_, 3, v_r_904_);
lean_ctor_set(v_reuseFailAlloc_924_, 4, v_r_888_);
v___x_920_ = v_reuseFailAlloc_924_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
lean_object* v___x_922_; 
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 4, v___x_920_);
lean_ctor_set(v___x_898_, 3, v___y_916_);
lean_ctor_set(v___x_898_, 2, v_v_902_);
lean_ctor_set(v___x_898_, 1, v_k_901_);
lean_ctor_set(v___x_898_, 0, v___x_913_);
v___x_922_ = v___x_898_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_913_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v_k_901_);
lean_ctor_set(v_reuseFailAlloc_923_, 2, v_v_902_);
lean_ctor_set(v_reuseFailAlloc_923_, 3, v___y_916_);
lean_ctor_set(v_reuseFailAlloc_923_, 4, v___x_920_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
v___jp_925_:
{
lean_object* v___x_927_; lean_object* v___x_929_; 
v___x_927_ = lean_nat_add(v___x_912_, v___y_926_);
lean_dec(v___y_926_);
lean_dec(v___x_912_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 4, v_l_903_);
lean_ctor_set(v___x_738_, 0, v___x_927_);
v___x_929_ = v___x_738_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_927_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v_k_733_);
lean_ctor_set(v_reuseFailAlloc_933_, 2, v_v_734_);
lean_ctor_set(v_reuseFailAlloc_933_, 3, v_l_735_);
lean_ctor_set(v_reuseFailAlloc_933_, 4, v_l_903_);
v___x_929_ = v_reuseFailAlloc_933_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
lean_object* v___x_930_; 
v___x_930_ = lean_nat_add(v___x_882_, v_size_905_);
if (lean_obj_tag(v_r_904_) == 0)
{
lean_object* v_size_931_; 
v_size_931_ = lean_ctor_get(v_r_904_, 0);
lean_inc(v_size_931_);
v___y_915_ = v___x_930_;
v___y_916_ = v___x_929_;
v___y_917_ = v_size_931_;
goto v___jp_914_;
}
else
{
lean_object* v___x_932_; 
v___x_932_ = lean_unsigned_to_nat(0u);
v___y_915_ = v___x_930_;
v___y_916_ = v___x_929_;
v___y_917_ = v___x_932_;
goto v___jp_914_;
}
}
}
}
}
else
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_946_; 
lean_del_object(v___x_738_);
v___x_942_ = lean_nat_add(v___x_882_, v_size_883_);
v___x_943_ = lean_nat_add(v___x_942_, v_size_884_);
lean_dec(v_size_884_);
v___x_944_ = lean_nat_add(v___x_942_, v_size_900_);
lean_dec(v___x_942_);
lean_inc_ref(v_l_735_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 4, v_l_887_);
lean_ctor_set(v___x_898_, 3, v_l_735_);
lean_ctor_set(v___x_898_, 2, v_v_734_);
lean_ctor_set(v___x_898_, 1, v_k_733_);
lean_ctor_set(v___x_898_, 0, v___x_944_);
v___x_946_ = v___x_898_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v_k_733_);
lean_ctor_set(v_reuseFailAlloc_959_, 2, v_v_734_);
lean_ctor_set(v_reuseFailAlloc_959_, 3, v_l_735_);
lean_ctor_set(v_reuseFailAlloc_959_, 4, v_l_887_);
v___x_946_ = v_reuseFailAlloc_959_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
v_isSharedCheck_953_ = !lean_is_exclusive(v_l_735_);
if (v_isSharedCheck_953_ == 0)
{
lean_object* v_unused_954_; lean_object* v_unused_955_; lean_object* v_unused_956_; lean_object* v_unused_957_; lean_object* v_unused_958_; 
v_unused_954_ = lean_ctor_get(v_l_735_, 4);
lean_dec(v_unused_954_);
v_unused_955_ = lean_ctor_get(v_l_735_, 3);
lean_dec(v_unused_955_);
v_unused_956_ = lean_ctor_get(v_l_735_, 2);
lean_dec(v_unused_956_);
v_unused_957_ = lean_ctor_get(v_l_735_, 1);
lean_dec(v_unused_957_);
v_unused_958_ = lean_ctor_get(v_l_735_, 0);
lean_dec(v_unused_958_);
v___x_948_ = v_l_735_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_dec(v_l_735_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 4, v_r_888_);
lean_ctor_set(v___x_948_, 3, v___x_946_);
lean_ctor_set(v___x_948_, 2, v_v_886_);
lean_ctor_set(v___x_948_, 1, v_k_885_);
lean_ctor_set(v___x_948_, 0, v___x_943_);
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_943_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_k_885_);
lean_ctor_set(v_reuseFailAlloc_952_, 2, v_v_886_);
lean_ctor_set(v_reuseFailAlloc_952_, 3, v___x_946_);
lean_ctor_set(v_reuseFailAlloc_952_, 4, v_r_888_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_966_; 
v_l_966_ = lean_ctor_get(v_impl_881_, 3);
lean_inc(v_l_966_);
if (lean_obj_tag(v_l_966_) == 0)
{
lean_object* v_r_967_; lean_object* v_k_968_; lean_object* v_v_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_992_; 
v_r_967_ = lean_ctor_get(v_impl_881_, 4);
v_k_968_ = lean_ctor_get(v_impl_881_, 1);
v_v_969_ = lean_ctor_get(v_impl_881_, 2);
v_isSharedCheck_992_ = !lean_is_exclusive(v_impl_881_);
if (v_isSharedCheck_992_ == 0)
{
lean_object* v_unused_993_; lean_object* v_unused_994_; 
v_unused_993_ = lean_ctor_get(v_impl_881_, 3);
lean_dec(v_unused_993_);
v_unused_994_ = lean_ctor_get(v_impl_881_, 0);
lean_dec(v_unused_994_);
v___x_971_ = v_impl_881_;
v_isShared_972_ = v_isSharedCheck_992_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_r_967_);
lean_inc(v_v_969_);
lean_inc(v_k_968_);
lean_dec(v_impl_881_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_992_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v_k_973_; lean_object* v_v_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_988_; 
v_k_973_ = lean_ctor_get(v_l_966_, 1);
v_v_974_ = lean_ctor_get(v_l_966_, 2);
v_isSharedCheck_988_ = !lean_is_exclusive(v_l_966_);
if (v_isSharedCheck_988_ == 0)
{
lean_object* v_unused_989_; lean_object* v_unused_990_; lean_object* v_unused_991_; 
v_unused_989_ = lean_ctor_get(v_l_966_, 4);
lean_dec(v_unused_989_);
v_unused_990_ = lean_ctor_get(v_l_966_, 3);
lean_dec(v_unused_990_);
v_unused_991_ = lean_ctor_get(v_l_966_, 0);
lean_dec(v_unused_991_);
v___x_976_ = v_l_966_;
v_isShared_977_ = v_isSharedCheck_988_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_v_974_);
lean_inc(v_k_973_);
lean_dec(v_l_966_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_988_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; lean_object* v___x_980_; 
v___x_978_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_967_, 2);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 4, v_r_967_);
lean_ctor_set(v___x_976_, 3, v_r_967_);
lean_ctor_set(v___x_976_, 2, v_v_734_);
lean_ctor_set(v___x_976_, 1, v_k_733_);
lean_ctor_set(v___x_976_, 0, v___x_882_);
v___x_980_ = v___x_976_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v_k_733_);
lean_ctor_set(v_reuseFailAlloc_987_, 2, v_v_734_);
lean_ctor_set(v_reuseFailAlloc_987_, 3, v_r_967_);
lean_ctor_set(v_reuseFailAlloc_987_, 4, v_r_967_);
v___x_980_ = v_reuseFailAlloc_987_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v___x_982_; 
lean_inc(v_r_967_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 3, v_r_967_);
lean_ctor_set(v___x_971_, 0, v___x_882_);
v___x_982_ = v___x_971_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v_k_968_);
lean_ctor_set(v_reuseFailAlloc_986_, 2, v_v_969_);
lean_ctor_set(v_reuseFailAlloc_986_, 3, v_r_967_);
lean_ctor_set(v_reuseFailAlloc_986_, 4, v_r_967_);
v___x_982_ = v_reuseFailAlloc_986_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_984_; 
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 4, v___x_982_);
lean_ctor_set(v___x_738_, 3, v___x_980_);
lean_ctor_set(v___x_738_, 2, v_v_974_);
lean_ctor_set(v___x_738_, 1, v_k_973_);
lean_ctor_set(v___x_738_, 0, v___x_978_);
v___x_984_ = v___x_738_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_978_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_k_973_);
lean_ctor_set(v_reuseFailAlloc_985_, 2, v_v_974_);
lean_ctor_set(v_reuseFailAlloc_985_, 3, v___x_980_);
lean_ctor_set(v_reuseFailAlloc_985_, 4, v___x_982_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
}
}
else
{
lean_object* v_r_995_; 
v_r_995_ = lean_ctor_get(v_impl_881_, 4);
lean_inc(v_r_995_);
if (lean_obj_tag(v_r_995_) == 0)
{
lean_object* v_k_996_; lean_object* v_v_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1008_; 
v_k_996_ = lean_ctor_get(v_impl_881_, 1);
v_v_997_ = lean_ctor_get(v_impl_881_, 2);
v_isSharedCheck_1008_ = !lean_is_exclusive(v_impl_881_);
if (v_isSharedCheck_1008_ == 0)
{
lean_object* v_unused_1009_; lean_object* v_unused_1010_; lean_object* v_unused_1011_; 
v_unused_1009_ = lean_ctor_get(v_impl_881_, 4);
lean_dec(v_unused_1009_);
v_unused_1010_ = lean_ctor_get(v_impl_881_, 3);
lean_dec(v_unused_1010_);
v_unused_1011_ = lean_ctor_get(v_impl_881_, 0);
lean_dec(v_unused_1011_);
v___x_999_ = v_impl_881_;
v_isShared_1000_ = v_isSharedCheck_1008_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_v_997_);
lean_inc(v_k_996_);
lean_dec(v_impl_881_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1008_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1001_; lean_object* v___x_1003_; 
v___x_1001_ = lean_unsigned_to_nat(3u);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 4, v_l_966_);
lean_ctor_set(v___x_999_, 2, v_v_734_);
lean_ctor_set(v___x_999_, 1, v_k_733_);
lean_ctor_set(v___x_999_, 0, v___x_882_);
v___x_1003_ = v___x_999_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_k_733_);
lean_ctor_set(v_reuseFailAlloc_1007_, 2, v_v_734_);
lean_ctor_set(v_reuseFailAlloc_1007_, 3, v_l_966_);
lean_ctor_set(v_reuseFailAlloc_1007_, 4, v_l_966_);
v___x_1003_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
lean_object* v___x_1005_; 
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 4, v_r_995_);
lean_ctor_set(v___x_738_, 3, v___x_1003_);
lean_ctor_set(v___x_738_, 2, v_v_997_);
lean_ctor_set(v___x_738_, 1, v_k_996_);
lean_ctor_set(v___x_738_, 0, v___x_1001_);
v___x_1005_ = v___x_738_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v_k_996_);
lean_ctor_set(v_reuseFailAlloc_1006_, 2, v_v_997_);
lean_ctor_set(v_reuseFailAlloc_1006_, 3, v___x_1003_);
lean_ctor_set(v_reuseFailAlloc_1006_, 4, v_r_995_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
else
{
lean_object* v___x_1012_; lean_object* v___x_1014_; 
v___x_1012_ = lean_unsigned_to_nat(2u);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 4, v_impl_881_);
lean_ctor_set(v___x_738_, 3, v_r_995_);
lean_ctor_set(v___x_738_, 0, v___x_1012_);
v___x_1014_ = v___x_738_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1012_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v_k_733_);
lean_ctor_set(v_reuseFailAlloc_1015_, 2, v_v_734_);
lean_ctor_set(v_reuseFailAlloc_1015_, 3, v_r_995_);
lean_ctor_set(v_reuseFailAlloc_1015_, 4, v_impl_881_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
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
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = lean_unsigned_to_nat(1u);
v___x_1018_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
lean_ctor_set(v___x_1018_, 1, v_k_729_);
lean_ctor_set(v___x_1018_, 2, v_v_730_);
lean_ctor_set(v___x_1018_, 3, v_t_731_);
lean_ctor_set(v___x_1018_, 4, v_t_731_);
return v___x_1018_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_LeanOptions_fromOptions_x3f_spec__1(lean_object* v_init_1019_, lean_object* v_x_1020_){
_start:
{
if (lean_obj_tag(v_x_1020_) == 0)
{
lean_object* v_k_1021_; lean_object* v_v_1022_; lean_object* v_l_1023_; lean_object* v_r_1024_; lean_object* v___x_1025_; 
v_k_1021_ = lean_ctor_get(v_x_1020_, 1);
lean_inc(v_k_1021_);
v_v_1022_ = lean_ctor_get(v_x_1020_, 2);
lean_inc(v_v_1022_);
v_l_1023_ = lean_ctor_get(v_x_1020_, 3);
lean_inc(v_l_1023_);
v_r_1024_ = lean_ctor_get(v_x_1020_, 4);
lean_inc(v_r_1024_);
lean_dec_ref(v_x_1020_);
v___x_1025_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_LeanOptions_fromOptions_x3f_spec__1(v_init_1019_, v_l_1023_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_dec(v_r_1024_);
lean_dec(v_v_1022_);
lean_dec(v_k_1021_);
return v___x_1025_;
}
else
{
lean_object* v_val_1026_; lean_object* v_a_1027_; lean_object* v___x_1028_; 
v_val_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_val_1026_);
lean_dec_ref(v___x_1025_);
v_a_1027_ = lean_ctor_get(v_val_1026_, 0);
lean_inc(v_a_1027_);
lean_dec(v_val_1026_);
v___x_1028_ = l_Lean_LeanOptionValue_ofDataValue_x3f(v_v_1022_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v___x_1029_; 
lean_dec(v_a_1027_);
lean_dec(v_r_1024_);
lean_dec(v_k_1021_);
v___x_1029_ = lean_box(0);
return v___x_1029_;
}
else
{
lean_object* v_val_1030_; lean_object* v___x_1031_; 
v_val_1030_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_val_1030_);
lean_dec_ref(v___x_1028_);
v___x_1031_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_LeanOptions_fromOptions_x3f_spec__0___redArg(v_k_1021_, v_val_1030_, v_a_1027_);
v_init_1019_ = v___x_1031_;
v_x_1020_ = v_r_1024_;
goto _start;
}
}
}
else
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1033_, 0, v_init_1019_);
v___x_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
return v___x_1034_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptions_fromOptions_x3f(lean_object* v_options_1035_){
_start:
{
lean_object* v_map_1036_; lean_object* v_values_1037_; lean_object* v___x_1038_; 
v_map_1036_ = lean_ctor_get(v_options_1035_, 0);
lean_inc(v_map_1036_);
lean_dec_ref(v_options_1035_);
v_values_1037_ = lean_box(1);
v___x_1038_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_LeanOptions_fromOptions_x3f_spec__1(v_values_1037_, v_map_1036_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v___x_1039_; 
v___x_1039_ = lean_box(0);
return v___x_1039_;
}
else
{
lean_object* v_val_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1048_; 
v_val_1040_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1042_ = v___x_1038_;
v_isShared_1043_ = v_isSharedCheck_1048_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_val_1040_);
lean_dec(v___x_1038_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1048_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v_a_1044_; lean_object* v___x_1046_; 
v_a_1044_ = lean_ctor_get(v_val_1040_, 0);
lean_inc(v_a_1044_);
lean_dec(v_val_1040_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v_a_1044_);
v___x_1046_ = v___x_1042_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1044_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_LeanOptions_fromOptions_x3f_spec__0(lean_object* v_00_u03b2_1049_, lean_object* v_k_1050_, lean_object* v_v_1051_, lean_object* v_t_1052_, lean_object* v_hl_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_LeanOptions_fromOptions_x3f_spec__0___redArg(v_k_1050_, v_v_1051_, v_t_1052_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonLeanOptions___lam__0(lean_object* v___f_1055_, lean_object* v_j_1056_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Lean_NameMap_fromJson_x3f___redArg(v___f_1055_, v_j_1056_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_1057_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1057_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
v_a_1066_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1057_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1057_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
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
}
LEAN_EXPORT lean_object* l_Lean_instToJsonLeanOptions___lam__0(lean_object* v___f_1077_, lean_object* v_options_1078_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_NameMap_toJson___redArg(v___f_1077_, v_options_1078_);
return v___x_1079_;
}
}
lean_object* runtime_initialize_Lean_Data_Json_FromToJson_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_LeanOptions(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

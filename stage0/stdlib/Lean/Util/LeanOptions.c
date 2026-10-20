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
size_t v___x_620_; size_t v___x_621_; lean_object* v___x_622_; 
v___x_620_ = ((size_t)0ULL);
v___x_621_ = lean_usize_of_nat(v___x_618_);
v___x_622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LeanOptions_ofArray_spec__0(v_opts_615_, v___x_620_, v___x_621_, v___x_616_);
return v___x_622_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptions_ofArray___boxed(lean_object* v_opts_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lean_LeanOptions_ofArray(v_opts_623_);
lean_dec_ref(v_opts_623_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LeanOptions_append_spec__0___redArg(lean_object* v_b_u2082_625_, lean_object* v_k_626_, lean_object* v_t_627_){
_start:
{
if (lean_obj_tag(v_t_627_) == 0)
{
lean_object* v_size_628_; lean_object* v_k_629_; lean_object* v_v_630_; lean_object* v_l_631_; lean_object* v_r_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_644_; 
v_size_628_ = lean_ctor_get(v_t_627_, 0);
v_k_629_ = lean_ctor_get(v_t_627_, 1);
v_v_630_ = lean_ctor_get(v_t_627_, 2);
v_l_631_ = lean_ctor_get(v_t_627_, 3);
v_r_632_ = lean_ctor_get(v_t_627_, 4);
v_isSharedCheck_644_ = !lean_is_exclusive(v_t_627_);
if (v_isSharedCheck_644_ == 0)
{
v___x_634_ = v_t_627_;
v_isShared_635_ = v_isSharedCheck_644_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_r_632_);
lean_inc(v_l_631_);
lean_inc(v_v_630_);
lean_inc(v_k_629_);
lean_inc(v_size_628_);
lean_dec(v_t_627_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_644_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
uint8_t v___x_636_; 
v___x_636_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_626_, v_k_629_);
switch(v___x_636_)
{
case 0:
{
lean_object* v_impl_637_; lean_object* v___x_638_; 
lean_del_object(v___x_634_);
lean_dec(v_size_628_);
v_impl_637_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LeanOptions_append_spec__0___redArg(v_b_u2082_625_, v_k_626_, v_l_631_);
v___x_638_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_629_, v_v_630_, v_impl_637_, v_r_632_);
return v___x_638_;
}
case 1:
{
lean_object* v___x_640_; 
lean_dec(v_v_630_);
lean_dec(v_k_629_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 2, v_b_u2082_625_);
lean_ctor_set(v___x_634_, 1, v_k_626_);
v___x_640_ = v___x_634_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_size_628_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v_k_626_);
lean_ctor_set(v_reuseFailAlloc_641_, 2, v_b_u2082_625_);
lean_ctor_set(v_reuseFailAlloc_641_, 3, v_l_631_);
lean_ctor_set(v_reuseFailAlloc_641_, 4, v_r_632_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
default: 
{
lean_object* v_impl_642_; lean_object* v___x_643_; 
lean_del_object(v___x_634_);
lean_dec(v_size_628_);
v_impl_642_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LeanOptions_append_spec__0___redArg(v_b_u2082_625_, v_k_626_, v_r_632_);
v___x_643_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_629_, v_v_630_, v_l_631_, v_impl_642_);
return v___x_643_;
}
}
}
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_unsigned_to_nat(1u);
v___x_646_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
lean_ctor_set(v___x_646_, 1, v_k_626_);
lean_ctor_set(v___x_646_, 2, v_b_u2082_625_);
lean_ctor_set(v___x_646_, 3, v_t_627_);
lean_ctor_set(v___x_646_, 4, v_t_627_);
return v___x_646_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LeanOptions_append_spec__1_spec__1(lean_object* v_init_647_, lean_object* v_x_648_){
_start:
{
if (lean_obj_tag(v_x_648_) == 0)
{
lean_object* v_k_649_; lean_object* v_v_650_; lean_object* v_l_651_; lean_object* v_r_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v_k_649_ = lean_ctor_get(v_x_648_, 1);
lean_inc(v_k_649_);
v_v_650_ = lean_ctor_get(v_x_648_, 2);
lean_inc(v_v_650_);
v_l_651_ = lean_ctor_get(v_x_648_, 3);
lean_inc(v_l_651_);
v_r_652_ = lean_ctor_get(v_x_648_, 4);
lean_inc(v_r_652_);
lean_dec_ref_known(v_x_648_, 5);
v___x_653_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LeanOptions_append_spec__1_spec__1(v_init_647_, v_l_651_);
v___x_654_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LeanOptions_append_spec__0___redArg(v_v_650_, v_k_649_, v___x_653_);
v_init_647_ = v___x_654_;
v_x_648_ = v_r_652_;
goto _start;
}
else
{
return v_init_647_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptions_append(lean_object* v_self_656_, lean_object* v_new_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LeanOptions_append_spec__1_spec__1(v_self_656_, v_new_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LeanOptions_append_spec__0(lean_object* v_b_u2082_659_, lean_object* v_k_660_, lean_object* v_t_661_, lean_object* v_hl_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LeanOptions_append_spec__0___redArg(v_b_u2082_659_, v_k_660_, v_t_661_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LeanOptions_append_spec__1(lean_object* v_init_664_, lean_object* v_t_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LeanOptions_append_spec__1_spec__1(v_init_664_, v_t_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptions_appendArray(lean_object* v_self_669_, lean_object* v_new_670_){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_671_ = lean_unsigned_to_nat(0u);
v___x_672_ = lean_array_get_size(v_new_670_);
v___x_673_ = lean_nat_dec_lt(v___x_671_, v___x_672_);
if (v___x_673_ == 0)
{
return v_self_669_;
}
else
{
size_t v___x_674_; size_t v___x_675_; lean_object* v___x_676_; 
v___x_674_ = ((size_t)0ULL);
v___x_675_ = lean_usize_of_nat(v___x_672_);
v___x_676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LeanOptions_ofArray_spec__0(v_new_670_, v___x_674_, v___x_675_, v_self_669_);
return v___x_676_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptions_appendArray___boxed(lean_object* v_self_677_, lean_object* v_new_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_LeanOptions_appendArray(v_self_677_, v_new_678_);
lean_dec_ref(v_new_678_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0(lean_object* v_o_685_, lean_object* v_k_686_, lean_object* v_v_687_){
_start:
{
lean_object* v_map_688_; uint8_t v_hasTrace_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_702_; 
v_map_688_ = lean_ctor_get(v_o_685_, 0);
v_hasTrace_689_ = lean_ctor_get_uint8(v_o_685_, sizeof(void*)*1);
v_isSharedCheck_702_ = !lean_is_exclusive(v_o_685_);
if (v_isSharedCheck_702_ == 0)
{
v___x_691_ = v_o_685_;
v_isShared_692_ = v_isSharedCheck_702_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_map_688_);
lean_dec(v_o_685_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_702_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; 
lean_inc(v_k_686_);
v___x_693_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_686_, v_v_687_, v_map_688_);
if (v_hasTrace_689_ == 0)
{
lean_object* v___x_694_; uint8_t v___x_695_; lean_object* v___x_697_; 
v___x_694_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0___closed__1));
v___x_695_ = l_Lean_Name_isPrefixOf(v___x_694_, v_k_686_);
lean_dec(v_k_686_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_693_);
v___x_697_ = v___x_691_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_693_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_ctor_set_uint8(v___x_697_, sizeof(void*)*1, v___x_695_);
return v___x_697_;
}
}
else
{
lean_object* v___x_700_; 
lean_dec(v_k_686_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_693_);
v___x_700_ = v___x_691_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_693_);
lean_ctor_set_uint8(v_reuseFailAlloc_701_, sizeof(void*)*1, v_hasTrace_689_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_LeanOptions_toOptions_spec__1(lean_object* v_init_703_, lean_object* v_x_704_){
_start:
{
if (lean_obj_tag(v_x_704_) == 0)
{
lean_object* v_k_705_; lean_object* v_v_706_; lean_object* v_l_707_; lean_object* v_r_708_; lean_object* v___x_709_; lean_object* v_a_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v_k_705_ = lean_ctor_get(v_x_704_, 1);
lean_inc(v_k_705_);
v_v_706_ = lean_ctor_get(v_x_704_, 2);
lean_inc(v_v_706_);
v_l_707_ = lean_ctor_get(v_x_704_, 3);
lean_inc(v_l_707_);
v_r_708_ = lean_ctor_get(v_x_704_, 4);
lean_inc(v_r_708_);
lean_dec_ref_known(v_x_704_, 5);
v___x_709_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_LeanOptions_toOptions_spec__1(v_init_703_, v_l_707_);
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref(v___x_709_);
v___x_711_ = l_Lean_LeanOptionValue_toDataValue(v_v_706_);
v___x_712_ = l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0(v_a_710_, v_k_705_, v___x_711_);
v_init_703_ = v___x_712_;
v_x_704_ = v_r_708_;
goto _start;
}
else
{
lean_object* v___x_714_; 
v___x_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_714_, 0, v_init_703_);
return v___x_714_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptions_toOptions(lean_object* v_leanOptions_715_){
_start:
{
lean_object* v_options_716_; lean_object* v___x_717_; lean_object* v_a_718_; 
v_options_716_ = l_Lean_Options_empty;
v___x_717_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_LeanOptions_toOptions_spec__1(v_options_716_, v_leanOptions_715_);
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
lean_dec_ref(v___x_717_);
return v_a_718_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_LeanOptions_fromOptions_x3f_spec__0___redArg(lean_object* v_k_719_, lean_object* v_v_720_, lean_object* v_t_721_){
_start:
{
if (lean_obj_tag(v_t_721_) == 0)
{
lean_object* v_size_722_; lean_object* v_k_723_; lean_object* v_v_724_; lean_object* v_l_725_; lean_object* v_r_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_1006_; 
v_size_722_ = lean_ctor_get(v_t_721_, 0);
v_k_723_ = lean_ctor_get(v_t_721_, 1);
v_v_724_ = lean_ctor_get(v_t_721_, 2);
v_l_725_ = lean_ctor_get(v_t_721_, 3);
v_r_726_ = lean_ctor_get(v_t_721_, 4);
v_isSharedCheck_1006_ = !lean_is_exclusive(v_t_721_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_728_ = v_t_721_;
v_isShared_729_ = v_isSharedCheck_1006_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_r_726_);
lean_inc(v_l_725_);
lean_inc(v_v_724_);
lean_inc(v_k_723_);
lean_inc(v_size_722_);
lean_dec(v_t_721_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_1006_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
uint8_t v___x_730_; 
v___x_730_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_719_, v_k_723_);
switch(v___x_730_)
{
case 0:
{
lean_object* v_impl_731_; lean_object* v___x_732_; 
lean_dec(v_size_722_);
v_impl_731_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_LeanOptions_fromOptions_x3f_spec__0___redArg(v_k_719_, v_v_720_, v_l_725_);
v___x_732_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_726_) == 0)
{
lean_object* v_size_733_; lean_object* v_size_734_; lean_object* v_k_735_; lean_object* v_v_736_; lean_object* v_l_737_; lean_object* v_r_738_; lean_object* v___x_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
v_size_733_ = lean_ctor_get(v_r_726_, 0);
v_size_734_ = lean_ctor_get(v_impl_731_, 0);
v_k_735_ = lean_ctor_get(v_impl_731_, 1);
v_v_736_ = lean_ctor_get(v_impl_731_, 2);
v_l_737_ = lean_ctor_get(v_impl_731_, 3);
v_r_738_ = lean_ctor_get(v_impl_731_, 4);
lean_inc(v_r_738_);
v___x_739_ = lean_unsigned_to_nat(3u);
v___x_740_ = lean_nat_mul(v___x_739_, v_size_733_);
v___x_741_ = lean_nat_dec_lt(v___x_740_, v_size_734_);
lean_dec(v___x_740_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_745_; 
lean_dec(v_r_738_);
v___x_742_ = lean_nat_add(v___x_732_, v_size_734_);
v___x_743_ = lean_nat_add(v___x_742_, v_size_733_);
lean_dec(v___x_742_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 3, v_impl_731_);
lean_ctor_set(v___x_728_, 0, v___x_743_);
v___x_745_ = v___x_728_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_743_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_k_723_);
lean_ctor_set(v_reuseFailAlloc_746_, 2, v_v_724_);
lean_ctor_set(v_reuseFailAlloc_746_, 3, v_impl_731_);
lean_ctor_set(v_reuseFailAlloc_746_, 4, v_r_726_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
else
{
lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_812_; 
lean_inc(v_l_737_);
lean_inc(v_v_736_);
lean_inc(v_k_735_);
lean_inc(v_size_734_);
v_isSharedCheck_812_ = !lean_is_exclusive(v_impl_731_);
if (v_isSharedCheck_812_ == 0)
{
lean_object* v_unused_813_; lean_object* v_unused_814_; lean_object* v_unused_815_; lean_object* v_unused_816_; lean_object* v_unused_817_; 
v_unused_813_ = lean_ctor_get(v_impl_731_, 4);
lean_dec(v_unused_813_);
v_unused_814_ = lean_ctor_get(v_impl_731_, 3);
lean_dec(v_unused_814_);
v_unused_815_ = lean_ctor_get(v_impl_731_, 2);
lean_dec(v_unused_815_);
v_unused_816_ = lean_ctor_get(v_impl_731_, 1);
lean_dec(v_unused_816_);
v_unused_817_ = lean_ctor_get(v_impl_731_, 0);
lean_dec(v_unused_817_);
v___x_748_ = v_impl_731_;
v_isShared_749_ = v_isSharedCheck_812_;
goto v_resetjp_747_;
}
else
{
lean_dec(v_impl_731_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_812_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v_size_750_; lean_object* v_size_751_; lean_object* v_k_752_; lean_object* v_v_753_; lean_object* v_l_754_; lean_object* v_r_755_; lean_object* v___x_756_; lean_object* v___x_757_; uint8_t v___x_758_; 
v_size_750_ = lean_ctor_get(v_l_737_, 0);
v_size_751_ = lean_ctor_get(v_r_738_, 0);
v_k_752_ = lean_ctor_get(v_r_738_, 1);
v_v_753_ = lean_ctor_get(v_r_738_, 2);
v_l_754_ = lean_ctor_get(v_r_738_, 3);
v_r_755_ = lean_ctor_get(v_r_738_, 4);
v___x_756_ = lean_unsigned_to_nat(2u);
v___x_757_ = lean_nat_mul(v___x_756_, v_size_750_);
v___x_758_ = lean_nat_dec_lt(v_size_751_, v___x_757_);
lean_dec(v___x_757_);
if (v___x_758_ == 0)
{
lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_787_; 
lean_inc(v_r_755_);
lean_inc(v_l_754_);
lean_inc(v_v_753_);
lean_inc(v_k_752_);
v_isSharedCheck_787_ = !lean_is_exclusive(v_r_738_);
if (v_isSharedCheck_787_ == 0)
{
lean_object* v_unused_788_; lean_object* v_unused_789_; lean_object* v_unused_790_; lean_object* v_unused_791_; lean_object* v_unused_792_; 
v_unused_788_ = lean_ctor_get(v_r_738_, 4);
lean_dec(v_unused_788_);
v_unused_789_ = lean_ctor_get(v_r_738_, 3);
lean_dec(v_unused_789_);
v_unused_790_ = lean_ctor_get(v_r_738_, 2);
lean_dec(v_unused_790_);
v_unused_791_ = lean_ctor_get(v_r_738_, 1);
lean_dec(v_unused_791_);
v_unused_792_ = lean_ctor_get(v_r_738_, 0);
lean_dec(v_unused_792_);
v___x_760_ = v_r_738_;
v_isShared_761_ = v_isSharedCheck_787_;
goto v_resetjp_759_;
}
else
{
lean_dec(v_r_738_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_787_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___x_775_; lean_object* v___y_777_; 
v___x_762_ = lean_nat_add(v___x_732_, v_size_734_);
lean_dec(v_size_734_);
v___x_763_ = lean_nat_add(v___x_762_, v_size_733_);
lean_dec(v___x_762_);
v___x_775_ = lean_nat_add(v___x_732_, v_size_750_);
if (lean_obj_tag(v_l_754_) == 0)
{
lean_object* v_size_785_; 
v_size_785_ = lean_ctor_get(v_l_754_, 0);
lean_inc(v_size_785_);
v___y_777_ = v_size_785_;
goto v___jp_776_;
}
else
{
lean_object* v___x_786_; 
v___x_786_ = lean_unsigned_to_nat(0u);
v___y_777_ = v___x_786_;
goto v___jp_776_;
}
v___jp_764_:
{
lean_object* v___x_768_; lean_object* v___x_770_; 
v___x_768_ = lean_nat_add(v___y_765_, v___y_767_);
lean_dec(v___y_767_);
lean_dec(v___y_765_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 4, v_r_726_);
lean_ctor_set(v___x_760_, 3, v_r_755_);
lean_ctor_set(v___x_760_, 2, v_v_724_);
lean_ctor_set(v___x_760_, 1, v_k_723_);
lean_ctor_set(v___x_760_, 0, v___x_768_);
v___x_770_ = v___x_760_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_768_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_k_723_);
lean_ctor_set(v_reuseFailAlloc_774_, 2, v_v_724_);
lean_ctor_set(v_reuseFailAlloc_774_, 3, v_r_755_);
lean_ctor_set(v_reuseFailAlloc_774_, 4, v_r_726_);
v___x_770_ = v_reuseFailAlloc_774_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
lean_object* v___x_772_; 
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 4, v___x_770_);
lean_ctor_set(v___x_748_, 3, v___y_766_);
lean_ctor_set(v___x_748_, 2, v_v_753_);
lean_ctor_set(v___x_748_, 1, v_k_752_);
lean_ctor_set(v___x_748_, 0, v___x_763_);
v___x_772_ = v___x_748_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_763_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_k_752_);
lean_ctor_set(v_reuseFailAlloc_773_, 2, v_v_753_);
lean_ctor_set(v_reuseFailAlloc_773_, 3, v___y_766_);
lean_ctor_set(v_reuseFailAlloc_773_, 4, v___x_770_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
v___jp_776_:
{
lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_778_ = lean_nat_add(v___x_775_, v___y_777_);
lean_dec(v___y_777_);
lean_dec(v___x_775_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 4, v_l_754_);
lean_ctor_set(v___x_728_, 3, v_l_737_);
lean_ctor_set(v___x_728_, 2, v_v_736_);
lean_ctor_set(v___x_728_, 1, v_k_735_);
lean_ctor_set(v___x_728_, 0, v___x_778_);
v___x_780_ = v___x_728_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_778_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_k_735_);
lean_ctor_set(v_reuseFailAlloc_784_, 2, v_v_736_);
lean_ctor_set(v_reuseFailAlloc_784_, 3, v_l_737_);
lean_ctor_set(v_reuseFailAlloc_784_, 4, v_l_754_);
v___x_780_ = v_reuseFailAlloc_784_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_781_; 
v___x_781_ = lean_nat_add(v___x_732_, v_size_733_);
if (lean_obj_tag(v_r_755_) == 0)
{
lean_object* v_size_782_; 
v_size_782_ = lean_ctor_get(v_r_755_, 0);
lean_inc(v_size_782_);
v___y_765_ = v___x_781_;
v___y_766_ = v___x_780_;
v___y_767_ = v_size_782_;
goto v___jp_764_;
}
else
{
lean_object* v___x_783_; 
v___x_783_ = lean_unsigned_to_nat(0u);
v___y_765_ = v___x_781_;
v___y_766_ = v___x_780_;
v___y_767_ = v___x_783_;
goto v___jp_764_;
}
}
}
}
}
else
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_798_; 
lean_del_object(v___x_728_);
v___x_793_ = lean_nat_add(v___x_732_, v_size_734_);
lean_dec(v_size_734_);
v___x_794_ = lean_nat_add(v___x_793_, v_size_733_);
lean_dec(v___x_793_);
v___x_795_ = lean_nat_add(v___x_732_, v_size_733_);
v___x_796_ = lean_nat_add(v___x_795_, v_size_751_);
lean_dec(v___x_795_);
lean_inc_ref(v_r_726_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 4, v_r_726_);
lean_ctor_set(v___x_748_, 3, v_r_738_);
lean_ctor_set(v___x_748_, 2, v_v_724_);
lean_ctor_set(v___x_748_, 1, v_k_723_);
lean_ctor_set(v___x_748_, 0, v___x_796_);
v___x_798_ = v___x_748_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_k_723_);
lean_ctor_set(v_reuseFailAlloc_811_, 2, v_v_724_);
lean_ctor_set(v_reuseFailAlloc_811_, 3, v_r_738_);
lean_ctor_set(v_reuseFailAlloc_811_, 4, v_r_726_);
v___x_798_ = v_reuseFailAlloc_811_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
v_isSharedCheck_805_ = !lean_is_exclusive(v_r_726_);
if (v_isSharedCheck_805_ == 0)
{
lean_object* v_unused_806_; lean_object* v_unused_807_; lean_object* v_unused_808_; lean_object* v_unused_809_; lean_object* v_unused_810_; 
v_unused_806_ = lean_ctor_get(v_r_726_, 4);
lean_dec(v_unused_806_);
v_unused_807_ = lean_ctor_get(v_r_726_, 3);
lean_dec(v_unused_807_);
v_unused_808_ = lean_ctor_get(v_r_726_, 2);
lean_dec(v_unused_808_);
v_unused_809_ = lean_ctor_get(v_r_726_, 1);
lean_dec(v_unused_809_);
v_unused_810_ = lean_ctor_get(v_r_726_, 0);
lean_dec(v_unused_810_);
v___x_800_ = v_r_726_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_dec(v_r_726_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 4, v___x_798_);
lean_ctor_set(v___x_800_, 3, v_l_737_);
lean_ctor_set(v___x_800_, 2, v_v_736_);
lean_ctor_set(v___x_800_, 1, v_k_735_);
lean_ctor_set(v___x_800_, 0, v___x_794_);
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_794_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_k_735_);
lean_ctor_set(v_reuseFailAlloc_804_, 2, v_v_736_);
lean_ctor_set(v_reuseFailAlloc_804_, 3, v_l_737_);
lean_ctor_set(v_reuseFailAlloc_804_, 4, v___x_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_818_; 
v_l_818_ = lean_ctor_get(v_impl_731_, 3);
if (lean_obj_tag(v_l_818_) == 0)
{
lean_object* v_r_819_; lean_object* v_k_820_; lean_object* v_v_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_832_; 
lean_inc_ref(v_l_818_);
v_r_819_ = lean_ctor_get(v_impl_731_, 4);
v_k_820_ = lean_ctor_get(v_impl_731_, 1);
v_v_821_ = lean_ctor_get(v_impl_731_, 2);
v_isSharedCheck_832_ = !lean_is_exclusive(v_impl_731_);
if (v_isSharedCheck_832_ == 0)
{
lean_object* v_unused_833_; lean_object* v_unused_834_; 
v_unused_833_ = lean_ctor_get(v_impl_731_, 3);
lean_dec(v_unused_833_);
v_unused_834_ = lean_ctor_get(v_impl_731_, 0);
lean_dec(v_unused_834_);
v___x_823_ = v_impl_731_;
v_isShared_824_ = v_isSharedCheck_832_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_r_819_);
lean_inc(v_v_821_);
lean_inc(v_k_820_);
lean_dec(v_impl_731_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_832_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_825_; lean_object* v___x_827_; 
v___x_825_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_819_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 3, v_r_819_);
lean_ctor_set(v___x_823_, 2, v_v_724_);
lean_ctor_set(v___x_823_, 1, v_k_723_);
lean_ctor_set(v___x_823_, 0, v___x_732_);
v___x_827_ = v___x_823_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_732_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v_k_723_);
lean_ctor_set(v_reuseFailAlloc_831_, 2, v_v_724_);
lean_ctor_set(v_reuseFailAlloc_831_, 3, v_r_819_);
lean_ctor_set(v_reuseFailAlloc_831_, 4, v_r_819_);
v___x_827_ = v_reuseFailAlloc_831_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v___x_829_; 
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 4, v___x_827_);
lean_ctor_set(v___x_728_, 3, v_l_818_);
lean_ctor_set(v___x_728_, 2, v_v_821_);
lean_ctor_set(v___x_728_, 1, v_k_820_);
lean_ctor_set(v___x_728_, 0, v___x_825_);
v___x_829_ = v___x_728_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_825_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v_k_820_);
lean_ctor_set(v_reuseFailAlloc_830_, 2, v_v_821_);
lean_ctor_set(v_reuseFailAlloc_830_, 3, v_l_818_);
lean_ctor_set(v_reuseFailAlloc_830_, 4, v___x_827_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
else
{
lean_object* v_r_835_; 
v_r_835_ = lean_ctor_get(v_impl_731_, 4);
lean_inc(v_r_835_);
if (lean_obj_tag(v_r_835_) == 0)
{
lean_object* v_k_836_; lean_object* v_v_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_860_; 
lean_inc(v_l_818_);
v_k_836_ = lean_ctor_get(v_impl_731_, 1);
v_v_837_ = lean_ctor_get(v_impl_731_, 2);
v_isSharedCheck_860_ = !lean_is_exclusive(v_impl_731_);
if (v_isSharedCheck_860_ == 0)
{
lean_object* v_unused_861_; lean_object* v_unused_862_; lean_object* v_unused_863_; 
v_unused_861_ = lean_ctor_get(v_impl_731_, 4);
lean_dec(v_unused_861_);
v_unused_862_ = lean_ctor_get(v_impl_731_, 3);
lean_dec(v_unused_862_);
v_unused_863_ = lean_ctor_get(v_impl_731_, 0);
lean_dec(v_unused_863_);
v___x_839_ = v_impl_731_;
v_isShared_840_ = v_isSharedCheck_860_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_v_837_);
lean_inc(v_k_836_);
lean_dec(v_impl_731_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_860_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v_k_841_; lean_object* v_v_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_856_; 
v_k_841_ = lean_ctor_get(v_r_835_, 1);
v_v_842_ = lean_ctor_get(v_r_835_, 2);
v_isSharedCheck_856_ = !lean_is_exclusive(v_r_835_);
if (v_isSharedCheck_856_ == 0)
{
lean_object* v_unused_857_; lean_object* v_unused_858_; lean_object* v_unused_859_; 
v_unused_857_ = lean_ctor_get(v_r_835_, 4);
lean_dec(v_unused_857_);
v_unused_858_ = lean_ctor_get(v_r_835_, 3);
lean_dec(v_unused_858_);
v_unused_859_ = lean_ctor_get(v_r_835_, 0);
lean_dec(v_unused_859_);
v___x_844_ = v_r_835_;
v_isShared_845_ = v_isSharedCheck_856_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_v_842_);
lean_inc(v_k_841_);
lean_dec(v_r_835_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_856_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v___x_848_; 
v___x_846_ = lean_unsigned_to_nat(3u);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 4, v_l_818_);
lean_ctor_set(v___x_844_, 3, v_l_818_);
lean_ctor_set(v___x_844_, 2, v_v_837_);
lean_ctor_set(v___x_844_, 1, v_k_836_);
lean_ctor_set(v___x_844_, 0, v___x_732_);
v___x_848_ = v___x_844_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_732_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_k_836_);
lean_ctor_set(v_reuseFailAlloc_855_, 2, v_v_837_);
lean_ctor_set(v_reuseFailAlloc_855_, 3, v_l_818_);
lean_ctor_set(v_reuseFailAlloc_855_, 4, v_l_818_);
v___x_848_ = v_reuseFailAlloc_855_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
lean_object* v___x_850_; 
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 4, v_l_818_);
lean_ctor_set(v___x_839_, 2, v_v_724_);
lean_ctor_set(v___x_839_, 1, v_k_723_);
lean_ctor_set(v___x_839_, 0, v___x_732_);
v___x_850_ = v___x_839_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_732_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v_k_723_);
lean_ctor_set(v_reuseFailAlloc_854_, 2, v_v_724_);
lean_ctor_set(v_reuseFailAlloc_854_, 3, v_l_818_);
lean_ctor_set(v_reuseFailAlloc_854_, 4, v_l_818_);
v___x_850_ = v_reuseFailAlloc_854_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
lean_object* v___x_852_; 
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 4, v___x_850_);
lean_ctor_set(v___x_728_, 3, v___x_848_);
lean_ctor_set(v___x_728_, 2, v_v_842_);
lean_ctor_set(v___x_728_, 1, v_k_841_);
lean_ctor_set(v___x_728_, 0, v___x_846_);
v___x_852_ = v___x_728_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_846_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v_k_841_);
lean_ctor_set(v_reuseFailAlloc_853_, 2, v_v_842_);
lean_ctor_set(v_reuseFailAlloc_853_, 3, v___x_848_);
lean_ctor_set(v_reuseFailAlloc_853_, 4, v___x_850_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
}
}
else
{
lean_object* v___x_864_; lean_object* v___x_866_; 
v___x_864_ = lean_unsigned_to_nat(2u);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 4, v_r_835_);
lean_ctor_set(v___x_728_, 3, v_impl_731_);
lean_ctor_set(v___x_728_, 0, v___x_864_);
v___x_866_ = v___x_728_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_864_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v_k_723_);
lean_ctor_set(v_reuseFailAlloc_867_, 2, v_v_724_);
lean_ctor_set(v_reuseFailAlloc_867_, 3, v_impl_731_);
lean_ctor_set(v_reuseFailAlloc_867_, 4, v_r_835_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
case 1:
{
lean_object* v___x_869_; 
lean_dec(v_v_724_);
lean_dec(v_k_723_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 2, v_v_720_);
lean_ctor_set(v___x_728_, 1, v_k_719_);
v___x_869_ = v___x_728_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_size_722_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_k_719_);
lean_ctor_set(v_reuseFailAlloc_870_, 2, v_v_720_);
lean_ctor_set(v_reuseFailAlloc_870_, 3, v_l_725_);
lean_ctor_set(v_reuseFailAlloc_870_, 4, v_r_726_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
default: 
{
lean_object* v_impl_871_; lean_object* v___x_872_; 
lean_dec(v_size_722_);
v_impl_871_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_LeanOptions_fromOptions_x3f_spec__0___redArg(v_k_719_, v_v_720_, v_r_726_);
v___x_872_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_725_) == 0)
{
lean_object* v_size_873_; lean_object* v_size_874_; lean_object* v_k_875_; lean_object* v_v_876_; lean_object* v_l_877_; lean_object* v_r_878_; lean_object* v___x_879_; lean_object* v___x_880_; uint8_t v___x_881_; 
v_size_873_ = lean_ctor_get(v_l_725_, 0);
v_size_874_ = lean_ctor_get(v_impl_871_, 0);
v_k_875_ = lean_ctor_get(v_impl_871_, 1);
v_v_876_ = lean_ctor_get(v_impl_871_, 2);
v_l_877_ = lean_ctor_get(v_impl_871_, 3);
lean_inc(v_l_877_);
v_r_878_ = lean_ctor_get(v_impl_871_, 4);
v___x_879_ = lean_unsigned_to_nat(3u);
v___x_880_ = lean_nat_mul(v___x_879_, v_size_873_);
v___x_881_ = lean_nat_dec_lt(v___x_880_, v_size_874_);
lean_dec(v___x_880_);
if (v___x_881_ == 0)
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_885_; 
lean_dec(v_l_877_);
v___x_882_ = lean_nat_add(v___x_872_, v_size_873_);
v___x_883_ = lean_nat_add(v___x_882_, v_size_874_);
lean_dec(v___x_882_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 4, v_impl_871_);
lean_ctor_set(v___x_728_, 0, v___x_883_);
v___x_885_ = v___x_728_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v_k_723_);
lean_ctor_set(v_reuseFailAlloc_886_, 2, v_v_724_);
lean_ctor_set(v_reuseFailAlloc_886_, 3, v_l_725_);
lean_ctor_set(v_reuseFailAlloc_886_, 4, v_impl_871_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
else
{
lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_950_; 
lean_inc(v_r_878_);
lean_inc(v_v_876_);
lean_inc(v_k_875_);
lean_inc(v_size_874_);
v_isSharedCheck_950_ = !lean_is_exclusive(v_impl_871_);
if (v_isSharedCheck_950_ == 0)
{
lean_object* v_unused_951_; lean_object* v_unused_952_; lean_object* v_unused_953_; lean_object* v_unused_954_; lean_object* v_unused_955_; 
v_unused_951_ = lean_ctor_get(v_impl_871_, 4);
lean_dec(v_unused_951_);
v_unused_952_ = lean_ctor_get(v_impl_871_, 3);
lean_dec(v_unused_952_);
v_unused_953_ = lean_ctor_get(v_impl_871_, 2);
lean_dec(v_unused_953_);
v_unused_954_ = lean_ctor_get(v_impl_871_, 1);
lean_dec(v_unused_954_);
v_unused_955_ = lean_ctor_get(v_impl_871_, 0);
lean_dec(v_unused_955_);
v___x_888_ = v_impl_871_;
v_isShared_889_ = v_isSharedCheck_950_;
goto v_resetjp_887_;
}
else
{
lean_dec(v_impl_871_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_950_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v_size_890_; lean_object* v_k_891_; lean_object* v_v_892_; lean_object* v_l_893_; lean_object* v_r_894_; lean_object* v_size_895_; lean_object* v___x_896_; lean_object* v___x_897_; uint8_t v___x_898_; 
v_size_890_ = lean_ctor_get(v_l_877_, 0);
v_k_891_ = lean_ctor_get(v_l_877_, 1);
v_v_892_ = lean_ctor_get(v_l_877_, 2);
v_l_893_ = lean_ctor_get(v_l_877_, 3);
v_r_894_ = lean_ctor_get(v_l_877_, 4);
v_size_895_ = lean_ctor_get(v_r_878_, 0);
v___x_896_ = lean_unsigned_to_nat(2u);
v___x_897_ = lean_nat_mul(v___x_896_, v_size_895_);
v___x_898_ = lean_nat_dec_lt(v_size_890_, v___x_897_);
lean_dec(v___x_897_);
if (v___x_898_ == 0)
{
lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_926_; 
lean_inc(v_r_894_);
lean_inc(v_l_893_);
lean_inc(v_v_892_);
lean_inc(v_k_891_);
v_isSharedCheck_926_ = !lean_is_exclusive(v_l_877_);
if (v_isSharedCheck_926_ == 0)
{
lean_object* v_unused_927_; lean_object* v_unused_928_; lean_object* v_unused_929_; lean_object* v_unused_930_; lean_object* v_unused_931_; 
v_unused_927_ = lean_ctor_get(v_l_877_, 4);
lean_dec(v_unused_927_);
v_unused_928_ = lean_ctor_get(v_l_877_, 3);
lean_dec(v_unused_928_);
v_unused_929_ = lean_ctor_get(v_l_877_, 2);
lean_dec(v_unused_929_);
v_unused_930_ = lean_ctor_get(v_l_877_, 1);
lean_dec(v_unused_930_);
v_unused_931_ = lean_ctor_get(v_l_877_, 0);
lean_dec(v_unused_931_);
v___x_900_ = v_l_877_;
v_isShared_901_ = v_isSharedCheck_926_;
goto v_resetjp_899_;
}
else
{
lean_dec(v_l_877_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_926_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_916_; 
v___x_902_ = lean_nat_add(v___x_872_, v_size_873_);
v___x_903_ = lean_nat_add(v___x_902_, v_size_874_);
lean_dec(v_size_874_);
if (lean_obj_tag(v_l_893_) == 0)
{
lean_object* v_size_924_; 
v_size_924_ = lean_ctor_get(v_l_893_, 0);
lean_inc(v_size_924_);
v___y_916_ = v_size_924_;
goto v___jp_915_;
}
else
{
lean_object* v___x_925_; 
v___x_925_ = lean_unsigned_to_nat(0u);
v___y_916_ = v___x_925_;
goto v___jp_915_;
}
v___jp_904_:
{
lean_object* v___x_908_; lean_object* v___x_910_; 
v___x_908_ = lean_nat_add(v___y_905_, v___y_907_);
lean_dec(v___y_907_);
lean_dec(v___y_905_);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 4, v_r_878_);
lean_ctor_set(v___x_900_, 3, v_r_894_);
lean_ctor_set(v___x_900_, 2, v_v_876_);
lean_ctor_set(v___x_900_, 1, v_k_875_);
lean_ctor_set(v___x_900_, 0, v___x_908_);
v___x_910_ = v___x_900_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_908_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v_k_875_);
lean_ctor_set(v_reuseFailAlloc_914_, 2, v_v_876_);
lean_ctor_set(v_reuseFailAlloc_914_, 3, v_r_894_);
lean_ctor_set(v_reuseFailAlloc_914_, 4, v_r_878_);
v___x_910_ = v_reuseFailAlloc_914_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
lean_object* v___x_912_; 
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 4, v___x_910_);
lean_ctor_set(v___x_888_, 3, v___y_906_);
lean_ctor_set(v___x_888_, 2, v_v_892_);
lean_ctor_set(v___x_888_, 1, v_k_891_);
lean_ctor_set(v___x_888_, 0, v___x_903_);
v___x_912_ = v___x_888_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_903_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_k_891_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v_v_892_);
lean_ctor_set(v_reuseFailAlloc_913_, 3, v___y_906_);
lean_ctor_set(v_reuseFailAlloc_913_, 4, v___x_910_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
v___jp_915_:
{
lean_object* v___x_917_; lean_object* v___x_919_; 
v___x_917_ = lean_nat_add(v___x_902_, v___y_916_);
lean_dec(v___y_916_);
lean_dec(v___x_902_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 4, v_l_893_);
lean_ctor_set(v___x_728_, 0, v___x_917_);
v___x_919_ = v___x_728_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v_k_723_);
lean_ctor_set(v_reuseFailAlloc_923_, 2, v_v_724_);
lean_ctor_set(v_reuseFailAlloc_923_, 3, v_l_725_);
lean_ctor_set(v_reuseFailAlloc_923_, 4, v_l_893_);
v___x_919_ = v_reuseFailAlloc_923_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
lean_object* v___x_920_; 
v___x_920_ = lean_nat_add(v___x_872_, v_size_895_);
if (lean_obj_tag(v_r_894_) == 0)
{
lean_object* v_size_921_; 
v_size_921_ = lean_ctor_get(v_r_894_, 0);
lean_inc(v_size_921_);
v___y_905_ = v___x_920_;
v___y_906_ = v___x_919_;
v___y_907_ = v_size_921_;
goto v___jp_904_;
}
else
{
lean_object* v___x_922_; 
v___x_922_ = lean_unsigned_to_nat(0u);
v___y_905_ = v___x_920_;
v___y_906_ = v___x_919_;
v___y_907_ = v___x_922_;
goto v___jp_904_;
}
}
}
}
}
else
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_936_; 
lean_del_object(v___x_728_);
v___x_932_ = lean_nat_add(v___x_872_, v_size_873_);
v___x_933_ = lean_nat_add(v___x_932_, v_size_874_);
lean_dec(v_size_874_);
v___x_934_ = lean_nat_add(v___x_932_, v_size_890_);
lean_dec(v___x_932_);
lean_inc_ref(v_l_725_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 4, v_l_877_);
lean_ctor_set(v___x_888_, 3, v_l_725_);
lean_ctor_set(v___x_888_, 2, v_v_724_);
lean_ctor_set(v___x_888_, 1, v_k_723_);
lean_ctor_set(v___x_888_, 0, v___x_934_);
v___x_936_ = v___x_888_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_934_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_k_723_);
lean_ctor_set(v_reuseFailAlloc_949_, 2, v_v_724_);
lean_ctor_set(v_reuseFailAlloc_949_, 3, v_l_725_);
lean_ctor_set(v_reuseFailAlloc_949_, 4, v_l_877_);
v___x_936_ = v_reuseFailAlloc_949_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
v_isSharedCheck_943_ = !lean_is_exclusive(v_l_725_);
if (v_isSharedCheck_943_ == 0)
{
lean_object* v_unused_944_; lean_object* v_unused_945_; lean_object* v_unused_946_; lean_object* v_unused_947_; lean_object* v_unused_948_; 
v_unused_944_ = lean_ctor_get(v_l_725_, 4);
lean_dec(v_unused_944_);
v_unused_945_ = lean_ctor_get(v_l_725_, 3);
lean_dec(v_unused_945_);
v_unused_946_ = lean_ctor_get(v_l_725_, 2);
lean_dec(v_unused_946_);
v_unused_947_ = lean_ctor_get(v_l_725_, 1);
lean_dec(v_unused_947_);
v_unused_948_ = lean_ctor_get(v_l_725_, 0);
lean_dec(v_unused_948_);
v___x_938_ = v_l_725_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_dec(v_l_725_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 4, v_r_878_);
lean_ctor_set(v___x_938_, 3, v___x_936_);
lean_ctor_set(v___x_938_, 2, v_v_876_);
lean_ctor_set(v___x_938_, 1, v_k_875_);
lean_ctor_set(v___x_938_, 0, v___x_933_);
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_933_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_k_875_);
lean_ctor_set(v_reuseFailAlloc_942_, 2, v_v_876_);
lean_ctor_set(v_reuseFailAlloc_942_, 3, v___x_936_);
lean_ctor_set(v_reuseFailAlloc_942_, 4, v_r_878_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_956_; 
v_l_956_ = lean_ctor_get(v_impl_871_, 3);
lean_inc(v_l_956_);
if (lean_obj_tag(v_l_956_) == 0)
{
lean_object* v_r_957_; lean_object* v_k_958_; lean_object* v_v_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_982_; 
v_r_957_ = lean_ctor_get(v_impl_871_, 4);
v_k_958_ = lean_ctor_get(v_impl_871_, 1);
v_v_959_ = lean_ctor_get(v_impl_871_, 2);
v_isSharedCheck_982_ = !lean_is_exclusive(v_impl_871_);
if (v_isSharedCheck_982_ == 0)
{
lean_object* v_unused_983_; lean_object* v_unused_984_; 
v_unused_983_ = lean_ctor_get(v_impl_871_, 3);
lean_dec(v_unused_983_);
v_unused_984_ = lean_ctor_get(v_impl_871_, 0);
lean_dec(v_unused_984_);
v___x_961_ = v_impl_871_;
v_isShared_962_ = v_isSharedCheck_982_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_r_957_);
lean_inc(v_v_959_);
lean_inc(v_k_958_);
lean_dec(v_impl_871_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_982_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v_k_963_; lean_object* v_v_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_978_; 
v_k_963_ = lean_ctor_get(v_l_956_, 1);
v_v_964_ = lean_ctor_get(v_l_956_, 2);
v_isSharedCheck_978_ = !lean_is_exclusive(v_l_956_);
if (v_isSharedCheck_978_ == 0)
{
lean_object* v_unused_979_; lean_object* v_unused_980_; lean_object* v_unused_981_; 
v_unused_979_ = lean_ctor_get(v_l_956_, 4);
lean_dec(v_unused_979_);
v_unused_980_ = lean_ctor_get(v_l_956_, 3);
lean_dec(v_unused_980_);
v_unused_981_ = lean_ctor_get(v_l_956_, 0);
lean_dec(v_unused_981_);
v___x_966_ = v_l_956_;
v_isShared_967_ = v_isSharedCheck_978_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_v_964_);
lean_inc(v_k_963_);
lean_dec(v_l_956_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_978_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_968_; lean_object* v___x_970_; 
v___x_968_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_957_, 2);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 4, v_r_957_);
lean_ctor_set(v___x_966_, 3, v_r_957_);
lean_ctor_set(v___x_966_, 2, v_v_724_);
lean_ctor_set(v___x_966_, 1, v_k_723_);
lean_ctor_set(v___x_966_, 0, v___x_872_);
v___x_970_ = v___x_966_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_k_723_);
lean_ctor_set(v_reuseFailAlloc_977_, 2, v_v_724_);
lean_ctor_set(v_reuseFailAlloc_977_, 3, v_r_957_);
lean_ctor_set(v_reuseFailAlloc_977_, 4, v_r_957_);
v___x_970_ = v_reuseFailAlloc_977_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
lean_object* v___x_972_; 
lean_inc(v_r_957_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 3, v_r_957_);
lean_ctor_set(v___x_961_, 0, v___x_872_);
v___x_972_ = v___x_961_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_k_958_);
lean_ctor_set(v_reuseFailAlloc_976_, 2, v_v_959_);
lean_ctor_set(v_reuseFailAlloc_976_, 3, v_r_957_);
lean_ctor_set(v_reuseFailAlloc_976_, 4, v_r_957_);
v___x_972_ = v_reuseFailAlloc_976_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
lean_object* v___x_974_; 
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 4, v___x_972_);
lean_ctor_set(v___x_728_, 3, v___x_970_);
lean_ctor_set(v___x_728_, 2, v_v_964_);
lean_ctor_set(v___x_728_, 1, v_k_963_);
lean_ctor_set(v___x_728_, 0, v___x_968_);
v___x_974_ = v___x_728_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_k_963_);
lean_ctor_set(v_reuseFailAlloc_975_, 2, v_v_964_);
lean_ctor_set(v_reuseFailAlloc_975_, 3, v___x_970_);
lean_ctor_set(v_reuseFailAlloc_975_, 4, v___x_972_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
}
}
else
{
lean_object* v_r_985_; 
v_r_985_ = lean_ctor_get(v_impl_871_, 4);
lean_inc(v_r_985_);
if (lean_obj_tag(v_r_985_) == 0)
{
lean_object* v_k_986_; lean_object* v_v_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_998_; 
v_k_986_ = lean_ctor_get(v_impl_871_, 1);
v_v_987_ = lean_ctor_get(v_impl_871_, 2);
v_isSharedCheck_998_ = !lean_is_exclusive(v_impl_871_);
if (v_isSharedCheck_998_ == 0)
{
lean_object* v_unused_999_; lean_object* v_unused_1000_; lean_object* v_unused_1001_; 
v_unused_999_ = lean_ctor_get(v_impl_871_, 4);
lean_dec(v_unused_999_);
v_unused_1000_ = lean_ctor_get(v_impl_871_, 3);
lean_dec(v_unused_1000_);
v_unused_1001_ = lean_ctor_get(v_impl_871_, 0);
lean_dec(v_unused_1001_);
v___x_989_ = v_impl_871_;
v_isShared_990_ = v_isSharedCheck_998_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_v_987_);
lean_inc(v_k_986_);
lean_dec(v_impl_871_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_998_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_991_ = lean_unsigned_to_nat(3u);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 4, v_l_956_);
lean_ctor_set(v___x_989_, 2, v_v_724_);
lean_ctor_set(v___x_989_, 1, v_k_723_);
lean_ctor_set(v___x_989_, 0, v___x_872_);
v___x_993_ = v___x_989_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_k_723_);
lean_ctor_set(v_reuseFailAlloc_997_, 2, v_v_724_);
lean_ctor_set(v_reuseFailAlloc_997_, 3, v_l_956_);
lean_ctor_set(v_reuseFailAlloc_997_, 4, v_l_956_);
v___x_993_ = v_reuseFailAlloc_997_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_995_; 
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 4, v_r_985_);
lean_ctor_set(v___x_728_, 3, v___x_993_);
lean_ctor_set(v___x_728_, 2, v_v_987_);
lean_ctor_set(v___x_728_, 1, v_k_986_);
lean_ctor_set(v___x_728_, 0, v___x_991_);
v___x_995_ = v___x_728_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v_k_986_);
lean_ctor_set(v_reuseFailAlloc_996_, 2, v_v_987_);
lean_ctor_set(v_reuseFailAlloc_996_, 3, v___x_993_);
lean_ctor_set(v_reuseFailAlloc_996_, 4, v_r_985_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
else
{
lean_object* v___x_1002_; lean_object* v___x_1004_; 
v___x_1002_ = lean_unsigned_to_nat(2u);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 4, v_impl_871_);
lean_ctor_set(v___x_728_, 3, v_r_985_);
lean_ctor_set(v___x_728_, 0, v___x_1002_);
v___x_1004_ = v___x_728_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_1002_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v_k_723_);
lean_ctor_set(v_reuseFailAlloc_1005_, 2, v_v_724_);
lean_ctor_set(v_reuseFailAlloc_1005_, 3, v_r_985_);
lean_ctor_set(v_reuseFailAlloc_1005_, 4, v_impl_871_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
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
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = lean_unsigned_to_nat(1u);
v___x_1008_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v_k_719_);
lean_ctor_set(v___x_1008_, 2, v_v_720_);
lean_ctor_set(v___x_1008_, 3, v_t_721_);
lean_ctor_set(v___x_1008_, 4, v_t_721_);
return v___x_1008_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_LeanOptions_fromOptions_x3f_spec__1(lean_object* v_init_1009_, lean_object* v_x_1010_){
_start:
{
if (lean_obj_tag(v_x_1010_) == 0)
{
lean_object* v_k_1011_; lean_object* v_v_1012_; lean_object* v_l_1013_; lean_object* v_r_1014_; lean_object* v___x_1015_; 
v_k_1011_ = lean_ctor_get(v_x_1010_, 1);
lean_inc(v_k_1011_);
v_v_1012_ = lean_ctor_get(v_x_1010_, 2);
lean_inc(v_v_1012_);
v_l_1013_ = lean_ctor_get(v_x_1010_, 3);
lean_inc(v_l_1013_);
v_r_1014_ = lean_ctor_get(v_x_1010_, 4);
lean_inc(v_r_1014_);
lean_dec_ref_known(v_x_1010_, 5);
v___x_1015_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_LeanOptions_fromOptions_x3f_spec__1(v_init_1009_, v_l_1013_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_dec(v_r_1014_);
lean_dec(v_v_1012_);
lean_dec(v_k_1011_);
return v___x_1015_;
}
else
{
lean_object* v_val_1016_; lean_object* v_a_1017_; lean_object* v___x_1018_; 
v_val_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_val_1016_);
lean_dec_ref_known(v___x_1015_, 1);
v_a_1017_ = lean_ctor_get(v_val_1016_, 0);
lean_inc(v_a_1017_);
lean_dec(v_val_1016_);
v___x_1018_ = l_Lean_LeanOptionValue_ofDataValue_x3f(v_v_1012_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v___x_1019_; 
lean_dec(v_a_1017_);
lean_dec(v_r_1014_);
lean_dec(v_k_1011_);
v___x_1019_ = lean_box(0);
return v___x_1019_;
}
else
{
lean_object* v_val_1020_; lean_object* v___x_1021_; 
v_val_1020_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_val_1020_);
lean_dec_ref_known(v___x_1018_, 1);
v___x_1021_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_LeanOptions_fromOptions_x3f_spec__0___redArg(v_k_1011_, v_val_1020_, v_a_1017_);
v_init_1009_ = v___x_1021_;
v_x_1010_ = v_r_1014_;
goto _start;
}
}
}
else
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1023_, 0, v_init_1009_);
v___x_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
return v___x_1024_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LeanOptions_fromOptions_x3f(lean_object* v_options_1025_){
_start:
{
lean_object* v_map_1026_; lean_object* v_values_1027_; lean_object* v___x_1028_; 
v_map_1026_ = lean_ctor_get(v_options_1025_, 0);
lean_inc(v_map_1026_);
lean_dec_ref(v_options_1025_);
v_values_1027_ = lean_box(1);
v___x_1028_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_LeanOptions_fromOptions_x3f_spec__1(v_values_1027_, v_map_1026_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v___x_1029_; 
v___x_1029_ = lean_box(0);
return v___x_1029_;
}
else
{
lean_object* v_val_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1038_; 
v_val_1030_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1032_ = v___x_1028_;
v_isShared_1033_ = v_isSharedCheck_1038_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_val_1030_);
lean_dec(v___x_1028_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1038_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v_a_1034_; lean_object* v___x_1036_; 
v_a_1034_ = lean_ctor_get(v_val_1030_, 0);
lean_inc(v_a_1034_);
lean_dec(v_val_1030_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 0, v_a_1034_);
v___x_1036_ = v___x_1032_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1034_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_LeanOptions_fromOptions_x3f_spec__0(lean_object* v_00_u03b2_1039_, lean_object* v_k_1040_, lean_object* v_v_1041_, lean_object* v_t_1042_, lean_object* v_hl_1043_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_LeanOptions_fromOptions_x3f_spec__0___redArg(v_k_1040_, v_v_1041_, v_t_1042_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonLeanOptions___lam__0(lean_object* v___f_1045_, lean_object* v_j_1046_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l_Lean_NameMap_fromJson_x3f___redArg(v___f_1045_, v_j_1046_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_1047_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1047_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
v_a_1056_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1047_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1047_);
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
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonLeanOptions___lam__0(lean_object* v___f_1067_, lean_object* v_options_1068_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Lean_NameMap_toJson___redArg(v___f_1067_, v_options_1068_);
return v___x_1069_;
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

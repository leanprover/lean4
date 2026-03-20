// Lean compiler output
// Module: Lean.Data.KVMap
// Imports: public import Init.Data.Format.Syntax public import Init.Data.ToString.Name public import Init.Data.ToString.Extra
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
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_instToString___lam__0(lean_object*);
lean_object* l_instToStringProd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Lean_Syntax_instRepr_repr(lean_object*, lean_object*);
lean_object* l_List_forIn_x27_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DataValue_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_DataValue_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_DataValue_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DataValue_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DataValue_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DataValue_ofString_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DataValue_ofString_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DataValue_ofBool_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DataValue_ofBool_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DataValue_ofName_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DataValue_ofName_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DataValue_ofNat_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DataValue_ofNat_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DataValue_ofInt_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DataValue_ofInt_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DataValue_ofSyntax_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DataValue_ofSyntax_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_instInhabitedDataValue_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_instInhabitedDataValue_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedDataValue_default___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedDataValue_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedDataValue_default___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedDataValue_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedDataValue_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedDataValue_default = (const lean_object*)&l_Lean_instInhabitedDataValue_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedDataValue = (const lean_object*)&l_Lean_instInhabitedDataValue_default___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_instBEqDataValue_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqDataValue_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqDataValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqDataValue_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqDataValue___closed__0 = (const lean_object*)&l_Lean_instBEqDataValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqDataValue = (const lean_object*)&l_Lean_instBEqDataValue___closed__0_value;
static const lean_string_object l_Lean_instReprDataValue_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.DataValue.ofString"};
static const lean_object* l_Lean_instReprDataValue_repr___closed__0 = (const lean_object*)&l_Lean_instReprDataValue_repr___closed__0_value;
static const lean_ctor_object l_Lean_instReprDataValue_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprDataValue_repr___closed__0_value)}};
static const lean_object* l_Lean_instReprDataValue_repr___closed__1 = (const lean_object*)&l_Lean_instReprDataValue_repr___closed__1_value;
static const lean_ctor_object l_Lean_instReprDataValue_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprDataValue_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprDataValue_repr___closed__2 = (const lean_object*)&l_Lean_instReprDataValue_repr___closed__2_value;
static lean_once_cell_t l_Lean_instReprDataValue_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprDataValue_repr___closed__3;
static lean_once_cell_t l_Lean_instReprDataValue_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprDataValue_repr___closed__4;
static const lean_string_object l_Lean_instReprDataValue_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.DataValue.ofBool"};
static const lean_object* l_Lean_instReprDataValue_repr___closed__5 = (const lean_object*)&l_Lean_instReprDataValue_repr___closed__5_value;
static const lean_ctor_object l_Lean_instReprDataValue_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprDataValue_repr___closed__5_value)}};
static const lean_object* l_Lean_instReprDataValue_repr___closed__6 = (const lean_object*)&l_Lean_instReprDataValue_repr___closed__6_value;
static const lean_ctor_object l_Lean_instReprDataValue_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprDataValue_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprDataValue_repr___closed__7 = (const lean_object*)&l_Lean_instReprDataValue_repr___closed__7_value;
static const lean_string_object l_Lean_instReprDataValue_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.DataValue.ofName"};
static const lean_object* l_Lean_instReprDataValue_repr___closed__8 = (const lean_object*)&l_Lean_instReprDataValue_repr___closed__8_value;
static const lean_ctor_object l_Lean_instReprDataValue_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprDataValue_repr___closed__8_value)}};
static const lean_object* l_Lean_instReprDataValue_repr___closed__9 = (const lean_object*)&l_Lean_instReprDataValue_repr___closed__9_value;
static const lean_ctor_object l_Lean_instReprDataValue_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprDataValue_repr___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprDataValue_repr___closed__10 = (const lean_object*)&l_Lean_instReprDataValue_repr___closed__10_value;
static const lean_string_object l_Lean_instReprDataValue_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.DataValue.ofNat"};
static const lean_object* l_Lean_instReprDataValue_repr___closed__11 = (const lean_object*)&l_Lean_instReprDataValue_repr___closed__11_value;
static const lean_ctor_object l_Lean_instReprDataValue_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprDataValue_repr___closed__11_value)}};
static const lean_object* l_Lean_instReprDataValue_repr___closed__12 = (const lean_object*)&l_Lean_instReprDataValue_repr___closed__12_value;
static const lean_ctor_object l_Lean_instReprDataValue_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprDataValue_repr___closed__12_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprDataValue_repr___closed__13 = (const lean_object*)&l_Lean_instReprDataValue_repr___closed__13_value;
static const lean_string_object l_Lean_instReprDataValue_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.DataValue.ofInt"};
static const lean_object* l_Lean_instReprDataValue_repr___closed__14 = (const lean_object*)&l_Lean_instReprDataValue_repr___closed__14_value;
static const lean_ctor_object l_Lean_instReprDataValue_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprDataValue_repr___closed__14_value)}};
static const lean_object* l_Lean_instReprDataValue_repr___closed__15 = (const lean_object*)&l_Lean_instReprDataValue_repr___closed__15_value;
static const lean_ctor_object l_Lean_instReprDataValue_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprDataValue_repr___closed__15_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprDataValue_repr___closed__16 = (const lean_object*)&l_Lean_instReprDataValue_repr___closed__16_value;
static lean_once_cell_t l_Lean_instReprDataValue_repr___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprDataValue_repr___closed__17;
static const lean_string_object l_Lean_instReprDataValue_repr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.DataValue.ofSyntax"};
static const lean_object* l_Lean_instReprDataValue_repr___closed__18 = (const lean_object*)&l_Lean_instReprDataValue_repr___closed__18_value;
static const lean_ctor_object l_Lean_instReprDataValue_repr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprDataValue_repr___closed__18_value)}};
static const lean_object* l_Lean_instReprDataValue_repr___closed__19 = (const lean_object*)&l_Lean_instReprDataValue_repr___closed__19_value;
static const lean_ctor_object l_Lean_instReprDataValue_repr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprDataValue_repr___closed__19_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprDataValue_repr___closed__20 = (const lean_object*)&l_Lean_instReprDataValue_repr___closed__20_value;
LEAN_EXPORT lean_object* l_Lean_instReprDataValue_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprDataValue_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprDataValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprDataValue_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprDataValue___closed__0 = (const lean_object*)&l_Lean_instReprDataValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprDataValue = (const lean_object*)&l_Lean_instReprDataValue___closed__0_value;
LEAN_EXPORT uint8_t lean_data_value_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DataValue_beqExp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_bool_data_value(uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkBoolDataValueEx___boxed(lean_object*);
LEAN_EXPORT uint8_t lean_data_value_bool(lean_object*);
LEAN_EXPORT lean_object* l_Lean_DataValue_getBoolEx___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_DataValue_sameCtor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DataValue_sameCtor___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_DataValue_str___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_DataValue_str___closed__0 = (const lean_object*)&l_Lean_DataValue_str___closed__0_value;
static const lean_string_object l_Lean_DataValue_str___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_DataValue_str___closed__1 = (const lean_object*)&l_Lean_DataValue_str___closed__1_value;
static const lean_string_object l_Lean_DataValue_str___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lean_DataValue_str___closed__2 = (const lean_object*)&l_Lean_DataValue_str___closed__2_value;
LEAN_EXPORT lean_object* lean_data_value_to_string(lean_object*);
static const lean_closure_object l_Lean_instToStringDataValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lean_data_value_to_string, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToStringDataValue___closed__0 = (const lean_object*)&l_Lean_instToStringDataValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToStringDataValue = (const lean_object*)&l_Lean_instToStringDataValue___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instCoeStringDataValue___lam__0(lean_object*);
static const lean_closure_object l_Lean_instCoeStringDataValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instCoeStringDataValue___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instCoeStringDataValue___closed__0 = (const lean_object*)&l_Lean_instCoeStringDataValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instCoeStringDataValue = (const lean_object*)&l_Lean_instCoeStringDataValue___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instCoeBoolDataValue___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_instCoeBoolDataValue___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instCoeBoolDataValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instCoeBoolDataValue___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instCoeBoolDataValue___closed__0 = (const lean_object*)&l_Lean_instCoeBoolDataValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instCoeBoolDataValue = (const lean_object*)&l_Lean_instCoeBoolDataValue___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instCoeNameDataValue___lam__0(lean_object*);
static const lean_closure_object l_Lean_instCoeNameDataValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instCoeNameDataValue___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instCoeNameDataValue___closed__0 = (const lean_object*)&l_Lean_instCoeNameDataValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instCoeNameDataValue = (const lean_object*)&l_Lean_instCoeNameDataValue___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instCoeNatDataValue___lam__0(lean_object*);
static const lean_closure_object l_Lean_instCoeNatDataValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instCoeNatDataValue___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instCoeNatDataValue___closed__0 = (const lean_object*)&l_Lean_instCoeNatDataValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instCoeNatDataValue = (const lean_object*)&l_Lean_instCoeNatDataValue___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instCoeIntDataValue___lam__0(lean_object*);
static const lean_closure_object l_Lean_instCoeIntDataValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instCoeIntDataValue___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instCoeIntDataValue___closed__0 = (const lean_object*)&l_Lean_instCoeIntDataValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instCoeIntDataValue = (const lean_object*)&l_Lean_instCoeIntDataValue___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instCoeSyntaxDataValue___lam__0(lean_object*);
static const lean_closure_object l_Lean_instCoeSyntaxDataValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instCoeSyntaxDataValue___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instCoeSyntaxDataValue___closed__0 = (const lean_object*)&l_Lean_instCoeSyntaxDataValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instCoeSyntaxDataValue = (const lean_object*)&l_Lean_instCoeSyntaxDataValue___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedKVMap_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedKVMap;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprKVMap_repr_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0_spec__2(lean_object*, lean_object*);
static const lean_string_object l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__0_value;
static const lean_string_object l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__1_value;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__1_value)}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__2_value;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__3 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__3_value;
static const lean_string_object l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__4 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__4_value;
static lean_once_cell_t l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__5;
static lean_once_cell_t l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__6;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__0_value)}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__7 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__7_value;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__4_value)}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__8 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__8_value;
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1(lean_object*, lean_object*);
static const lean_string_object l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__0 = (const lean_object*)&l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__0_value)}};
static const lean_object* l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__1 = (const lean_object*)&l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__1_value;
static const lean_string_object l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__2 = (const lean_object*)&l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__2_value;
static const lean_string_object l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__3 = (const lean_object*)&l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__3_value;
static lean_once_cell_t l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__4;
static lean_once_cell_t l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__5;
static const lean_ctor_object l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__2_value)}};
static const lean_object* l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__6 = (const lean_object*)&l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__6_value;
static const lean_ctor_object l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__3_value)}};
static const lean_object* l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__7 = (const lean_object*)&l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__7_value;
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg(lean_object*);
static const lean_string_object l_Lean_instReprKVMap_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_instReprKVMap_repr___redArg___closed__0 = (const lean_object*)&l_Lean_instReprKVMap_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_instReprKVMap_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "entries"};
static const lean_object* l_Lean_instReprKVMap_repr___redArg___closed__1 = (const lean_object*)&l_Lean_instReprKVMap_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_instReprKVMap_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprKVMap_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_instReprKVMap_repr___redArg___closed__2 = (const lean_object*)&l_Lean_instReprKVMap_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_instReprKVMap_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprKVMap_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_instReprKVMap_repr___redArg___closed__3 = (const lean_object*)&l_Lean_instReprKVMap_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_instReprKVMap_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_instReprKVMap_repr___redArg___closed__4 = (const lean_object*)&l_Lean_instReprKVMap_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_instReprKVMap_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprKVMap_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_instReprKVMap_repr___redArg___closed__5 = (const lean_object*)&l_Lean_instReprKVMap_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_instReprKVMap_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprKVMap_repr___redArg___closed__3_value),((lean_object*)&l_Lean_instReprKVMap_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_instReprKVMap_repr___redArg___closed__6 = (const lean_object*)&l_Lean_instReprKVMap_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_instReprKVMap_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprKVMap_repr___redArg___closed__7;
static const lean_string_object l_Lean_instReprKVMap_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_instReprKVMap_repr___redArg___closed__8 = (const lean_object*)&l_Lean_instReprKVMap_repr___redArg___closed__8_value;
static lean_once_cell_t l_Lean_instReprKVMap_repr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprKVMap_repr___redArg___closed__9;
static lean_once_cell_t l_Lean_instReprKVMap_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprKVMap_repr___redArg___closed__10;
static const lean_ctor_object l_Lean_instReprKVMap_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprKVMap_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_instReprKVMap_repr___redArg___closed__11 = (const lean_object*)&l_Lean_instReprKVMap_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lean_instReprKVMap_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprKVMap_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_instReprKVMap_repr___redArg___closed__12 = (const lean_object*)&l_Lean_instReprKVMap_repr___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_instReprKVMap_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprKVMap_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprKVMap_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprKVMap_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprKVMap___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprKVMap_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprKVMap___closed__0 = (const lean_object*)&l_Lean_instReprKVMap___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprKVMap = (const lean_object*)&l_Lean_instReprKVMap___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_KVMap_instToString___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_KVMap_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_instToString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_KVMap_instToString___closed__0 = (const lean_object*)&l_Lean_KVMap_instToString___closed__0_value;
static const lean_closure_object l_Lean_KVMap_instToString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringProd___redArg___lam__0, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_KVMap_instToString___closed__0_value),((lean_object*)&l_Lean_instToStringDataValue___closed__0_value)} };
static const lean_object* l_Lean_KVMap_instToString___closed__1 = (const lean_object*)&l_Lean_KVMap_instToString___closed__1_value;
static const lean_closure_object l_Lean_KVMap_instToString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_KVMap_instToString___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_KVMap_instToString___closed__1_value)} };
static const lean_object* l_Lean_KVMap_instToString___closed__2 = (const lean_object*)&l_Lean_KVMap_instToString___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_KVMap_instToString = (const lean_object*)&l_Lean_KVMap_instToString___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_KVMap_empty;
LEAN_EXPORT uint8_t l_Lean_KVMap_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_isEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_size___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_findCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_findCore___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_find___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_findD(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_findD___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_insertCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_KVMap_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_KVMap_erase_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_KVMap_erase_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_erase___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_getString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_getString___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_getNat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_getNat___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_getInt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_getInt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_KVMap_getBool___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_getName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_getName___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_getSyntax(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_getSyntax___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_setString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_setNat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_setInt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_setBool(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_KVMap_setBool___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_setName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_setSyntax(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_updateString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_updateNat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_updateInt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_updateBool(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_updateName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_updateSyntax(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_forIn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_instForInProdNameDataValueOfMonad(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_KVMap_subsetAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_subsetAux___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_KVMap_subset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_subset___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_mergeBy(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_KVMap_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_eqv___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_KVMap_instBEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_KVMap_eqv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_KVMap_instBEq___closed__0 = (const lean_object*)&l_Lean_KVMap_instBEq___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_KVMap_instBEq = (const lean_object*)&l_Lean_KVMap_instBEq___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_KVMap_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_get_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_get___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_set___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_set(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_update___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_update(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueDataValue___lam__0(lean_object*);
static const lean_closure_object l_Lean_KVMap_instValueDataValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_KVMap_instValueDataValue___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_KVMap_instValueDataValue___closed__0 = (const lean_object*)&l_Lean_KVMap_instValueDataValue___closed__0_value;
static const lean_closure_object l_Lean_KVMap_instValueDataValue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_KVMap_instValueDataValue___closed__1 = (const lean_object*)&l_Lean_KVMap_instValueDataValue___closed__1_value;
static const lean_ctor_object l_Lean_KVMap_instValueDataValue___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_KVMap_instValueDataValue___closed__1_value),((lean_object*)&l_Lean_KVMap_instValueDataValue___closed__0_value)}};
static const lean_object* l_Lean_KVMap_instValueDataValue___closed__2 = (const lean_object*)&l_Lean_KVMap_instValueDataValue___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_KVMap_instValueDataValue = (const lean_object*)&l_Lean_KVMap_instValueDataValue___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueBool___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueBool___lam__1___boxed(lean_object*);
static const lean_closure_object l_Lean_KVMap_instValueBool___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_KVMap_instValueBool___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_KVMap_instValueBool___closed__0 = (const lean_object*)&l_Lean_KVMap_instValueBool___closed__0_value;
static const lean_ctor_object l_Lean_KVMap_instValueBool___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instCoeBoolDataValue___closed__0_value),((lean_object*)&l_Lean_KVMap_instValueBool___closed__0_value)}};
static const lean_object* l_Lean_KVMap_instValueBool___closed__1 = (const lean_object*)&l_Lean_KVMap_instValueBool___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_KVMap_instValueBool = (const lean_object*)&l_Lean_KVMap_instValueBool___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueNat___lam__1(lean_object*);
static const lean_closure_object l_Lean_KVMap_instValueNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_KVMap_instValueNat___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_KVMap_instValueNat___closed__0 = (const lean_object*)&l_Lean_KVMap_instValueNat___closed__0_value;
static const lean_ctor_object l_Lean_KVMap_instValueNat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instCoeNatDataValue___closed__0_value),((lean_object*)&l_Lean_KVMap_instValueNat___closed__0_value)}};
static const lean_object* l_Lean_KVMap_instValueNat___closed__1 = (const lean_object*)&l_Lean_KVMap_instValueNat___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_KVMap_instValueNat = (const lean_object*)&l_Lean_KVMap_instValueNat___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueInt___lam__1(lean_object*);
static const lean_closure_object l_Lean_KVMap_instValueInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_KVMap_instValueInt___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_KVMap_instValueInt___closed__0 = (const lean_object*)&l_Lean_KVMap_instValueInt___closed__0_value;
static const lean_ctor_object l_Lean_KVMap_instValueInt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instCoeIntDataValue___closed__0_value),((lean_object*)&l_Lean_KVMap_instValueInt___closed__0_value)}};
static const lean_object* l_Lean_KVMap_instValueInt___closed__1 = (const lean_object*)&l_Lean_KVMap_instValueInt___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_KVMap_instValueInt = (const lean_object*)&l_Lean_KVMap_instValueInt___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueName___lam__1(lean_object*);
static const lean_closure_object l_Lean_KVMap_instValueName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_KVMap_instValueName___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_KVMap_instValueName___closed__0 = (const lean_object*)&l_Lean_KVMap_instValueName___closed__0_value;
static const lean_ctor_object l_Lean_KVMap_instValueName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instCoeNameDataValue___closed__0_value),((lean_object*)&l_Lean_KVMap_instValueName___closed__0_value)}};
static const lean_object* l_Lean_KVMap_instValueName___closed__1 = (const lean_object*)&l_Lean_KVMap_instValueName___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_KVMap_instValueName = (const lean_object*)&l_Lean_KVMap_instValueName___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueString___lam__1(lean_object*);
static const lean_closure_object l_Lean_KVMap_instValueString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_KVMap_instValueString___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_KVMap_instValueString___closed__0 = (const lean_object*)&l_Lean_KVMap_instValueString___closed__0_value;
static const lean_ctor_object l_Lean_KVMap_instValueString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instCoeStringDataValue___closed__0_value),((lean_object*)&l_Lean_KVMap_instValueString___closed__0_value)}};
static const lean_object* l_Lean_KVMap_instValueString___closed__1 = (const lean_object*)&l_Lean_KVMap_instValueString___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_KVMap_instValueString = (const lean_object*)&l_Lean_KVMap_instValueString___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueSyntax___lam__1(lean_object*);
static const lean_closure_object l_Lean_KVMap_instValueSyntax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_KVMap_instValueSyntax___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_KVMap_instValueSyntax___closed__0 = (const lean_object*)&l_Lean_KVMap_instValueSyntax___closed__0_value;
static const lean_ctor_object l_Lean_KVMap_instValueSyntax___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instCoeSyntaxDataValue___closed__0_value),((lean_object*)&l_Lean_KVMap_instValueSyntax___closed__0_value)}};
static const lean_object* l_Lean_KVMap_instValueSyntax___closed__1 = (const lean_object*)&l_Lean_KVMap_instValueSyntax___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_KVMap_instValueSyntax = (const lean_object*)&l_Lean_KVMap_instValueSyntax___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_DataValue_ctorIdx(lean_object* v_x_1_){
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
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
case 3:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
case 4:
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
default: 
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(5u);
return v___x_7_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_ctorIdx___boxed(lean_object* v_x_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_DataValue_ctorIdx(v_x_8_);
lean_dec_ref(v_x_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_ctorElim___redArg(lean_object* v_t_10_, lean_object* v_k_11_){
_start:
{
switch(lean_obj_tag(v_t_10_))
{
case 0:
{
lean_object* v_v_12_; lean_object* v___x_13_; 
v_v_12_ = lean_ctor_get(v_t_10_, 0);
lean_inc_ref(v_v_12_);
lean_dec_ref(v_t_10_);
v___x_13_ = lean_apply_1(v_k_11_, v_v_12_);
return v___x_13_;
}
case 1:
{
uint8_t v_v_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v_v_14_ = lean_ctor_get_uint8(v_t_10_, 0);
lean_dec_ref(v_t_10_);
v___x_15_ = lean_box(v_v_14_);
v___x_16_ = lean_apply_1(v_k_11_, v___x_15_);
return v___x_16_;
}
default: 
{
lean_object* v_v_17_; lean_object* v___x_18_; 
v_v_17_ = lean_ctor_get(v_t_10_, 0);
lean_inc(v_v_17_);
lean_dec_ref(v_t_10_);
v___x_18_ = lean_apply_1(v_k_11_, v_v_17_);
return v___x_18_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_ctorElim(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_DataValue_ctorElim___redArg(v_t_21_, v_k_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_ctorElim___boxed(lean_object* v_motive_25_, lean_object* v_ctorIdx_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_k_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_DataValue_ctorElim(v_motive_25_, v_ctorIdx_26_, v_t_27_, v_h_28_, v_k_29_);
lean_dec(v_ctorIdx_26_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_ofString_elim___redArg(lean_object* v_t_31_, lean_object* v_ofString_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_DataValue_ctorElim___redArg(v_t_31_, v_ofString_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_ofString_elim(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_ofString_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_DataValue_ctorElim___redArg(v_t_35_, v_ofString_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_ofBool_elim___redArg(lean_object* v_t_39_, lean_object* v_ofBool_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_DataValue_ctorElim___redArg(v_t_39_, v_ofBool_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_ofBool_elim(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_ofBool_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lean_DataValue_ctorElim___redArg(v_t_43_, v_ofBool_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_ofName_elim___redArg(lean_object* v_t_47_, lean_object* v_ofName_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lean_DataValue_ctorElim___redArg(v_t_47_, v_ofName_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_ofName_elim(lean_object* v_motive_50_, lean_object* v_t_51_, lean_object* v_h_52_, lean_object* v_ofName_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l_Lean_DataValue_ctorElim___redArg(v_t_51_, v_ofName_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_ofNat_elim___redArg(lean_object* v_t_55_, lean_object* v_ofNat_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_DataValue_ctorElim___redArg(v_t_55_, v_ofNat_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_ofNat_elim(lean_object* v_motive_58_, lean_object* v_t_59_, lean_object* v_h_60_, lean_object* v_ofNat_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l_Lean_DataValue_ctorElim___redArg(v_t_59_, v_ofNat_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_ofInt_elim___redArg(lean_object* v_t_63_, lean_object* v_ofInt_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_DataValue_ctorElim___redArg(v_t_63_, v_ofInt_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_ofInt_elim(lean_object* v_motive_66_, lean_object* v_t_67_, lean_object* v_h_68_, lean_object* v_ofInt_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_DataValue_ctorElim___redArg(v_t_67_, v_ofInt_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_ofSyntax_elim___redArg(lean_object* v_t_71_, lean_object* v_ofSyntax_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_DataValue_ctorElim___redArg(v_t_71_, v_ofSyntax_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_ofSyntax_elim(lean_object* v_motive_74_, lean_object* v_t_75_, lean_object* v_h_76_, lean_object* v_ofSyntax_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Lean_DataValue_ctorElim___redArg(v_t_75_, v_ofSyntax_77_);
return v___x_78_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqDataValue_beq(lean_object* v_x_84_, lean_object* v_x_85_){
_start:
{
switch(lean_obj_tag(v_x_84_))
{
case 0:
{
if (lean_obj_tag(v_x_85_) == 0)
{
lean_object* v_v_86_; lean_object* v_v_87_; uint8_t v___x_88_; 
v_v_86_ = lean_ctor_get(v_x_84_, 0);
lean_inc_ref(v_v_86_);
lean_dec_ref(v_x_84_);
v_v_87_ = lean_ctor_get(v_x_85_, 0);
lean_inc_ref(v_v_87_);
lean_dec_ref(v_x_85_);
v___x_88_ = lean_string_dec_eq(v_v_86_, v_v_87_);
lean_dec_ref(v_v_87_);
lean_dec_ref(v_v_86_);
return v___x_88_;
}
else
{
uint8_t v___x_89_; 
lean_dec_ref(v_x_84_);
lean_dec_ref(v_x_85_);
v___x_89_ = 0;
return v___x_89_;
}
}
case 1:
{
if (lean_obj_tag(v_x_85_) == 1)
{
uint8_t v_v_90_; 
v_v_90_ = lean_ctor_get_uint8(v_x_84_, 0);
lean_dec_ref(v_x_84_);
if (v_v_90_ == 0)
{
uint8_t v_v_91_; 
v_v_91_ = lean_ctor_get_uint8(v_x_85_, 0);
lean_dec_ref(v_x_85_);
if (v_v_91_ == 0)
{
uint8_t v___x_92_; 
v___x_92_ = 1;
return v___x_92_;
}
else
{
return v_v_90_;
}
}
else
{
uint8_t v_v_93_; 
v_v_93_ = lean_ctor_get_uint8(v_x_85_, 0);
lean_dec_ref(v_x_85_);
return v_v_93_;
}
}
else
{
uint8_t v___x_94_; 
lean_dec_ref(v_x_84_);
lean_dec_ref(v_x_85_);
v___x_94_ = 0;
return v___x_94_;
}
}
case 2:
{
if (lean_obj_tag(v_x_85_) == 2)
{
lean_object* v_v_95_; lean_object* v_v_96_; uint8_t v___x_97_; 
v_v_95_ = lean_ctor_get(v_x_84_, 0);
lean_inc(v_v_95_);
lean_dec_ref(v_x_84_);
v_v_96_ = lean_ctor_get(v_x_85_, 0);
lean_inc(v_v_96_);
lean_dec_ref(v_x_85_);
v___x_97_ = lean_name_eq(v_v_95_, v_v_96_);
lean_dec(v_v_96_);
lean_dec(v_v_95_);
return v___x_97_;
}
else
{
uint8_t v___x_98_; 
lean_dec_ref(v_x_84_);
lean_dec_ref(v_x_85_);
v___x_98_ = 0;
return v___x_98_;
}
}
case 3:
{
if (lean_obj_tag(v_x_85_) == 3)
{
lean_object* v_v_99_; lean_object* v_v_100_; uint8_t v___x_101_; 
v_v_99_ = lean_ctor_get(v_x_84_, 0);
lean_inc(v_v_99_);
lean_dec_ref(v_x_84_);
v_v_100_ = lean_ctor_get(v_x_85_, 0);
lean_inc(v_v_100_);
lean_dec_ref(v_x_85_);
v___x_101_ = lean_nat_dec_eq(v_v_99_, v_v_100_);
lean_dec(v_v_100_);
lean_dec(v_v_99_);
return v___x_101_;
}
else
{
uint8_t v___x_102_; 
lean_dec_ref(v_x_84_);
lean_dec_ref(v_x_85_);
v___x_102_ = 0;
return v___x_102_;
}
}
case 4:
{
if (lean_obj_tag(v_x_85_) == 4)
{
lean_object* v_v_103_; lean_object* v_v_104_; uint8_t v___x_105_; 
v_v_103_ = lean_ctor_get(v_x_84_, 0);
lean_inc(v_v_103_);
lean_dec_ref(v_x_84_);
v_v_104_ = lean_ctor_get(v_x_85_, 0);
lean_inc(v_v_104_);
lean_dec_ref(v_x_85_);
v___x_105_ = lean_int_dec_eq(v_v_103_, v_v_104_);
lean_dec(v_v_104_);
lean_dec(v_v_103_);
return v___x_105_;
}
else
{
uint8_t v___x_106_; 
lean_dec_ref(v_x_84_);
lean_dec_ref(v_x_85_);
v___x_106_ = 0;
return v___x_106_;
}
}
default: 
{
if (lean_obj_tag(v_x_85_) == 5)
{
lean_object* v_v_107_; lean_object* v_v_108_; uint8_t v___x_109_; 
v_v_107_ = lean_ctor_get(v_x_84_, 0);
lean_inc(v_v_107_);
lean_dec_ref(v_x_84_);
v_v_108_ = lean_ctor_get(v_x_85_, 0);
lean_inc(v_v_108_);
lean_dec_ref(v_x_85_);
v___x_109_ = l_Lean_Syntax_structEq(v_v_107_, v_v_108_);
return v___x_109_;
}
else
{
uint8_t v___x_110_; 
lean_dec_ref(v_x_84_);
lean_dec_ref(v_x_85_);
v___x_110_ = 0;
return v___x_110_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqDataValue_beq___boxed(lean_object* v_x_111_, lean_object* v_x_112_){
_start:
{
uint8_t v_res_113_; lean_object* v_r_114_; 
v_res_113_ = l_Lean_instBEqDataValue_beq(v_x_111_, v_x_112_);
v_r_114_ = lean_box(v_res_113_);
return v_r_114_;
}
}
static lean_object* _init_l_Lean_instReprDataValue_repr___closed__3(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_unsigned_to_nat(2u);
v___x_124_ = lean_nat_to_int(v___x_123_);
return v___x_124_;
}
}
static lean_object* _init_l_Lean_instReprDataValue_repr___closed__4(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = lean_unsigned_to_nat(1u);
v___x_126_ = lean_nat_to_int(v___x_125_);
return v___x_126_;
}
}
static lean_object* _init_l_Lean_instReprDataValue_repr___closed__17(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = lean_unsigned_to_nat(0u);
v___x_152_ = lean_nat_to_int(v___x_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprDataValue_repr(lean_object* v_x_159_, lean_object* v_prec_160_){
_start:
{
lean_object* v___y_162_; lean_object* v___y_163_; lean_object* v___y_164_; 
switch(lean_obj_tag(v_x_159_))
{
case 0:
{
lean_object* v_v_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_190_; 
v_v_170_ = lean_ctor_get(v_x_159_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v_x_159_);
if (v_isSharedCheck_190_ == 0)
{
v___x_172_ = v_x_159_;
v_isShared_173_ = v_isSharedCheck_190_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_v_170_);
lean_dec(v_x_159_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_190_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___y_175_; lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_186_ = lean_unsigned_to_nat(1024u);
v___x_187_ = lean_nat_dec_le(v___x_186_, v_prec_160_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; 
v___x_188_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__3, &l_Lean_instReprDataValue_repr___closed__3_once, _init_l_Lean_instReprDataValue_repr___closed__3);
v___y_175_ = v___x_188_;
goto v___jp_174_;
}
else
{
lean_object* v___x_189_; 
v___x_189_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__4, &l_Lean_instReprDataValue_repr___closed__4_once, _init_l_Lean_instReprDataValue_repr___closed__4);
v___y_175_ = v___x_189_;
goto v___jp_174_;
}
v___jp_174_:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_176_ = ((lean_object*)(l_Lean_instReprDataValue_repr___closed__2));
v___x_177_ = l_String_quote(v_v_170_);
if (v_isShared_173_ == 0)
{
lean_ctor_set_tag(v___x_172_, 3);
lean_ctor_set(v___x_172_, 0, v___x_177_);
v___x_179_ = v___x_172_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_177_);
v___x_179_ = v_reuseFailAlloc_185_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_176_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
v___x_181_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_181_, 0, v___y_175_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
v___x_182_ = 0;
v___x_183_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_183_, 0, v___x_181_);
lean_ctor_set_uint8(v___x_183_, sizeof(void*)*1, v___x_182_);
v___x_184_ = l_Repr_addAppParen(v___x_183_, v_prec_160_);
return v___x_184_;
}
}
}
}
case 1:
{
uint8_t v_v_191_; lean_object* v___y_193_; lean_object* v___x_201_; uint8_t v___x_202_; 
v_v_191_ = lean_ctor_get_uint8(v_x_159_, 0);
lean_dec_ref(v_x_159_);
v___x_201_ = lean_unsigned_to_nat(1024u);
v___x_202_ = lean_nat_dec_le(v___x_201_, v_prec_160_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; 
v___x_203_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__3, &l_Lean_instReprDataValue_repr___closed__3_once, _init_l_Lean_instReprDataValue_repr___closed__3);
v___y_193_ = v___x_203_;
goto v___jp_192_;
}
else
{
lean_object* v___x_204_; 
v___x_204_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__4, &l_Lean_instReprDataValue_repr___closed__4_once, _init_l_Lean_instReprDataValue_repr___closed__4);
v___y_193_ = v___x_204_;
goto v___jp_192_;
}
v___jp_192_:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; uint8_t v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_194_ = ((lean_object*)(l_Lean_instReprDataValue_repr___closed__7));
v___x_195_ = l_Bool_repr___redArg(v_v_191_);
v___x_196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_194_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
v___x_197_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_197_, 0, v___y_193_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
v___x_198_ = 0;
v___x_199_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_199_, 0, v___x_197_);
lean_ctor_set_uint8(v___x_199_, sizeof(void*)*1, v___x_198_);
v___x_200_ = l_Repr_addAppParen(v___x_199_, v_prec_160_);
return v___x_200_;
}
}
case 2:
{
lean_object* v_v_205_; lean_object* v___y_207_; lean_object* v___x_216_; uint8_t v___x_217_; 
v_v_205_ = lean_ctor_get(v_x_159_, 0);
lean_inc(v_v_205_);
lean_dec_ref(v_x_159_);
v___x_216_ = lean_unsigned_to_nat(1024u);
v___x_217_ = lean_nat_dec_le(v___x_216_, v_prec_160_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; 
v___x_218_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__3, &l_Lean_instReprDataValue_repr___closed__3_once, _init_l_Lean_instReprDataValue_repr___closed__3);
v___y_207_ = v___x_218_;
goto v___jp_206_;
}
else
{
lean_object* v___x_219_; 
v___x_219_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__4, &l_Lean_instReprDataValue_repr___closed__4_once, _init_l_Lean_instReprDataValue_repr___closed__4);
v___y_207_ = v___x_219_;
goto v___jp_206_;
}
v___jp_206_:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_208_ = ((lean_object*)(l_Lean_instReprDataValue_repr___closed__10));
v___x_209_ = lean_unsigned_to_nat(1024u);
v___x_210_ = l_Lean_Name_reprPrec(v_v_205_, v___x_209_);
v___x_211_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_208_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
v___x_212_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_212_, 0, v___y_207_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
v___x_213_ = 0;
v___x_214_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_214_, 0, v___x_212_);
lean_ctor_set_uint8(v___x_214_, sizeof(void*)*1, v___x_213_);
v___x_215_ = l_Repr_addAppParen(v___x_214_, v_prec_160_);
return v___x_215_;
}
}
case 3:
{
lean_object* v_v_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_240_; 
v_v_220_ = lean_ctor_get(v_x_159_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v_x_159_);
if (v_isSharedCheck_240_ == 0)
{
v___x_222_ = v_x_159_;
v_isShared_223_ = v_isSharedCheck_240_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_v_220_);
lean_dec(v_x_159_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_240_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___y_225_; lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_236_ = lean_unsigned_to_nat(1024u);
v___x_237_ = lean_nat_dec_le(v___x_236_, v_prec_160_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; 
v___x_238_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__3, &l_Lean_instReprDataValue_repr___closed__3_once, _init_l_Lean_instReprDataValue_repr___closed__3);
v___y_225_ = v___x_238_;
goto v___jp_224_;
}
else
{
lean_object* v___x_239_; 
v___x_239_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__4, &l_Lean_instReprDataValue_repr___closed__4_once, _init_l_Lean_instReprDataValue_repr___closed__4);
v___y_225_ = v___x_239_;
goto v___jp_224_;
}
v___jp_224_:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_226_ = ((lean_object*)(l_Lean_instReprDataValue_repr___closed__13));
v___x_227_ = l_Nat_reprFast(v_v_220_);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 0, v___x_227_);
v___x_229_ = v___x_222_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_227_);
v___x_229_ = v_reuseFailAlloc_235_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_226_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_231_, 0, v___y_225_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
v___x_232_ = 0;
v___x_233_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_233_, 0, v___x_231_);
lean_ctor_set_uint8(v___x_233_, sizeof(void*)*1, v___x_232_);
v___x_234_ = l_Repr_addAppParen(v___x_233_, v_prec_160_);
return v___x_234_;
}
}
}
}
case 4:
{
lean_object* v_v_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_264_; 
v_v_241_ = lean_ctor_get(v_x_159_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v_x_159_);
if (v_isSharedCheck_264_ == 0)
{
v___x_243_ = v_x_159_;
v_isShared_244_ = v_isSharedCheck_264_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_v_241_);
lean_dec(v_x_159_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_264_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___y_246_; lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_260_ = lean_unsigned_to_nat(1024u);
v___x_261_ = lean_nat_dec_le(v___x_260_, v_prec_160_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; 
v___x_262_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__3, &l_Lean_instReprDataValue_repr___closed__3_once, _init_l_Lean_instReprDataValue_repr___closed__3);
v___y_246_ = v___x_262_;
goto v___jp_245_;
}
else
{
lean_object* v___x_263_; 
v___x_263_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__4, &l_Lean_instReprDataValue_repr___closed__4_once, _init_l_Lean_instReprDataValue_repr___closed__4);
v___y_246_ = v___x_263_;
goto v___jp_245_;
}
v___jp_245_:
{
lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_247_ = ((lean_object*)(l_Lean_instReprDataValue_repr___closed__16));
v___x_248_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__17, &l_Lean_instReprDataValue_repr___closed__17_once, _init_l_Lean_instReprDataValue_repr___closed__17);
v___x_249_ = lean_int_dec_lt(v_v_241_, v___x_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; lean_object* v___x_252_; 
v___x_250_ = l_Int_repr(v_v_241_);
lean_dec(v_v_241_);
if (v_isShared_244_ == 0)
{
lean_ctor_set_tag(v___x_243_, 3);
lean_ctor_set(v___x_243_, 0, v___x_250_);
v___x_252_ = v___x_243_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_250_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
v___y_162_ = v___x_247_;
v___y_163_ = v___y_246_;
v___y_164_ = v___x_252_;
goto v___jp_161_;
}
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_257_; 
v___x_254_ = lean_unsigned_to_nat(1024u);
v___x_255_ = l_Int_repr(v_v_241_);
lean_dec(v_v_241_);
if (v_isShared_244_ == 0)
{
lean_ctor_set_tag(v___x_243_, 3);
lean_ctor_set(v___x_243_, 0, v___x_255_);
v___x_257_ = v___x_243_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_255_);
v___x_257_ = v_reuseFailAlloc_259_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_258_; 
v___x_258_ = l_Repr_addAppParen(v___x_257_, v___x_254_);
v___y_162_ = v___x_247_;
v___y_163_ = v___y_246_;
v___y_164_ = v___x_258_;
goto v___jp_161_;
}
}
}
}
}
default: 
{
lean_object* v_v_265_; lean_object* v___y_267_; lean_object* v___x_276_; uint8_t v___x_277_; 
v_v_265_ = lean_ctor_get(v_x_159_, 0);
lean_inc(v_v_265_);
lean_dec_ref(v_x_159_);
v___x_276_ = lean_unsigned_to_nat(1024u);
v___x_277_ = lean_nat_dec_le(v___x_276_, v_prec_160_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; 
v___x_278_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__3, &l_Lean_instReprDataValue_repr___closed__3_once, _init_l_Lean_instReprDataValue_repr___closed__3);
v___y_267_ = v___x_278_;
goto v___jp_266_;
}
else
{
lean_object* v___x_279_; 
v___x_279_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__4, &l_Lean_instReprDataValue_repr___closed__4_once, _init_l_Lean_instReprDataValue_repr___closed__4);
v___y_267_ = v___x_279_;
goto v___jp_266_;
}
v___jp_266_:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_268_ = ((lean_object*)(l_Lean_instReprDataValue_repr___closed__20));
v___x_269_ = lean_unsigned_to_nat(1024u);
v___x_270_ = l_Lean_Syntax_instRepr_repr(v_v_265_, v___x_269_);
v___x_271_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_268_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
v___x_272_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_272_, 0, v___y_267_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
v___x_273_ = 0;
v___x_274_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_274_, 0, v___x_272_);
lean_ctor_set_uint8(v___x_274_, sizeof(void*)*1, v___x_273_);
v___x_275_ = l_Repr_addAppParen(v___x_274_, v_prec_160_);
return v___x_275_;
}
}
}
v___jp_161_:
{
lean_object* v___x_165_; lean_object* v___x_166_; uint8_t v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_165_, 0, v___y_162_);
lean_ctor_set(v___x_165_, 1, v___y_164_);
v___x_166_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_166_, 0, v___y_163_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
v___x_167_ = 0;
v___x_168_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_168_, 0, v___x_166_);
lean_ctor_set_uint8(v___x_168_, sizeof(void*)*1, v___x_167_);
v___x_169_ = l_Repr_addAppParen(v___x_168_, v_prec_160_);
return v___x_169_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprDataValue_repr___boxed(lean_object* v_x_280_, lean_object* v_prec_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_instReprDataValue_repr(v_x_280_, v_prec_281_);
lean_dec(v_prec_281_);
return v_res_282_;
}
}
LEAN_EXPORT uint8_t lean_data_value_beq(lean_object* v_a_285_, lean_object* v_b_286_){
_start:
{
uint8_t v___x_287_; 
v___x_287_ = l_Lean_instBEqDataValue_beq(v_a_285_, v_b_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_beqExp___boxed(lean_object* v_a_288_, lean_object* v_b_289_){
_start:
{
uint8_t v_res_290_; lean_object* v_r_291_; 
v_res_290_ = lean_data_value_beq(v_a_288_, v_b_289_);
v_r_291_ = lean_box(v_res_290_);
return v_r_291_;
}
}
LEAN_EXPORT lean_object* lean_mk_bool_data_value(uint8_t v_b_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_293_, 0, v_b_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBoolDataValueEx___boxed(lean_object* v_b_294_){
_start:
{
uint8_t v_b_boxed_295_; lean_object* v_res_296_; 
v_b_boxed_295_ = lean_unbox(v_b_294_);
v_res_296_ = lean_mk_bool_data_value(v_b_boxed_295_);
return v_res_296_;
}
}
LEAN_EXPORT uint8_t lean_data_value_bool(lean_object* v_x_297_){
_start:
{
if (lean_obj_tag(v_x_297_) == 1)
{
uint8_t v_v_298_; 
v_v_298_ = lean_ctor_get_uint8(v_x_297_, 0);
lean_dec_ref(v_x_297_);
return v_v_298_;
}
else
{
uint8_t v___x_299_; 
lean_dec_ref(v_x_297_);
v___x_299_ = 0;
return v___x_299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_getBoolEx___boxed(lean_object* v_x_300_){
_start:
{
uint8_t v_res_301_; lean_object* v_r_302_; 
v_res_301_ = lean_data_value_bool(v_x_300_);
v_r_302_ = lean_box(v_res_301_);
return v_r_302_;
}
}
LEAN_EXPORT uint8_t l_Lean_DataValue_sameCtor(lean_object* v_x_303_, lean_object* v_x_304_){
_start:
{
switch(lean_obj_tag(v_x_303_))
{
case 0:
{
if (lean_obj_tag(v_x_304_) == 0)
{
uint8_t v___x_305_; 
v___x_305_ = 1;
return v___x_305_;
}
else
{
uint8_t v___x_306_; 
v___x_306_ = 0;
return v___x_306_;
}
}
case 1:
{
if (lean_obj_tag(v_x_304_) == 1)
{
uint8_t v___x_307_; 
v___x_307_ = 1;
return v___x_307_;
}
else
{
uint8_t v___x_308_; 
v___x_308_ = 0;
return v___x_308_;
}
}
case 2:
{
if (lean_obj_tag(v_x_304_) == 2)
{
uint8_t v___x_309_; 
v___x_309_ = 1;
return v___x_309_;
}
else
{
uint8_t v___x_310_; 
v___x_310_ = 0;
return v___x_310_;
}
}
case 3:
{
if (lean_obj_tag(v_x_304_) == 3)
{
uint8_t v___x_311_; 
v___x_311_ = 1;
return v___x_311_;
}
else
{
uint8_t v___x_312_; 
v___x_312_ = 0;
return v___x_312_;
}
}
case 4:
{
if (lean_obj_tag(v_x_304_) == 4)
{
uint8_t v___x_313_; 
v___x_313_ = 1;
return v___x_313_;
}
else
{
uint8_t v___x_314_; 
v___x_314_ = 0;
return v___x_314_;
}
}
default: 
{
if (lean_obj_tag(v_x_304_) == 5)
{
uint8_t v___x_315_; 
v___x_315_ = 1;
return v___x_315_;
}
else
{
uint8_t v___x_316_; 
v___x_316_ = 0;
return v___x_316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_sameCtor___boxed(lean_object* v_x_317_, lean_object* v_x_318_){
_start:
{
uint8_t v_res_319_; lean_object* v_r_320_; 
v_res_319_ = l_Lean_DataValue_sameCtor(v_x_317_, v_x_318_);
lean_dec_ref(v_x_318_);
lean_dec_ref(v_x_317_);
v_r_320_ = lean_box(v_res_319_);
return v_r_320_;
}
}
LEAN_EXPORT lean_object* lean_data_value_to_string(lean_object* v_x_324_){
_start:
{
switch(lean_obj_tag(v_x_324_))
{
case 0:
{
lean_object* v_v_325_; 
v_v_325_ = lean_ctor_get(v_x_324_, 0);
lean_inc_ref(v_v_325_);
lean_dec_ref(v_x_324_);
return v_v_325_;
}
case 1:
{
uint8_t v_v_326_; 
v_v_326_ = lean_ctor_get_uint8(v_x_324_, 0);
lean_dec_ref(v_x_324_);
if (v_v_326_ == 0)
{
lean_object* v___x_327_; 
v___x_327_ = ((lean_object*)(l_Lean_DataValue_str___closed__0));
return v___x_327_;
}
else
{
lean_object* v___x_328_; 
v___x_328_ = ((lean_object*)(l_Lean_DataValue_str___closed__1));
return v___x_328_;
}
}
case 2:
{
lean_object* v_v_329_; uint8_t v___x_330_; lean_object* v___x_331_; 
v_v_329_ = lean_ctor_get(v_x_324_, 0);
lean_inc(v_v_329_);
lean_dec_ref(v_x_324_);
v___x_330_ = 1;
v___x_331_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_329_, v___x_330_);
return v___x_331_;
}
case 3:
{
lean_object* v_v_332_; lean_object* v___x_333_; 
v_v_332_ = lean_ctor_get(v_x_324_, 0);
lean_inc(v_v_332_);
lean_dec_ref(v_x_324_);
v___x_333_ = l_Nat_reprFast(v_v_332_);
return v___x_333_;
}
case 4:
{
lean_object* v_v_334_; lean_object* v_intZero_335_; uint8_t v_isNeg_336_; 
v_v_334_ = lean_ctor_get(v_x_324_, 0);
lean_inc(v_v_334_);
lean_dec_ref(v_x_324_);
v_intZero_335_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__17, &l_Lean_instReprDataValue_repr___closed__17_once, _init_l_Lean_instReprDataValue_repr___closed__17);
v_isNeg_336_ = lean_int_dec_lt(v_v_334_, v_intZero_335_);
if (v_isNeg_336_ == 0)
{
lean_object* v_a_337_; lean_object* v___x_338_; 
v_a_337_ = lean_nat_abs(v_v_334_);
lean_dec(v_v_334_);
v___x_338_ = l_Nat_reprFast(v_a_337_);
return v___x_338_;
}
else
{
lean_object* v_abs_339_; lean_object* v_one_340_; lean_object* v_a_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v_abs_339_ = lean_nat_abs(v_v_334_);
lean_dec(v_v_334_);
v_one_340_ = lean_unsigned_to_nat(1u);
v_a_341_ = lean_nat_sub(v_abs_339_, v_one_340_);
lean_dec(v_abs_339_);
v___x_342_ = ((lean_object*)(l_Lean_DataValue_str___closed__2));
v___x_343_ = lean_nat_add(v_a_341_, v_one_340_);
lean_dec(v_a_341_);
v___x_344_ = l_Nat_reprFast(v___x_343_);
v___x_345_ = lean_string_append(v___x_342_, v___x_344_);
lean_dec_ref(v___x_344_);
return v___x_345_;
}
}
default: 
{
lean_object* v_v_346_; lean_object* v___x_347_; uint8_t v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v_v_346_ = lean_ctor_get(v_x_324_, 0);
lean_inc(v_v_346_);
lean_dec_ref(v_x_324_);
v___x_347_ = lean_box(0);
v___x_348_ = 0;
v___x_349_ = l_Lean_Syntax_formatStx(v_v_346_, v___x_347_, v___x_348_);
v___x_350_ = l_Std_Format_defWidth;
v___x_351_ = lean_unsigned_to_nat(0u);
v___x_352_ = l_Std_Format_pretty(v___x_349_, v___x_350_, v___x_351_, v___x_351_);
return v___x_352_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeStringDataValue___lam__0(lean_object* v_v_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_356_, 0, v_v_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeBoolDataValue___lam__0(uint8_t v_v_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_360_, 0, v_v_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeBoolDataValue___lam__0___boxed(lean_object* v_v_361_){
_start:
{
uint8_t v_v_boxed_362_; lean_object* v_res_363_; 
v_v_boxed_362_ = lean_unbox(v_v_361_);
v_res_363_ = l_Lean_instCoeBoolDataValue___lam__0(v_v_boxed_362_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeNameDataValue___lam__0(lean_object* v_v_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_367_, 0, v_v_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeNatDataValue___lam__0(lean_object* v_v_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_371_, 0, v_v_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeIntDataValue___lam__0(lean_object* v_v_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_375_, 0, v_v_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeSyntaxDataValue___lam__0(lean_object* v_v_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_379_, 0, v_v_378_);
return v___x_379_;
}
}
static lean_object* _init_l_Lean_instInhabitedKVMap_default(void){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = lean_box(0);
return v___x_382_;
}
}
static lean_object* _init_l_Lean_instInhabitedKVMap(void){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = lean_box(0);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprKVMap_repr_spec__1(lean_object* v_a_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = lean_nat_to_int(v_a_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_386_, lean_object* v_x_387_, lean_object* v_x_388_){
_start:
{
if (lean_obj_tag(v_x_388_) == 0)
{
lean_dec(v_x_386_);
return v_x_387_;
}
else
{
lean_object* v_head_389_; lean_object* v_tail_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_399_; 
v_head_389_ = lean_ctor_get(v_x_388_, 0);
v_tail_390_ = lean_ctor_get(v_x_388_, 1);
v_isSharedCheck_399_ = !lean_is_exclusive(v_x_388_);
if (v_isSharedCheck_399_ == 0)
{
v___x_392_ = v_x_388_;
v_isShared_393_ = v_isSharedCheck_399_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_tail_390_);
lean_inc(v_head_389_);
lean_dec(v_x_388_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_399_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
lean_inc(v_x_386_);
if (v_isShared_393_ == 0)
{
lean_ctor_set_tag(v___x_392_, 5);
lean_ctor_set(v___x_392_, 1, v_x_386_);
lean_ctor_set(v___x_392_, 0, v_x_387_);
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_x_387_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_x_386_);
v___x_395_ = v_reuseFailAlloc_398_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
lean_object* v___x_396_; 
v___x_396_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
lean_ctor_set(v___x_396_, 1, v_head_389_);
v_x_387_ = v___x_396_;
v_x_388_ = v_tail_390_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0_spec__2(lean_object* v_x_400_, lean_object* v_x_401_){
_start:
{
if (lean_obj_tag(v_x_400_) == 0)
{
lean_object* v___x_402_; 
lean_dec(v_x_401_);
v___x_402_ = lean_box(0);
return v___x_402_;
}
else
{
lean_object* v_tail_403_; 
v_tail_403_ = lean_ctor_get(v_x_400_, 1);
if (lean_obj_tag(v_tail_403_) == 0)
{
lean_object* v_head_404_; 
lean_dec(v_x_401_);
v_head_404_ = lean_ctor_get(v_x_400_, 0);
lean_inc(v_head_404_);
lean_dec_ref(v_x_400_);
return v_head_404_;
}
else
{
lean_object* v_head_405_; lean_object* v___x_406_; 
lean_inc(v_tail_403_);
v_head_405_ = lean_ctor_get(v_x_400_, 0);
lean_inc(v_head_405_);
lean_dec_ref(v_x_400_);
v___x_406_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0_spec__2_spec__3(v_x_401_, v_head_405_, v_tail_403_);
return v___x_406_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__0));
v___x_416_ = lean_string_length(v___x_415_);
return v___x_416_;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__5, &l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__5_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__5);
v___x_418_ = lean_nat_to_int(v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(lean_object* v_x_423_){
_start:
{
lean_object* v_fst_424_; lean_object* v_snd_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_448_; 
v_fst_424_ = lean_ctor_get(v_x_423_, 0);
v_snd_425_ = lean_ctor_get(v_x_423_, 1);
v_isSharedCheck_448_ = !lean_is_exclusive(v_x_423_);
if (v_isSharedCheck_448_ == 0)
{
v___x_427_ = v_x_423_;
v_isShared_428_ = v_isSharedCheck_448_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_snd_425_);
lean_inc(v_fst_424_);
lean_dec(v_x_423_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_448_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_429_ = lean_unsigned_to_nat(0u);
v___x_430_ = l_Lean_Name_reprPrec(v_fst_424_, v___x_429_);
v___x_431_ = lean_box(0);
if (v_isShared_428_ == 0)
{
lean_ctor_set_tag(v___x_427_, 1);
lean_ctor_set(v___x_427_, 1, v___x_431_);
lean_ctor_set(v___x_427_, 0, v___x_430_);
v___x_433_ = v___x_427_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v___x_431_);
v___x_433_ = v_reuseFailAlloc_447_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; uint8_t v___x_445_; lean_object* v___x_446_; 
v___x_434_ = l_Lean_instReprDataValue_repr(v_snd_425_, v___x_429_);
v___x_435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
lean_ctor_set(v___x_435_, 1, v___x_433_);
v___x_436_ = l_List_reverse___redArg(v___x_435_);
v___x_437_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__3));
v___x_438_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0_spec__2(v___x_436_, v___x_437_);
v___x_439_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__6, &l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__6_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__6);
v___x_440_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__7));
v___x_441_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
lean_ctor_set(v___x_441_, 1, v___x_438_);
v___x_442_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__8));
v___x_443_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_443_, 0, v___x_441_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v___x_444_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_439_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
v___x_445_ = 0;
v___x_446_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_446_, 0, v___x_444_);
lean_ctor_set_uint8(v___x_446_, sizeof(void*)*1, v___x_445_);
return v___x_446_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1_spec__4_spec__6(lean_object* v_x_449_, lean_object* v_x_450_, lean_object* v_x_451_){
_start:
{
if (lean_obj_tag(v_x_451_) == 0)
{
lean_dec(v_x_449_);
return v_x_450_;
}
else
{
lean_object* v_head_452_; lean_object* v_tail_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_463_; 
v_head_452_ = lean_ctor_get(v_x_451_, 0);
v_tail_453_ = lean_ctor_get(v_x_451_, 1);
v_isSharedCheck_463_ = !lean_is_exclusive(v_x_451_);
if (v_isSharedCheck_463_ == 0)
{
v___x_455_ = v_x_451_;
v_isShared_456_ = v_isSharedCheck_463_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_tail_453_);
lean_inc(v_head_452_);
lean_dec(v_x_451_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_463_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
lean_inc(v_x_449_);
if (v_isShared_456_ == 0)
{
lean_ctor_set_tag(v___x_455_, 5);
lean_ctor_set(v___x_455_, 1, v_x_449_);
lean_ctor_set(v___x_455_, 0, v_x_450_);
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_x_450_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v_x_449_);
v___x_458_ = v_reuseFailAlloc_462_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(v_head_452_);
v___x_460_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_458_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
v_x_450_ = v___x_460_;
v_x_451_ = v_tail_453_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1_spec__4(lean_object* v_x_464_, lean_object* v_x_465_, lean_object* v_x_466_){
_start:
{
if (lean_obj_tag(v_x_466_) == 0)
{
lean_dec(v_x_464_);
return v_x_465_;
}
else
{
lean_object* v_head_467_; lean_object* v_tail_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_478_; 
v_head_467_ = lean_ctor_get(v_x_466_, 0);
v_tail_468_ = lean_ctor_get(v_x_466_, 1);
v_isSharedCheck_478_ = !lean_is_exclusive(v_x_466_);
if (v_isSharedCheck_478_ == 0)
{
v___x_470_ = v_x_466_;
v_isShared_471_ = v_isSharedCheck_478_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_tail_468_);
lean_inc(v_head_467_);
lean_dec(v_x_466_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_478_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
lean_inc(v_x_464_);
if (v_isShared_471_ == 0)
{
lean_ctor_set_tag(v___x_470_, 5);
lean_ctor_set(v___x_470_, 1, v_x_464_);
lean_ctor_set(v___x_470_, 0, v_x_465_);
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_x_465_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_x_464_);
v___x_473_ = v_reuseFailAlloc_477_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_474_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(v_head_467_);
v___x_475_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_473_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
v___x_476_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1_spec__4_spec__6(v_x_464_, v___x_475_, v_tail_468_);
return v___x_476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1(lean_object* v_x_479_, lean_object* v_x_480_){
_start:
{
if (lean_obj_tag(v_x_479_) == 0)
{
lean_object* v___x_481_; 
lean_dec(v_x_480_);
v___x_481_ = lean_box(0);
return v___x_481_;
}
else
{
lean_object* v_tail_482_; 
v_tail_482_ = lean_ctor_get(v_x_479_, 1);
if (lean_obj_tag(v_tail_482_) == 0)
{
lean_object* v_head_483_; lean_object* v___x_484_; 
lean_dec(v_x_480_);
v_head_483_ = lean_ctor_get(v_x_479_, 0);
lean_inc(v_head_483_);
lean_dec_ref(v_x_479_);
v___x_484_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(v_head_483_);
return v___x_484_;
}
else
{
lean_object* v_head_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
lean_inc(v_tail_482_);
v_head_485_ = lean_ctor_get(v_x_479_, 0);
lean_inc(v_head_485_);
lean_dec_ref(v_x_479_);
v___x_486_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(v_head_485_);
v___x_487_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1_spec__4(v_x_480_, v___x_486_, v_tail_482_);
return v___x_487_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = ((lean_object*)(l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__2));
v___x_494_ = lean_string_length(v___x_493_);
return v___x_494_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_obj_once(&l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__4, &l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__4_once, _init_l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__4);
v___x_496_ = lean_nat_to_int(v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg(lean_object* v_a_501_){
_start:
{
if (lean_obj_tag(v_a_501_) == 0)
{
lean_object* v___x_502_; 
v___x_502_ = ((lean_object*)(l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__1));
return v___x_502_;
}
else
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; uint8_t v___x_511_; lean_object* v___x_512_; 
v___x_503_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__3));
v___x_504_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1(v_a_501_, v___x_503_);
v___x_505_ = lean_obj_once(&l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__5, &l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__5_once, _init_l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__5);
v___x_506_ = ((lean_object*)(l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__6));
v___x_507_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
lean_ctor_set(v___x_507_, 1, v___x_504_);
v___x_508_ = ((lean_object*)(l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__7));
v___x_509_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_507_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
v___x_510_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_505_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
v___x_511_ = 0;
v___x_512_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_512_, 0, v___x_510_);
lean_ctor_set_uint8(v___x_512_, sizeof(void*)*1, v___x_511_);
return v___x_512_;
}
}
}
static lean_object* _init_l_Lean_instReprKVMap_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_unsigned_to_nat(11u);
v___x_527_ = lean_nat_to_int(v___x_526_);
return v___x_527_;
}
}
static lean_object* _init_l_Lean_instReprKVMap_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = ((lean_object*)(l_Lean_instReprKVMap_repr___redArg___closed__0));
v___x_530_ = lean_string_length(v___x_529_);
return v___x_530_;
}
}
static lean_object* _init_l_Lean_instReprKVMap_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = lean_obj_once(&l_Lean_instReprKVMap_repr___redArg___closed__9, &l_Lean_instReprKVMap_repr___redArg___closed__9_once, _init_l_Lean_instReprKVMap_repr___redArg___closed__9);
v___x_532_ = lean_nat_to_int(v___x_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprKVMap_repr___redArg(lean_object* v_x_537_){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_538_ = ((lean_object*)(l_Lean_instReprKVMap_repr___redArg___closed__6));
v___x_539_ = lean_obj_once(&l_Lean_instReprKVMap_repr___redArg___closed__7, &l_Lean_instReprKVMap_repr___redArg___closed__7_once, _init_l_Lean_instReprKVMap_repr___redArg___closed__7);
v___x_540_ = l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg(v_x_537_);
v___x_541_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_539_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = 0;
v___x_543_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_543_, 0, v___x_541_);
lean_ctor_set_uint8(v___x_543_, sizeof(void*)*1, v___x_542_);
v___x_544_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_538_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
v___x_545_ = lean_obj_once(&l_Lean_instReprKVMap_repr___redArg___closed__10, &l_Lean_instReprKVMap_repr___redArg___closed__10_once, _init_l_Lean_instReprKVMap_repr___redArg___closed__10);
v___x_546_ = ((lean_object*)(l_Lean_instReprKVMap_repr___redArg___closed__11));
v___x_547_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
lean_ctor_set(v___x_547_, 1, v___x_544_);
v___x_548_ = ((lean_object*)(l_Lean_instReprKVMap_repr___redArg___closed__12));
v___x_549_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_547_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
v___x_550_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_545_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
v___x_551_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_551_, 0, v___x_550_);
lean_ctor_set_uint8(v___x_551_, sizeof(void*)*1, v___x_542_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprKVMap_repr(lean_object* v_x_552_, lean_object* v_prec_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Lean_instReprKVMap_repr___redArg(v_x_552_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprKVMap_repr___boxed(lean_object* v_x_555_, lean_object* v_prec_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_instReprKVMap_repr(v_x_555_, v_prec_556_);
lean_dec(v_prec_556_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprKVMap_repr_spec__0(lean_object* v_a_558_, lean_object* v_n_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg(v_a_558_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___boxed(lean_object* v_a_561_, lean_object* v_n_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_List_repr___at___00Lean_instReprKVMap_repr_spec__0(v_a_561_, v_n_562_);
lean_dec(v_n_562_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0(lean_object* v_x_564_, lean_object* v_x_565_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(v_x_564_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___boxed(lean_object* v_x_567_, lean_object* v_x_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0(v_x_567_, v_x_568_);
lean_dec(v_x_568_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instToString___lam__0(lean_object* v___f_572_, lean_object* v_m_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_List_toString___redArg(v___f_572_, v_m_573_);
return v___x_574_;
}
}
static lean_object* _init_l_Lean_KVMap_empty(void){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = lean_box(0);
return v___x_582_;
}
}
LEAN_EXPORT uint8_t l_Lean_KVMap_isEmpty(lean_object* v_x_583_){
_start:
{
uint8_t v___x_584_; 
v___x_584_ = l_List_isEmpty___redArg(v_x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_isEmpty___boxed(lean_object* v_x_585_){
_start:
{
uint8_t v_res_586_; lean_object* v_r_587_; 
v_res_586_ = l_Lean_KVMap_isEmpty(v_x_585_);
lean_dec(v_x_585_);
v_r_587_ = lean_box(v_res_586_);
return v_r_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_size(lean_object* v_m_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_List_lengthTR___redArg(v_m_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_size___boxed(lean_object* v_m_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_KVMap_size(v_m_590_);
lean_dec(v_m_590_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_findCore(lean_object* v_x_592_, lean_object* v_x_593_){
_start:
{
if (lean_obj_tag(v_x_592_) == 0)
{
lean_object* v___x_594_; 
v___x_594_ = lean_box(0);
return v___x_594_;
}
else
{
lean_object* v_head_595_; lean_object* v_tail_596_; lean_object* v_fst_597_; lean_object* v_snd_598_; uint8_t v___x_599_; 
v_head_595_ = lean_ctor_get(v_x_592_, 0);
v_tail_596_ = lean_ctor_get(v_x_592_, 1);
v_fst_597_ = lean_ctor_get(v_head_595_, 0);
v_snd_598_ = lean_ctor_get(v_head_595_, 1);
v___x_599_ = lean_name_eq(v_fst_597_, v_x_593_);
if (v___x_599_ == 0)
{
v_x_592_ = v_tail_596_;
goto _start;
}
else
{
lean_object* v___x_601_; 
lean_inc(v_snd_598_);
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v_snd_598_);
return v___x_601_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_findCore___boxed(lean_object* v_x_602_, lean_object* v_x_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Lean_KVMap_findCore(v_x_602_, v_x_603_);
lean_dec(v_x_603_);
lean_dec(v_x_602_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_find(lean_object* v_x_605_, lean_object* v_x_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_KVMap_findCore(v_x_605_, v_x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_find___boxed(lean_object* v_x_608_, lean_object* v_x_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lean_KVMap_find(v_x_608_, v_x_609_);
lean_dec(v_x_609_);
lean_dec(v_x_608_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_findD(lean_object* v_m_611_, lean_object* v_k_612_, lean_object* v_d_u2080_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_KVMap_findCore(v_m_611_, v_k_612_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_inc_ref(v_d_u2080_613_);
return v_d_u2080_613_;
}
else
{
lean_object* v_val_615_; 
v_val_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_val_615_);
lean_dec_ref(v___x_614_);
return v_val_615_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_findD___boxed(lean_object* v_m_616_, lean_object* v_k_617_, lean_object* v_d_u2080_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Lean_KVMap_findD(v_m_616_, v_k_617_, v_d_u2080_618_);
lean_dec_ref(v_d_u2080_618_);
lean_dec(v_k_617_);
lean_dec(v_m_616_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_insertCore(lean_object* v_x_620_, lean_object* v_x_621_, lean_object* v_x_622_){
_start:
{
if (lean_obj_tag(v_x_620_) == 0)
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_623_, 0, v_x_621_);
lean_ctor_set(v___x_623_, 1, v_x_622_);
v___x_624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
lean_ctor_set(v___x_624_, 1, v_x_620_);
return v___x_624_;
}
else
{
lean_object* v_head_625_; lean_object* v_tail_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_648_; 
v_head_625_ = lean_ctor_get(v_x_620_, 0);
v_tail_626_ = lean_ctor_get(v_x_620_, 1);
v_isSharedCheck_648_ = !lean_is_exclusive(v_x_620_);
if (v_isSharedCheck_648_ == 0)
{
v___x_628_ = v_x_620_;
v_isShared_629_ = v_isSharedCheck_648_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_tail_626_);
lean_inc(v_head_625_);
lean_dec(v_x_620_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_648_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v_fst_630_; uint8_t v___x_631_; 
v_fst_630_ = lean_ctor_get(v_head_625_, 0);
v___x_631_ = lean_name_eq(v_fst_630_, v_x_621_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; lean_object* v___x_634_; 
v___x_632_ = l_Lean_KVMap_insertCore(v_tail_626_, v_x_621_, v_x_622_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 1, v___x_632_);
v___x_634_ = v___x_628_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_head_625_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v___x_632_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
else
{
lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_645_; 
lean_inc(v_fst_630_);
lean_dec(v_x_621_);
v_isSharedCheck_645_ = !lean_is_exclusive(v_head_625_);
if (v_isSharedCheck_645_ == 0)
{
lean_object* v_unused_646_; lean_object* v_unused_647_; 
v_unused_646_ = lean_ctor_get(v_head_625_, 1);
lean_dec(v_unused_646_);
v_unused_647_ = lean_ctor_get(v_head_625_, 0);
lean_dec(v_unused_647_);
v___x_637_ = v_head_625_;
v_isShared_638_ = v_isSharedCheck_645_;
goto v_resetjp_636_;
}
else
{
lean_dec(v_head_625_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_645_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 1, v_x_622_);
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_fst_630_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_x_622_);
v___x_640_ = v_reuseFailAlloc_644_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_642_; 
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 0, v___x_640_);
v___x_642_ = v___x_628_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_640_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_tail_626_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_insert(lean_object* v_x_649_, lean_object* v_x_650_, lean_object* v_x_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Lean_KVMap_insertCore(v_x_649_, v_x_650_, v_x_651_);
return v___x_652_;
}
}
LEAN_EXPORT uint8_t l_Lean_KVMap_contains(lean_object* v_m_653_, lean_object* v_n_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_KVMap_findCore(v_m_653_, v_n_654_);
if (lean_obj_tag(v___x_655_) == 0)
{
uint8_t v___x_656_; 
v___x_656_ = 0;
return v___x_656_;
}
else
{
uint8_t v___x_657_; 
lean_dec_ref(v___x_655_);
v___x_657_ = 1;
return v___x_657_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_contains___boxed(lean_object* v_m_658_, lean_object* v_n_659_){
_start:
{
uint8_t v_res_660_; lean_object* v_r_661_; 
v_res_660_ = l_Lean_KVMap_contains(v_m_658_, v_n_659_);
lean_dec(v_n_659_);
lean_dec(v_m_658_);
v_r_661_ = lean_box(v_res_660_);
return v_r_661_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_KVMap_erase_spec__0(lean_object* v_x_662_, lean_object* v_a_663_, lean_object* v_a_664_){
_start:
{
if (lean_obj_tag(v_a_663_) == 0)
{
lean_object* v___x_665_; 
v___x_665_ = l_List_reverse___redArg(v_a_664_);
return v___x_665_;
}
else
{
lean_object* v_head_666_; lean_object* v_tail_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_678_; 
v_head_666_ = lean_ctor_get(v_a_663_, 0);
v_tail_667_ = lean_ctor_get(v_a_663_, 1);
v_isSharedCheck_678_ = !lean_is_exclusive(v_a_663_);
if (v_isSharedCheck_678_ == 0)
{
v___x_669_ = v_a_663_;
v_isShared_670_ = v_isSharedCheck_678_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_tail_667_);
lean_inc(v_head_666_);
lean_dec(v_a_663_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_678_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v_fst_671_; uint8_t v___x_672_; 
v_fst_671_ = lean_ctor_get(v_head_666_, 0);
v___x_672_ = lean_name_eq(v_fst_671_, v_x_662_);
if (v___x_672_ == 0)
{
lean_object* v___x_674_; 
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 1, v_a_664_);
v___x_674_ = v___x_669_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_head_666_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v_a_664_);
v___x_674_ = v_reuseFailAlloc_676_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
v_a_663_ = v_tail_667_;
v_a_664_ = v___x_674_;
goto _start;
}
}
else
{
lean_del_object(v___x_669_);
lean_dec(v_head_666_);
v_a_663_ = v_tail_667_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_KVMap_erase_spec__0___boxed(lean_object* v_x_679_, lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_List_filterTR_loop___at___00Lean_KVMap_erase_spec__0(v_x_679_, v_a_680_, v_a_681_);
lean_dec(v_x_679_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_erase(lean_object* v_x_683_, lean_object* v_x_684_){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = lean_box(0);
v___x_686_ = l_List_filterTR_loop___at___00Lean_KVMap_erase_spec__0(v_x_684_, v_x_683_, v___x_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_erase___boxed(lean_object* v_x_687_, lean_object* v_x_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_KVMap_erase(v_x_687_, v_x_688_);
lean_dec(v_x_688_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getString(lean_object* v_m_690_, lean_object* v_k_691_, lean_object* v_defVal_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Lean_KVMap_findCore(v_m_690_, v_k_691_);
if (lean_obj_tag(v___x_693_) == 1)
{
lean_object* v_val_694_; 
v_val_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_val_694_);
lean_dec_ref(v___x_693_);
if (lean_obj_tag(v_val_694_) == 0)
{
lean_object* v_v_695_; 
v_v_695_ = lean_ctor_get(v_val_694_, 0);
lean_inc_ref(v_v_695_);
lean_dec_ref(v_val_694_);
return v_v_695_;
}
else
{
lean_dec(v_val_694_);
lean_inc_ref(v_defVal_692_);
return v_defVal_692_;
}
}
else
{
lean_dec(v___x_693_);
lean_inc_ref(v_defVal_692_);
return v_defVal_692_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getString___boxed(lean_object* v_m_696_, lean_object* v_k_697_, lean_object* v_defVal_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lean_KVMap_getString(v_m_696_, v_k_697_, v_defVal_698_);
lean_dec_ref(v_defVal_698_);
lean_dec(v_k_697_);
lean_dec(v_m_696_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getNat(lean_object* v_m_700_, lean_object* v_k_701_, lean_object* v_defVal_702_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l_Lean_KVMap_findCore(v_m_700_, v_k_701_);
if (lean_obj_tag(v___x_703_) == 1)
{
lean_object* v_val_704_; 
v_val_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_val_704_);
lean_dec_ref(v___x_703_);
if (lean_obj_tag(v_val_704_) == 3)
{
lean_object* v_v_705_; 
v_v_705_ = lean_ctor_get(v_val_704_, 0);
lean_inc(v_v_705_);
lean_dec_ref(v_val_704_);
return v_v_705_;
}
else
{
lean_dec(v_val_704_);
lean_inc(v_defVal_702_);
return v_defVal_702_;
}
}
else
{
lean_dec(v___x_703_);
lean_inc(v_defVal_702_);
return v_defVal_702_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getNat___boxed(lean_object* v_m_706_, lean_object* v_k_707_, lean_object* v_defVal_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_KVMap_getNat(v_m_706_, v_k_707_, v_defVal_708_);
lean_dec(v_defVal_708_);
lean_dec(v_k_707_);
lean_dec(v_m_706_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getInt(lean_object* v_m_710_, lean_object* v_k_711_, lean_object* v_defVal_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Lean_KVMap_findCore(v_m_710_, v_k_711_);
if (lean_obj_tag(v___x_713_) == 1)
{
lean_object* v_val_714_; 
v_val_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_val_714_);
lean_dec_ref(v___x_713_);
if (lean_obj_tag(v_val_714_) == 4)
{
lean_object* v_v_715_; 
v_v_715_ = lean_ctor_get(v_val_714_, 0);
lean_inc(v_v_715_);
lean_dec_ref(v_val_714_);
return v_v_715_;
}
else
{
lean_dec(v_val_714_);
lean_inc(v_defVal_712_);
return v_defVal_712_;
}
}
else
{
lean_dec(v___x_713_);
lean_inc(v_defVal_712_);
return v_defVal_712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getInt___boxed(lean_object* v_m_716_, lean_object* v_k_717_, lean_object* v_defVal_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_KVMap_getInt(v_m_716_, v_k_717_, v_defVal_718_);
lean_dec(v_defVal_718_);
lean_dec(v_k_717_);
lean_dec(v_m_716_);
return v_res_719_;
}
}
LEAN_EXPORT uint8_t l_Lean_KVMap_getBool(lean_object* v_m_720_, lean_object* v_k_721_, uint8_t v_defVal_722_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l_Lean_KVMap_findCore(v_m_720_, v_k_721_);
if (lean_obj_tag(v___x_723_) == 1)
{
lean_object* v_val_724_; 
v_val_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_val_724_);
lean_dec_ref(v___x_723_);
if (lean_obj_tag(v_val_724_) == 1)
{
uint8_t v_v_725_; 
v_v_725_ = lean_ctor_get_uint8(v_val_724_, 0);
lean_dec_ref(v_val_724_);
return v_v_725_;
}
else
{
lean_dec(v_val_724_);
return v_defVal_722_;
}
}
else
{
lean_dec(v___x_723_);
return v_defVal_722_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getBool___boxed(lean_object* v_m_726_, lean_object* v_k_727_, lean_object* v_defVal_728_){
_start:
{
uint8_t v_defVal_boxed_729_; uint8_t v_res_730_; lean_object* v_r_731_; 
v_defVal_boxed_729_ = lean_unbox(v_defVal_728_);
v_res_730_ = l_Lean_KVMap_getBool(v_m_726_, v_k_727_, v_defVal_boxed_729_);
lean_dec(v_k_727_);
lean_dec(v_m_726_);
v_r_731_ = lean_box(v_res_730_);
return v_r_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getName(lean_object* v_m_732_, lean_object* v_k_733_, lean_object* v_defVal_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_KVMap_findCore(v_m_732_, v_k_733_);
if (lean_obj_tag(v___x_735_) == 1)
{
lean_object* v_val_736_; 
v_val_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_val_736_);
lean_dec_ref(v___x_735_);
if (lean_obj_tag(v_val_736_) == 2)
{
lean_object* v_v_737_; 
v_v_737_ = lean_ctor_get(v_val_736_, 0);
lean_inc(v_v_737_);
lean_dec_ref(v_val_736_);
return v_v_737_;
}
else
{
lean_dec(v_val_736_);
lean_inc(v_defVal_734_);
return v_defVal_734_;
}
}
else
{
lean_dec(v___x_735_);
lean_inc(v_defVal_734_);
return v_defVal_734_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getName___boxed(lean_object* v_m_738_, lean_object* v_k_739_, lean_object* v_defVal_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_KVMap_getName(v_m_738_, v_k_739_, v_defVal_740_);
lean_dec(v_defVal_740_);
lean_dec(v_k_739_);
lean_dec(v_m_738_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getSyntax(lean_object* v_m_742_, lean_object* v_k_743_, lean_object* v_defVal_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_Lean_KVMap_findCore(v_m_742_, v_k_743_);
if (lean_obj_tag(v___x_745_) == 1)
{
lean_object* v_val_746_; 
v_val_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_val_746_);
lean_dec_ref(v___x_745_);
if (lean_obj_tag(v_val_746_) == 5)
{
lean_object* v_v_747_; 
v_v_747_ = lean_ctor_get(v_val_746_, 0);
lean_inc(v_v_747_);
lean_dec_ref(v_val_746_);
return v_v_747_;
}
else
{
lean_dec(v_val_746_);
lean_inc(v_defVal_744_);
return v_defVal_744_;
}
}
else
{
lean_dec(v___x_745_);
lean_inc(v_defVal_744_);
return v_defVal_744_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getSyntax___boxed(lean_object* v_m_748_, lean_object* v_k_749_, lean_object* v_defVal_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_KVMap_getSyntax(v_m_748_, v_k_749_, v_defVal_750_);
lean_dec(v_defVal_750_);
lean_dec(v_k_749_);
lean_dec(v_m_748_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_setString(lean_object* v_m_752_, lean_object* v_k_753_, lean_object* v_v_754_){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_755_, 0, v_v_754_);
v___x_756_ = l_Lean_KVMap_insertCore(v_m_752_, v_k_753_, v___x_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_setNat(lean_object* v_m_757_, lean_object* v_k_758_, lean_object* v_v_759_){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_760_, 0, v_v_759_);
v___x_761_ = l_Lean_KVMap_insertCore(v_m_757_, v_k_758_, v___x_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_setInt(lean_object* v_m_762_, lean_object* v_k_763_, lean_object* v_v_764_){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_765_, 0, v_v_764_);
v___x_766_ = l_Lean_KVMap_insertCore(v_m_762_, v_k_763_, v___x_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_setBool(lean_object* v_m_767_, lean_object* v_k_768_, uint8_t v_v_769_){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_770_, 0, v_v_769_);
v___x_771_ = l_Lean_KVMap_insertCore(v_m_767_, v_k_768_, v___x_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_setBool___boxed(lean_object* v_m_772_, lean_object* v_k_773_, lean_object* v_v_774_){
_start:
{
uint8_t v_v_boxed_775_; lean_object* v_res_776_; 
v_v_boxed_775_ = lean_unbox(v_v_774_);
v_res_776_ = l_Lean_KVMap_setBool(v_m_772_, v_k_773_, v_v_boxed_775_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_setName(lean_object* v_m_777_, lean_object* v_k_778_, lean_object* v_v_779_){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_780_, 0, v_v_779_);
v___x_781_ = l_Lean_KVMap_insertCore(v_m_777_, v_k_778_, v___x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_setSyntax(lean_object* v_m_782_, lean_object* v_k_783_, lean_object* v_v_784_){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_785_, 0, v_v_784_);
v___x_786_ = l_Lean_KVMap_insertCore(v_m_782_, v_k_783_, v___x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_updateString(lean_object* v_m_787_, lean_object* v_k_788_, lean_object* v_f_789_){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_790_ = ((lean_object*)(l_Lean_instInhabitedDataValue_default___closed__0));
v___x_791_ = l_Lean_KVMap_getString(v_m_787_, v_k_788_, v___x_790_);
v___x_792_ = lean_apply_1(v_f_789_, v___x_791_);
v___x_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
v___x_794_ = l_Lean_KVMap_insertCore(v_m_787_, v_k_788_, v___x_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_updateNat(lean_object* v_m_795_, lean_object* v_k_796_, lean_object* v_f_797_){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_798_ = lean_unsigned_to_nat(0u);
v___x_799_ = l_Lean_KVMap_getNat(v_m_795_, v_k_796_, v___x_798_);
v___x_800_ = lean_apply_1(v_f_797_, v___x_799_);
v___x_801_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
v___x_802_ = l_Lean_KVMap_insertCore(v_m_795_, v_k_796_, v___x_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_updateInt(lean_object* v_m_803_, lean_object* v_k_804_, lean_object* v_f_805_){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_806_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__17, &l_Lean_instReprDataValue_repr___closed__17_once, _init_l_Lean_instReprDataValue_repr___closed__17);
v___x_807_ = l_Lean_KVMap_getInt(v_m_803_, v_k_804_, v___x_806_);
v___x_808_ = lean_apply_1(v_f_805_, v___x_807_);
v___x_809_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
v___x_810_ = l_Lean_KVMap_insertCore(v_m_803_, v_k_804_, v___x_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_updateBool(lean_object* v_m_811_, lean_object* v_k_812_, lean_object* v_f_813_){
_start:
{
uint8_t v___x_814_; uint8_t v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; uint8_t v___x_819_; lean_object* v___x_820_; 
v___x_814_ = 0;
v___x_815_ = l_Lean_KVMap_getBool(v_m_811_, v_k_812_, v___x_814_);
v___x_816_ = lean_box(v___x_815_);
v___x_817_ = lean_apply_1(v_f_813_, v___x_816_);
v___x_818_ = lean_alloc_ctor(1, 0, 1);
v___x_819_ = lean_unbox(v___x_817_);
lean_ctor_set_uint8(v___x_818_, 0, v___x_819_);
v___x_820_ = l_Lean_KVMap_insertCore(v_m_811_, v_k_812_, v___x_818_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_updateName(lean_object* v_m_821_, lean_object* v_k_822_, lean_object* v_f_823_){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_824_ = lean_box(0);
v___x_825_ = l_Lean_KVMap_getName(v_m_821_, v_k_822_, v___x_824_);
v___x_826_ = lean_apply_1(v_f_823_, v___x_825_);
v___x_827_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
v___x_828_ = l_Lean_KVMap_insertCore(v_m_821_, v_k_822_, v___x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_updateSyntax(lean_object* v_m_829_, lean_object* v_k_830_, lean_object* v_f_831_){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_832_ = lean_box(0);
v___x_833_ = l_Lean_KVMap_getSyntax(v_m_829_, v_k_830_, v___x_832_);
v___x_834_ = lean_apply_1(v_f_831_, v___x_833_);
v___x_835_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
v___x_836_ = l_Lean_KVMap_insertCore(v_m_829_, v_k_830_, v___x_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_forIn___redArg___lam__0(lean_object* v_f_837_, lean_object* v_a_838_, lean_object* v_x_839_, lean_object* v___y_840_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = lean_apply_2(v_f_837_, v_a_838_, v___y_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_forIn___redArg(lean_object* v_inst_842_, lean_object* v_kv_843_, lean_object* v_init_844_, lean_object* v_f_845_){
_start:
{
lean_object* v___f_846_; lean_object* v___x_847_; 
v___f_846_ = lean_alloc_closure((void*)(l_Lean_KVMap_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_846_, 0, v_f_845_);
v___x_847_ = l_List_forIn_x27_loop___redArg(v_inst_842_, v___f_846_, v_kv_843_, v_init_844_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_forIn(lean_object* v_00_u03b4_848_, lean_object* v_m_849_, lean_object* v_inst_850_, lean_object* v_kv_851_, lean_object* v_init_852_, lean_object* v_f_853_){
_start:
{
lean_object* v___f_854_; lean_object* v___x_855_; 
v___f_854_ = lean_alloc_closure((void*)(l_Lean_KVMap_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_854_, 0, v_f_853_);
v___x_855_ = l_List_forIn_x27_loop___redArg(v_inst_850_, v___f_854_, v_kv_851_, v_init_852_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__0(lean_object* v___y_856_, lean_object* v_a_857_, lean_object* v_x_858_, lean_object* v___y_859_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = lean_apply_2(v___y_856_, v_a_857_, v___y_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__1(lean_object* v_inst_861_, lean_object* v_00_u03b2_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v___f_866_; lean_object* v___x_867_; 
v___f_866_ = lean_alloc_closure((void*)(l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_866_, 0, v___y_865_);
v___x_867_ = l_List_forIn_x27_loop___redArg(v_inst_861_, v___f_866_, v___y_863_, v___y_864_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg(lean_object* v_inst_868_){
_start:
{
lean_object* v___f_869_; 
v___f_869_ = lean_alloc_closure((void*)(l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_869_, 0, v_inst_868_);
return v___f_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instForInProdNameDataValueOfMonad(lean_object* v_m_870_, lean_object* v_inst_871_){
_start:
{
lean_object* v___f_872_; 
v___f_872_ = lean_alloc_closure((void*)(l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_872_, 0, v_inst_871_);
return v___f_872_;
}
}
LEAN_EXPORT uint8_t l_Lean_KVMap_subsetAux(lean_object* v_x_873_, lean_object* v_x_874_){
_start:
{
if (lean_obj_tag(v_x_873_) == 0)
{
uint8_t v___x_875_; 
v___x_875_ = 1;
return v___x_875_;
}
else
{
lean_object* v_head_876_; lean_object* v_tail_877_; lean_object* v_fst_878_; lean_object* v_snd_879_; lean_object* v___x_880_; 
v_head_876_ = lean_ctor_get(v_x_873_, 0);
lean_inc(v_head_876_);
v_tail_877_ = lean_ctor_get(v_x_873_, 1);
lean_inc(v_tail_877_);
lean_dec_ref(v_x_873_);
v_fst_878_ = lean_ctor_get(v_head_876_, 0);
lean_inc(v_fst_878_);
v_snd_879_ = lean_ctor_get(v_head_876_, 1);
lean_inc(v_snd_879_);
lean_dec(v_head_876_);
v___x_880_ = l_Lean_KVMap_findCore(v_x_874_, v_fst_878_);
lean_dec(v_fst_878_);
if (lean_obj_tag(v___x_880_) == 0)
{
uint8_t v___x_881_; 
lean_dec(v_snd_879_);
lean_dec(v_tail_877_);
v___x_881_ = 0;
return v___x_881_;
}
else
{
lean_object* v_val_882_; uint8_t v___x_883_; 
v_val_882_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_val_882_);
lean_dec_ref(v___x_880_);
v___x_883_ = l_Lean_instBEqDataValue_beq(v_snd_879_, v_val_882_);
if (v___x_883_ == 0)
{
lean_dec(v_tail_877_);
return v___x_883_;
}
else
{
v_x_873_ = v_tail_877_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_subsetAux___boxed(lean_object* v_x_885_, lean_object* v_x_886_){
_start:
{
uint8_t v_res_887_; lean_object* v_r_888_; 
v_res_887_ = l_Lean_KVMap_subsetAux(v_x_885_, v_x_886_);
lean_dec(v_x_886_);
v_r_888_ = lean_box(v_res_887_);
return v_r_888_;
}
}
LEAN_EXPORT uint8_t l_Lean_KVMap_subset(lean_object* v_x_889_, lean_object* v_x_890_){
_start:
{
uint8_t v___x_891_; 
v___x_891_ = l_Lean_KVMap_subsetAux(v_x_889_, v_x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_subset___boxed(lean_object* v_x_892_, lean_object* v_x_893_){
_start:
{
uint8_t v_res_894_; lean_object* v_r_895_; 
v_res_894_ = l_Lean_KVMap_subset(v_x_892_, v_x_893_);
lean_dec(v_x_893_);
v_r_895_ = lean_box(v_res_894_);
return v_r_895_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___redArg(lean_object* v_mergeFn_896_, lean_object* v_as_x27_897_, lean_object* v_b_898_){
_start:
{
if (lean_obj_tag(v_as_x27_897_) == 0)
{
lean_dec_ref(v_mergeFn_896_);
return v_b_898_;
}
else
{
lean_object* v_head_899_; lean_object* v_tail_900_; lean_object* v_fst_901_; lean_object* v_snd_902_; lean_object* v___x_903_; 
v_head_899_ = lean_ctor_get(v_as_x27_897_, 0);
lean_inc(v_head_899_);
v_tail_900_ = lean_ctor_get(v_as_x27_897_, 1);
lean_inc(v_tail_900_);
lean_dec_ref(v_as_x27_897_);
v_fst_901_ = lean_ctor_get(v_head_899_, 0);
lean_inc(v_fst_901_);
v_snd_902_ = lean_ctor_get(v_head_899_, 1);
lean_inc(v_snd_902_);
lean_dec(v_head_899_);
v___x_903_ = l_Lean_KVMap_findCore(v_b_898_, v_fst_901_);
if (lean_obj_tag(v___x_903_) == 1)
{
lean_object* v_val_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v_val_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_val_904_);
lean_dec_ref(v___x_903_);
lean_inc_ref(v_mergeFn_896_);
lean_inc(v_fst_901_);
v___x_905_ = lean_apply_3(v_mergeFn_896_, v_fst_901_, v_val_904_, v_snd_902_);
v___x_906_ = l_Lean_KVMap_insertCore(v_b_898_, v_fst_901_, v___x_905_);
v_as_x27_897_ = v_tail_900_;
v_b_898_ = v___x_906_;
goto _start;
}
else
{
lean_object* v___x_908_; 
lean_dec(v___x_903_);
v___x_908_ = l_Lean_KVMap_insertCore(v_b_898_, v_fst_901_, v_snd_902_);
v_as_x27_897_ = v_tail_900_;
v_b_898_ = v___x_908_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_mergeBy(lean_object* v_mergeFn_910_, lean_object* v_l_911_, lean_object* v_r_912_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___redArg(v_mergeFn_910_, v_r_912_, v_l_911_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0(lean_object* v_mergeFn_914_, lean_object* v_as_915_, lean_object* v_as_x27_916_, lean_object* v_b_917_, lean_object* v_a_918_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___redArg(v_mergeFn_914_, v_as_x27_916_, v_b_917_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___boxed(lean_object* v_mergeFn_920_, lean_object* v_as_921_, lean_object* v_as_x27_922_, lean_object* v_b_923_, lean_object* v_a_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0(v_mergeFn_920_, v_as_921_, v_as_x27_922_, v_b_923_, v_a_924_);
lean_dec(v_as_921_);
return v_res_925_;
}
}
LEAN_EXPORT uint8_t l_Lean_KVMap_eqv(lean_object* v_m_u2081_926_, lean_object* v_m_u2082_927_){
_start:
{
uint8_t v___x_928_; 
lean_inc(v_m_u2081_926_);
v___x_928_ = l_Lean_KVMap_subsetAux(v_m_u2081_926_, v_m_u2082_927_);
if (v___x_928_ == 0)
{
lean_dec(v_m_u2082_927_);
lean_dec(v_m_u2081_926_);
return v___x_928_;
}
else
{
uint8_t v___x_929_; 
v___x_929_ = l_Lean_KVMap_subsetAux(v_m_u2082_927_, v_m_u2081_926_);
lean_dec(v_m_u2081_926_);
return v___x_929_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_eqv___boxed(lean_object* v_m_u2081_930_, lean_object* v_m_u2082_931_){
_start:
{
uint8_t v_res_932_; lean_object* v_r_933_; 
v_res_932_ = l_Lean_KVMap_eqv(v_m_u2081_930_, v_m_u2082_931_);
v_r_933_ = lean_box(v_res_932_);
return v_r_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_get_x3f___redArg(lean_object* v_inst_936_, lean_object* v_m_937_, lean_object* v_k_938_){
_start:
{
lean_object* v_ofDataValue_x3f_939_; lean_object* v___x_940_; 
v_ofDataValue_x3f_939_ = lean_ctor_get(v_inst_936_, 1);
lean_inc_ref(v_ofDataValue_x3f_939_);
lean_dec_ref(v_inst_936_);
v___x_940_ = l_Lean_KVMap_findCore(v_m_937_, v_k_938_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v___x_941_; 
lean_dec_ref(v_ofDataValue_x3f_939_);
v___x_941_ = lean_box(0);
return v___x_941_;
}
else
{
lean_object* v_val_942_; lean_object* v___x_943_; 
v_val_942_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_val_942_);
lean_dec_ref(v___x_940_);
v___x_943_ = lean_apply_1(v_ofDataValue_x3f_939_, v_val_942_);
return v___x_943_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_get_x3f___redArg___boxed(lean_object* v_inst_944_, lean_object* v_m_945_, lean_object* v_k_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lean_KVMap_get_x3f___redArg(v_inst_944_, v_m_945_, v_k_946_);
lean_dec(v_k_946_);
lean_dec(v_m_945_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_get_x3f(lean_object* v_00_u03b1_948_, lean_object* v_inst_949_, lean_object* v_m_950_, lean_object* v_k_951_){
_start:
{
lean_object* v_ofDataValue_x3f_952_; lean_object* v___x_953_; 
v_ofDataValue_x3f_952_ = lean_ctor_get(v_inst_949_, 1);
lean_inc_ref(v_ofDataValue_x3f_952_);
lean_dec_ref(v_inst_949_);
v___x_953_ = l_Lean_KVMap_findCore(v_m_950_, v_k_951_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v___x_954_; 
lean_dec_ref(v_ofDataValue_x3f_952_);
v___x_954_ = lean_box(0);
return v___x_954_;
}
else
{
lean_object* v_val_955_; lean_object* v___x_956_; 
v_val_955_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_val_955_);
lean_dec_ref(v___x_953_);
v___x_956_ = lean_apply_1(v_ofDataValue_x3f_952_, v_val_955_);
return v___x_956_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_get_x3f___boxed(lean_object* v_00_u03b1_957_, lean_object* v_inst_958_, lean_object* v_m_959_, lean_object* v_k_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Lean_KVMap_get_x3f(v_00_u03b1_957_, v_inst_958_, v_m_959_, v_k_960_);
lean_dec(v_k_960_);
lean_dec(v_m_959_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_get___redArg(lean_object* v_inst_962_, lean_object* v_m_963_, lean_object* v_k_964_, lean_object* v_defVal_965_){
_start:
{
lean_object* v_ofDataValue_x3f_966_; lean_object* v___x_967_; 
v_ofDataValue_x3f_966_ = lean_ctor_get(v_inst_962_, 1);
lean_inc_ref(v_ofDataValue_x3f_966_);
lean_dec_ref(v_inst_962_);
v___x_967_ = l_Lean_KVMap_findCore(v_m_963_, v_k_964_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_dec_ref(v_ofDataValue_x3f_966_);
lean_inc(v_defVal_965_);
return v_defVal_965_;
}
else
{
lean_object* v_val_968_; lean_object* v___x_969_; 
v_val_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_val_968_);
lean_dec_ref(v___x_967_);
v___x_969_ = lean_apply_1(v_ofDataValue_x3f_966_, v_val_968_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_inc(v_defVal_965_);
return v_defVal_965_;
}
else
{
lean_object* v_val_970_; 
v_val_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_val_970_);
lean_dec_ref(v___x_969_);
return v_val_970_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_get___redArg___boxed(lean_object* v_inst_971_, lean_object* v_m_972_, lean_object* v_k_973_, lean_object* v_defVal_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_KVMap_get___redArg(v_inst_971_, v_m_972_, v_k_973_, v_defVal_974_);
lean_dec(v_defVal_974_);
lean_dec(v_k_973_);
lean_dec(v_m_972_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_get(lean_object* v_00_u03b1_976_, lean_object* v_inst_977_, lean_object* v_m_978_, lean_object* v_k_979_, lean_object* v_defVal_980_){
_start:
{
lean_object* v_ofDataValue_x3f_981_; lean_object* v___x_982_; 
v_ofDataValue_x3f_981_ = lean_ctor_get(v_inst_977_, 1);
lean_inc_ref(v_ofDataValue_x3f_981_);
lean_dec_ref(v_inst_977_);
v___x_982_ = l_Lean_KVMap_findCore(v_m_978_, v_k_979_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_dec_ref(v_ofDataValue_x3f_981_);
lean_inc(v_defVal_980_);
return v_defVal_980_;
}
else
{
lean_object* v_val_983_; lean_object* v___x_984_; 
v_val_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_val_983_);
lean_dec_ref(v___x_982_);
v___x_984_ = lean_apply_1(v_ofDataValue_x3f_981_, v_val_983_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_inc(v_defVal_980_);
return v_defVal_980_;
}
else
{
lean_object* v_val_985_; 
v_val_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_val_985_);
lean_dec_ref(v___x_984_);
return v_val_985_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_get___boxed(lean_object* v_00_u03b1_986_, lean_object* v_inst_987_, lean_object* v_m_988_, lean_object* v_k_989_, lean_object* v_defVal_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lean_KVMap_get(v_00_u03b1_986_, v_inst_987_, v_m_988_, v_k_989_, v_defVal_990_);
lean_dec(v_defVal_990_);
lean_dec(v_k_989_);
lean_dec(v_m_988_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_set___redArg(lean_object* v_inst_992_, lean_object* v_m_993_, lean_object* v_k_994_, lean_object* v_v_995_){
_start:
{
lean_object* v_toDataValue_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v_toDataValue_996_ = lean_ctor_get(v_inst_992_, 0);
lean_inc_ref(v_toDataValue_996_);
lean_dec_ref(v_inst_992_);
v___x_997_ = lean_apply_1(v_toDataValue_996_, v_v_995_);
v___x_998_ = l_Lean_KVMap_insertCore(v_m_993_, v_k_994_, v___x_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_set(lean_object* v_00_u03b1_999_, lean_object* v_inst_1000_, lean_object* v_m_1001_, lean_object* v_k_1002_, lean_object* v_v_1003_){
_start:
{
lean_object* v_toDataValue_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v_toDataValue_1004_ = lean_ctor_get(v_inst_1000_, 0);
lean_inc_ref(v_toDataValue_1004_);
lean_dec_ref(v_inst_1000_);
v___x_1005_ = lean_apply_1(v_toDataValue_1004_, v_v_1003_);
v___x_1006_ = l_Lean_KVMap_insertCore(v_m_1001_, v_k_1002_, v___x_1005_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_update___redArg(lean_object* v_inst_1007_, lean_object* v_m_1008_, lean_object* v_k_1009_, lean_object* v_f_1010_){
_start:
{
lean_object* v_toDataValue_1011_; lean_object* v_ofDataValue_x3f_1012_; lean_object* v___y_1014_; lean_object* v___x_1020_; 
v_toDataValue_1011_ = lean_ctor_get(v_inst_1007_, 0);
lean_inc_ref(v_toDataValue_1011_);
v_ofDataValue_x3f_1012_ = lean_ctor_get(v_inst_1007_, 1);
lean_inc_ref(v_ofDataValue_x3f_1012_);
lean_dec_ref(v_inst_1007_);
v___x_1020_ = l_Lean_KVMap_findCore(v_m_1008_, v_k_1009_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v___x_1021_; 
lean_dec_ref(v_ofDataValue_x3f_1012_);
v___x_1021_ = lean_box(0);
v___y_1014_ = v___x_1021_;
goto v___jp_1013_;
}
else
{
lean_object* v_val_1022_; lean_object* v___x_1023_; 
v_val_1022_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_val_1022_);
lean_dec_ref(v___x_1020_);
v___x_1023_ = lean_apply_1(v_ofDataValue_x3f_1012_, v_val_1022_);
v___y_1014_ = v___x_1023_;
goto v___jp_1013_;
}
v___jp_1013_:
{
lean_object* v___x_1015_; 
v___x_1015_ = lean_apply_1(v_f_1010_, v___y_1014_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v___x_1016_; 
lean_dec_ref(v_toDataValue_1011_);
v___x_1016_ = l_Lean_KVMap_erase(v_m_1008_, v_k_1009_);
lean_dec(v_k_1009_);
return v___x_1016_;
}
else
{
lean_object* v_val_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v_val_1017_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_val_1017_);
lean_dec_ref(v___x_1015_);
v___x_1018_ = lean_apply_1(v_toDataValue_1011_, v_val_1017_);
v___x_1019_ = l_Lean_KVMap_insertCore(v_m_1008_, v_k_1009_, v___x_1018_);
return v___x_1019_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_update(lean_object* v_00_u03b1_1024_, lean_object* v_inst_1025_, lean_object* v_m_1026_, lean_object* v_k_1027_, lean_object* v_f_1028_){
_start:
{
lean_object* v_toDataValue_1029_; lean_object* v_ofDataValue_x3f_1030_; lean_object* v___y_1032_; lean_object* v___x_1038_; 
v_toDataValue_1029_ = lean_ctor_get(v_inst_1025_, 0);
lean_inc_ref(v_toDataValue_1029_);
v_ofDataValue_x3f_1030_ = lean_ctor_get(v_inst_1025_, 1);
lean_inc_ref(v_ofDataValue_x3f_1030_);
lean_dec_ref(v_inst_1025_);
v___x_1038_ = l_Lean_KVMap_findCore(v_m_1026_, v_k_1027_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v___x_1039_; 
lean_dec_ref(v_ofDataValue_x3f_1030_);
v___x_1039_ = lean_box(0);
v___y_1032_ = v___x_1039_;
goto v___jp_1031_;
}
else
{
lean_object* v_val_1040_; lean_object* v___x_1041_; 
v_val_1040_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_val_1040_);
lean_dec_ref(v___x_1038_);
v___x_1041_ = lean_apply_1(v_ofDataValue_x3f_1030_, v_val_1040_);
v___y_1032_ = v___x_1041_;
goto v___jp_1031_;
}
v___jp_1031_:
{
lean_object* v___x_1033_; 
v___x_1033_ = lean_apply_1(v_f_1028_, v___y_1032_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v___x_1034_; 
lean_dec_ref(v_toDataValue_1029_);
v___x_1034_ = l_Lean_KVMap_erase(v_m_1026_, v_k_1027_);
lean_dec(v_k_1027_);
return v___x_1034_;
}
else
{
lean_object* v_val_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v_val_1035_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_val_1035_);
lean_dec_ref(v___x_1033_);
v___x_1036_ = lean_apply_1(v_toDataValue_1029_, v_val_1035_);
v___x_1037_ = l_Lean_KVMap_insertCore(v_m_1026_, v_k_1027_, v___x_1036_);
return v___x_1037_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueDataValue___lam__0(lean_object* v_val_1042_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1043_, 0, v_val_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueBool___lam__1(lean_object* v_x_1050_){
_start:
{
if (lean_obj_tag(v_x_1050_) == 1)
{
uint8_t v_v_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v_v_1051_ = lean_ctor_get_uint8(v_x_1050_, 0);
v___x_1052_ = lean_box(v_v_1051_);
v___x_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
return v___x_1053_;
}
else
{
lean_object* v___x_1054_; 
v___x_1054_ = lean_box(0);
return v___x_1054_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueBool___lam__1___boxed(lean_object* v_x_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_KVMap_instValueBool___lam__1(v_x_1055_);
lean_dec_ref(v_x_1055_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueNat___lam__1(lean_object* v_x_1062_){
_start:
{
if (lean_obj_tag(v_x_1062_) == 3)
{
lean_object* v_v_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
v_v_1063_ = lean_ctor_get(v_x_1062_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_x_1062_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v_x_1062_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_v_1063_);
lean_dec(v_x_1062_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
lean_ctor_set_tag(v___x_1065_, 1);
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_v_1063_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
else
{
lean_object* v___x_1071_; 
lean_dec_ref(v_x_1062_);
v___x_1071_ = lean_box(0);
return v___x_1071_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueInt___lam__1(lean_object* v_x_1077_){
_start:
{
if (lean_obj_tag(v_x_1077_) == 4)
{
lean_object* v_v_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
v_v_1078_ = lean_ctor_get(v_x_1077_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_x_1077_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v_x_1077_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_v_1078_);
lean_dec(v_x_1077_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
lean_ctor_set_tag(v___x_1080_, 1);
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_v_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
else
{
lean_object* v___x_1086_; 
lean_dec_ref(v_x_1077_);
v___x_1086_ = lean_box(0);
return v___x_1086_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueName___lam__1(lean_object* v_x_1092_){
_start:
{
if (lean_obj_tag(v_x_1092_) == 2)
{
lean_object* v_v_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
v_v_1093_ = lean_ctor_get(v_x_1092_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_x_1092_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1095_ = v_x_1092_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_v_1093_);
lean_dec(v_x_1092_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
lean_ctor_set_tag(v___x_1095_, 1);
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_v_1093_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
else
{
lean_object* v___x_1101_; 
lean_dec_ref(v_x_1092_);
v___x_1101_ = lean_box(0);
return v___x_1101_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueString___lam__1(lean_object* v_x_1107_){
_start:
{
if (lean_obj_tag(v_x_1107_) == 0)
{
lean_object* v_v_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
v_v_1108_ = lean_ctor_get(v_x_1107_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_x_1107_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v_x_1107_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_v_1108_);
lean_dec(v_x_1107_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
lean_ctor_set_tag(v___x_1110_, 1);
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_v_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
else
{
lean_object* v___x_1116_; 
lean_dec_ref(v_x_1107_);
v___x_1116_ = lean_box(0);
return v___x_1116_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueSyntax___lam__1(lean_object* v_x_1122_){
_start:
{
if (lean_obj_tag(v_x_1122_) == 5)
{
lean_object* v_v_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
v_v_1123_ = lean_ctor_get(v_x_1122_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_x_1122_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v_x_1122_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_v_1123_);
lean_dec(v_x_1122_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
lean_ctor_set_tag(v___x_1125_, 1);
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_v_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
else
{
lean_object* v___x_1131_; 
lean_dec_ref(v_x_1122_);
v___x_1131_ = lean_box(0);
return v___x_1131_;
}
}
}
lean_object* runtime_initialize_Init_Data_Format_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Name(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Extra(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_KVMap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Format_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedKVMap_default = _init_l_Lean_instInhabitedKVMap_default();
lean_mark_persistent(l_Lean_instInhabitedKVMap_default);
l_Lean_instInhabitedKVMap = _init_l_Lean_instInhabitedKVMap();
lean_mark_persistent(l_Lean_instInhabitedKVMap);
l_Lean_KVMap_empty = _init_l_Lean_KVMap_empty();
lean_mark_persistent(l_Lean_KVMap_empty);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_KVMap(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Format_Syntax(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Name(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Extra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_KVMap(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Format_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_KVMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_KVMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_KVMap(builtin);
}
#ifdef __cplusplus
}
#endif

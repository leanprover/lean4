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
lean_object* l_Int_repr(lean_object*);
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
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
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
lean_inc(v___y_175_);
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
lean_inc(v___y_193_);
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
lean_inc(v___y_207_);
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
lean_inc(v___y_225_);
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
lean_inc(v___y_267_);
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
lean_inc(v___y_162_);
v___x_165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_165_, 0, v___y_162_);
lean_ctor_set(v___x_165_, 1, v___y_164_);
lean_inc(v___y_163_);
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
LEAN_EXPORT lean_object* lean_data_value_to_string(lean_object* v_x_323_){
_start:
{
switch(lean_obj_tag(v_x_323_))
{
case 0:
{
lean_object* v_v_324_; 
v_v_324_ = lean_ctor_get(v_x_323_, 0);
lean_inc_ref(v_v_324_);
lean_dec_ref(v_x_323_);
return v_v_324_;
}
case 1:
{
uint8_t v_v_325_; 
v_v_325_ = lean_ctor_get_uint8(v_x_323_, 0);
lean_dec_ref(v_x_323_);
if (v_v_325_ == 0)
{
lean_object* v___x_326_; 
v___x_326_ = ((lean_object*)(l_Lean_DataValue_str___closed__0));
return v___x_326_;
}
else
{
lean_object* v___x_327_; 
v___x_327_ = ((lean_object*)(l_Lean_DataValue_str___closed__1));
return v___x_327_;
}
}
case 2:
{
lean_object* v_v_328_; uint8_t v___x_329_; lean_object* v___x_330_; 
v_v_328_ = lean_ctor_get(v_x_323_, 0);
lean_inc(v_v_328_);
lean_dec_ref(v_x_323_);
v___x_329_ = 1;
v___x_330_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_328_, v___x_329_);
return v___x_330_;
}
case 3:
{
lean_object* v_v_331_; lean_object* v___x_332_; 
v_v_331_ = lean_ctor_get(v_x_323_, 0);
lean_inc(v_v_331_);
lean_dec_ref(v_x_323_);
v___x_332_ = l_Nat_reprFast(v_v_331_);
return v___x_332_;
}
case 4:
{
lean_object* v_v_333_; lean_object* v___x_334_; 
v_v_333_ = lean_ctor_get(v_x_323_, 0);
lean_inc(v_v_333_);
lean_dec_ref(v_x_323_);
v___x_334_ = l_Int_repr(v_v_333_);
lean_dec(v_v_333_);
return v___x_334_;
}
default: 
{
lean_object* v_v_335_; lean_object* v___x_336_; uint8_t v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v_v_335_ = lean_ctor_get(v_x_323_, 0);
lean_inc(v_v_335_);
lean_dec_ref(v_x_323_);
v___x_336_ = lean_box(0);
v___x_337_ = 0;
v___x_338_ = l_Lean_Syntax_formatStx(v_v_335_, v___x_336_, v___x_337_);
v___x_339_ = l_Std_Format_defWidth;
v___x_340_ = lean_unsigned_to_nat(0u);
v___x_341_ = l_Std_Format_pretty(v___x_338_, v___x_339_, v___x_340_, v___x_340_);
return v___x_341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeStringDataValue___lam__0(lean_object* v_v_344_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_345_, 0, v_v_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeBoolDataValue___lam__0(uint8_t v_v_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_349_, 0, v_v_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeBoolDataValue___lam__0___boxed(lean_object* v_v_350_){
_start:
{
uint8_t v_v_boxed_351_; lean_object* v_res_352_; 
v_v_boxed_351_ = lean_unbox(v_v_350_);
v_res_352_ = l_Lean_instCoeBoolDataValue___lam__0(v_v_boxed_351_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeNameDataValue___lam__0(lean_object* v_v_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_356_, 0, v_v_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeNatDataValue___lam__0(lean_object* v_v_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_360_, 0, v_v_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeIntDataValue___lam__0(lean_object* v_v_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_364_, 0, v_v_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeSyntaxDataValue___lam__0(lean_object* v_v_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_368_, 0, v_v_367_);
return v___x_368_;
}
}
static lean_object* _init_l_Lean_instInhabitedKVMap_default(void){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = lean_box(0);
return v___x_371_;
}
}
static lean_object* _init_l_Lean_instInhabitedKVMap(void){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = lean_box(0);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprKVMap_repr_spec__1(lean_object* v_a_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = lean_nat_to_int(v_a_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_375_, lean_object* v_x_376_, lean_object* v_x_377_){
_start:
{
if (lean_obj_tag(v_x_377_) == 0)
{
lean_dec(v_x_375_);
return v_x_376_;
}
else
{
lean_object* v_head_378_; lean_object* v_tail_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_388_; 
v_head_378_ = lean_ctor_get(v_x_377_, 0);
v_tail_379_ = lean_ctor_get(v_x_377_, 1);
v_isSharedCheck_388_ = !lean_is_exclusive(v_x_377_);
if (v_isSharedCheck_388_ == 0)
{
v___x_381_ = v_x_377_;
v_isShared_382_ = v_isSharedCheck_388_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_tail_379_);
lean_inc(v_head_378_);
lean_dec(v_x_377_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_388_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_384_; 
lean_inc(v_x_375_);
if (v_isShared_382_ == 0)
{
lean_ctor_set_tag(v___x_381_, 5);
lean_ctor_set(v___x_381_, 1, v_x_375_);
lean_ctor_set(v___x_381_, 0, v_x_376_);
v___x_384_ = v___x_381_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_x_376_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v_x_375_);
v___x_384_ = v_reuseFailAlloc_387_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
lean_object* v___x_385_; 
v___x_385_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
lean_ctor_set(v___x_385_, 1, v_head_378_);
v_x_376_ = v___x_385_;
v_x_377_ = v_tail_379_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0_spec__2(lean_object* v_x_389_, lean_object* v_x_390_){
_start:
{
if (lean_obj_tag(v_x_389_) == 0)
{
lean_object* v___x_391_; 
lean_dec(v_x_390_);
v___x_391_ = lean_box(0);
return v___x_391_;
}
else
{
lean_object* v_tail_392_; 
v_tail_392_ = lean_ctor_get(v_x_389_, 1);
if (lean_obj_tag(v_tail_392_) == 0)
{
lean_object* v_head_393_; 
lean_dec(v_x_390_);
v_head_393_ = lean_ctor_get(v_x_389_, 0);
lean_inc(v_head_393_);
lean_dec_ref(v_x_389_);
return v_head_393_;
}
else
{
lean_object* v_head_394_; lean_object* v___x_395_; 
lean_inc(v_tail_392_);
v_head_394_ = lean_ctor_get(v_x_389_, 0);
lean_inc(v_head_394_);
lean_dec_ref(v_x_389_);
v___x_395_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0_spec__2_spec__3(v_x_390_, v_head_394_, v_tail_392_);
return v___x_395_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__0));
v___x_405_ = lean_string_length(v___x_404_);
return v___x_405_;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__5, &l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__5_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__5);
v___x_407_ = lean_nat_to_int(v___x_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(lean_object* v_x_412_){
_start:
{
lean_object* v_fst_413_; lean_object* v_snd_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_437_; 
v_fst_413_ = lean_ctor_get(v_x_412_, 0);
v_snd_414_ = lean_ctor_get(v_x_412_, 1);
v_isSharedCheck_437_ = !lean_is_exclusive(v_x_412_);
if (v_isSharedCheck_437_ == 0)
{
v___x_416_ = v_x_412_;
v_isShared_417_ = v_isSharedCheck_437_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_snd_414_);
lean_inc(v_fst_413_);
lean_dec(v_x_412_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_437_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_422_; 
v___x_418_ = lean_unsigned_to_nat(0u);
v___x_419_ = l_Lean_Name_reprPrec(v_fst_413_, v___x_418_);
v___x_420_ = lean_box(0);
if (v_isShared_417_ == 0)
{
lean_ctor_set_tag(v___x_416_, 1);
lean_ctor_set(v___x_416_, 1, v___x_420_);
lean_ctor_set(v___x_416_, 0, v___x_419_);
v___x_422_ = v___x_416_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v___x_420_);
v___x_422_ = v_reuseFailAlloc_436_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; uint8_t v___x_434_; lean_object* v___x_435_; 
v___x_423_ = l_Lean_instReprDataValue_repr(v_snd_414_, v___x_418_);
v___x_424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
lean_ctor_set(v___x_424_, 1, v___x_422_);
v___x_425_ = l_List_reverse___redArg(v___x_424_);
v___x_426_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__3));
v___x_427_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0_spec__2(v___x_425_, v___x_426_);
v___x_428_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__6, &l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__6_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__6);
v___x_429_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__7));
v___x_430_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
lean_ctor_set(v___x_430_, 1, v___x_427_);
v___x_431_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__8));
v___x_432_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_430_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
v___x_433_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_428_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
v___x_434_ = 0;
v___x_435_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_435_, 0, v___x_433_);
lean_ctor_set_uint8(v___x_435_, sizeof(void*)*1, v___x_434_);
return v___x_435_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1_spec__4_spec__6(lean_object* v_x_438_, lean_object* v_x_439_, lean_object* v_x_440_){
_start:
{
if (lean_obj_tag(v_x_440_) == 0)
{
lean_dec(v_x_438_);
return v_x_439_;
}
else
{
lean_object* v_head_441_; lean_object* v_tail_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_452_; 
v_head_441_ = lean_ctor_get(v_x_440_, 0);
v_tail_442_ = lean_ctor_get(v_x_440_, 1);
v_isSharedCheck_452_ = !lean_is_exclusive(v_x_440_);
if (v_isSharedCheck_452_ == 0)
{
v___x_444_ = v_x_440_;
v_isShared_445_ = v_isSharedCheck_452_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_tail_442_);
lean_inc(v_head_441_);
lean_dec(v_x_440_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_452_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
lean_inc(v_x_438_);
if (v_isShared_445_ == 0)
{
lean_ctor_set_tag(v___x_444_, 5);
lean_ctor_set(v___x_444_, 1, v_x_438_);
lean_ctor_set(v___x_444_, 0, v_x_439_);
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_x_439_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_x_438_);
v___x_447_ = v_reuseFailAlloc_451_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(v_head_441_);
v___x_449_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_447_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
v_x_439_ = v___x_449_;
v_x_440_ = v_tail_442_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1_spec__4(lean_object* v_x_453_, lean_object* v_x_454_, lean_object* v_x_455_){
_start:
{
if (lean_obj_tag(v_x_455_) == 0)
{
lean_dec(v_x_453_);
return v_x_454_;
}
else
{
lean_object* v_head_456_; lean_object* v_tail_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_467_; 
v_head_456_ = lean_ctor_get(v_x_455_, 0);
v_tail_457_ = lean_ctor_get(v_x_455_, 1);
v_isSharedCheck_467_ = !lean_is_exclusive(v_x_455_);
if (v_isSharedCheck_467_ == 0)
{
v___x_459_ = v_x_455_;
v_isShared_460_ = v_isSharedCheck_467_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_tail_457_);
lean_inc(v_head_456_);
lean_dec(v_x_455_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_467_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
lean_inc(v_x_453_);
if (v_isShared_460_ == 0)
{
lean_ctor_set_tag(v___x_459_, 5);
lean_ctor_set(v___x_459_, 1, v_x_453_);
lean_ctor_set(v___x_459_, 0, v_x_454_);
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_x_454_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_x_453_);
v___x_462_ = v_reuseFailAlloc_466_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_463_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(v_head_456_);
v___x_464_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_462_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
v___x_465_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1_spec__4_spec__6(v_x_453_, v___x_464_, v_tail_457_);
return v___x_465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1(lean_object* v_x_468_, lean_object* v_x_469_){
_start:
{
if (lean_obj_tag(v_x_468_) == 0)
{
lean_object* v___x_470_; 
lean_dec(v_x_469_);
v___x_470_ = lean_box(0);
return v___x_470_;
}
else
{
lean_object* v_tail_471_; 
v_tail_471_ = lean_ctor_get(v_x_468_, 1);
if (lean_obj_tag(v_tail_471_) == 0)
{
lean_object* v_head_472_; lean_object* v___x_473_; 
lean_dec(v_x_469_);
v_head_472_ = lean_ctor_get(v_x_468_, 0);
lean_inc(v_head_472_);
lean_dec_ref(v_x_468_);
v___x_473_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(v_head_472_);
return v___x_473_;
}
else
{
lean_object* v_head_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
lean_inc(v_tail_471_);
v_head_474_ = lean_ctor_get(v_x_468_, 0);
lean_inc(v_head_474_);
lean_dec_ref(v_x_468_);
v___x_475_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(v_head_474_);
v___x_476_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1_spec__4(v_x_469_, v___x_475_, v_tail_471_);
return v___x_476_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = ((lean_object*)(l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__2));
v___x_483_ = lean_string_length(v___x_482_);
return v___x_483_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_obj_once(&l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__4, &l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__4_once, _init_l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__4);
v___x_485_ = lean_nat_to_int(v___x_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg(lean_object* v_a_490_){
_start:
{
if (lean_obj_tag(v_a_490_) == 0)
{
lean_object* v___x_491_; 
v___x_491_ = ((lean_object*)(l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__1));
return v___x_491_;
}
else
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; uint8_t v___x_500_; lean_object* v___x_501_; 
v___x_492_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__3));
v___x_493_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1(v_a_490_, v___x_492_);
v___x_494_ = lean_obj_once(&l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__5, &l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__5_once, _init_l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__5);
v___x_495_ = ((lean_object*)(l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__6));
v___x_496_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
lean_ctor_set(v___x_496_, 1, v___x_493_);
v___x_497_ = ((lean_object*)(l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__7));
v___x_498_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_496_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v___x_499_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_494_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
v___x_500_ = 0;
v___x_501_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_501_, 0, v___x_499_);
lean_ctor_set_uint8(v___x_501_, sizeof(void*)*1, v___x_500_);
return v___x_501_;
}
}
}
static lean_object* _init_l_Lean_instReprKVMap_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_unsigned_to_nat(11u);
v___x_516_ = lean_nat_to_int(v___x_515_);
return v___x_516_;
}
}
static lean_object* _init_l_Lean_instReprKVMap_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = ((lean_object*)(l_Lean_instReprKVMap_repr___redArg___closed__0));
v___x_519_ = lean_string_length(v___x_518_);
return v___x_519_;
}
}
static lean_object* _init_l_Lean_instReprKVMap_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = lean_obj_once(&l_Lean_instReprKVMap_repr___redArg___closed__9, &l_Lean_instReprKVMap_repr___redArg___closed__9_once, _init_l_Lean_instReprKVMap_repr___redArg___closed__9);
v___x_521_ = lean_nat_to_int(v___x_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprKVMap_repr___redArg(lean_object* v_x_526_){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; uint8_t v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_527_ = ((lean_object*)(l_Lean_instReprKVMap_repr___redArg___closed__6));
v___x_528_ = lean_obj_once(&l_Lean_instReprKVMap_repr___redArg___closed__7, &l_Lean_instReprKVMap_repr___redArg___closed__7_once, _init_l_Lean_instReprKVMap_repr___redArg___closed__7);
v___x_529_ = l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg(v_x_526_);
v___x_530_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_528_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = 0;
v___x_532_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_532_, 0, v___x_530_);
lean_ctor_set_uint8(v___x_532_, sizeof(void*)*1, v___x_531_);
v___x_533_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_527_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = lean_obj_once(&l_Lean_instReprKVMap_repr___redArg___closed__10, &l_Lean_instReprKVMap_repr___redArg___closed__10_once, _init_l_Lean_instReprKVMap_repr___redArg___closed__10);
v___x_535_ = ((lean_object*)(l_Lean_instReprKVMap_repr___redArg___closed__11));
v___x_536_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
lean_ctor_set(v___x_536_, 1, v___x_533_);
v___x_537_ = ((lean_object*)(l_Lean_instReprKVMap_repr___redArg___closed__12));
v___x_538_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_536_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
v___x_539_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_534_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_540_, 0, v___x_539_);
lean_ctor_set_uint8(v___x_540_, sizeof(void*)*1, v___x_531_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprKVMap_repr(lean_object* v_x_541_, lean_object* v_prec_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Lean_instReprKVMap_repr___redArg(v_x_541_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprKVMap_repr___boxed(lean_object* v_x_544_, lean_object* v_prec_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_instReprKVMap_repr(v_x_544_, v_prec_545_);
lean_dec(v_prec_545_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprKVMap_repr_spec__0(lean_object* v_a_547_, lean_object* v_n_548_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg(v_a_547_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___boxed(lean_object* v_a_550_, lean_object* v_n_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_List_repr___at___00Lean_instReprKVMap_repr_spec__0(v_a_550_, v_n_551_);
lean_dec(v_n_551_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0(lean_object* v_x_553_, lean_object* v_x_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(v_x_553_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___boxed(lean_object* v_x_556_, lean_object* v_x_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0(v_x_556_, v_x_557_);
lean_dec(v_x_557_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instToString___lam__0(lean_object* v___f_561_, lean_object* v_m_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_List_toString___redArg(v___f_561_, v_m_562_);
return v___x_563_;
}
}
static lean_object* _init_l_Lean_KVMap_empty(void){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = lean_box(0);
return v___x_571_;
}
}
LEAN_EXPORT uint8_t l_Lean_KVMap_isEmpty(lean_object* v_x_572_){
_start:
{
uint8_t v___x_573_; 
v___x_573_ = l_List_isEmpty___redArg(v_x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_isEmpty___boxed(lean_object* v_x_574_){
_start:
{
uint8_t v_res_575_; lean_object* v_r_576_; 
v_res_575_ = l_Lean_KVMap_isEmpty(v_x_574_);
lean_dec(v_x_574_);
v_r_576_ = lean_box(v_res_575_);
return v_r_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_size(lean_object* v_m_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_List_lengthTR___redArg(v_m_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_size___boxed(lean_object* v_m_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_KVMap_size(v_m_579_);
lean_dec(v_m_579_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_findCore(lean_object* v_x_581_, lean_object* v_x_582_){
_start:
{
if (lean_obj_tag(v_x_581_) == 0)
{
lean_object* v___x_583_; 
v___x_583_ = lean_box(0);
return v___x_583_;
}
else
{
lean_object* v_head_584_; lean_object* v_tail_585_; lean_object* v_fst_586_; lean_object* v_snd_587_; uint8_t v___x_588_; 
v_head_584_ = lean_ctor_get(v_x_581_, 0);
v_tail_585_ = lean_ctor_get(v_x_581_, 1);
v_fst_586_ = lean_ctor_get(v_head_584_, 0);
v_snd_587_ = lean_ctor_get(v_head_584_, 1);
v___x_588_ = lean_name_eq(v_fst_586_, v_x_582_);
if (v___x_588_ == 0)
{
v_x_581_ = v_tail_585_;
goto _start;
}
else
{
lean_object* v___x_590_; 
lean_inc(v_snd_587_);
v___x_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_590_, 0, v_snd_587_);
return v___x_590_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_findCore___boxed(lean_object* v_x_591_, lean_object* v_x_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_KVMap_findCore(v_x_591_, v_x_592_);
lean_dec(v_x_592_);
lean_dec(v_x_591_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_find(lean_object* v_x_594_, lean_object* v_x_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Lean_KVMap_findCore(v_x_594_, v_x_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_find___boxed(lean_object* v_x_597_, lean_object* v_x_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Lean_KVMap_find(v_x_597_, v_x_598_);
lean_dec(v_x_598_);
lean_dec(v_x_597_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_findD(lean_object* v_m_600_, lean_object* v_k_601_, lean_object* v_d_u2080_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_KVMap_findCore(v_m_600_, v_k_601_);
if (lean_obj_tag(v___x_603_) == 0)
{
lean_inc_ref(v_d_u2080_602_);
return v_d_u2080_602_;
}
else
{
lean_object* v_val_604_; 
v_val_604_ = lean_ctor_get(v___x_603_, 0);
lean_inc(v_val_604_);
lean_dec_ref(v___x_603_);
return v_val_604_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_findD___boxed(lean_object* v_m_605_, lean_object* v_k_606_, lean_object* v_d_u2080_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_KVMap_findD(v_m_605_, v_k_606_, v_d_u2080_607_);
lean_dec_ref(v_d_u2080_607_);
lean_dec(v_k_606_);
lean_dec(v_m_605_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_insertCore(lean_object* v_x_609_, lean_object* v_x_610_, lean_object* v_x_611_){
_start:
{
if (lean_obj_tag(v_x_609_) == 0)
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v_x_610_);
lean_ctor_set(v___x_612_, 1, v_x_611_);
v___x_613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
lean_ctor_set(v___x_613_, 1, v_x_609_);
return v___x_613_;
}
else
{
lean_object* v_head_614_; lean_object* v_tail_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_637_; 
v_head_614_ = lean_ctor_get(v_x_609_, 0);
v_tail_615_ = lean_ctor_get(v_x_609_, 1);
v_isSharedCheck_637_ = !lean_is_exclusive(v_x_609_);
if (v_isSharedCheck_637_ == 0)
{
v___x_617_ = v_x_609_;
v_isShared_618_ = v_isSharedCheck_637_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_tail_615_);
lean_inc(v_head_614_);
lean_dec(v_x_609_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_637_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v_fst_619_; uint8_t v___x_620_; 
v_fst_619_ = lean_ctor_get(v_head_614_, 0);
v___x_620_ = lean_name_eq(v_fst_619_, v_x_610_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_623_; 
v___x_621_ = l_Lean_KVMap_insertCore(v_tail_615_, v_x_610_, v_x_611_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 1, v___x_621_);
v___x_623_ = v___x_617_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_head_614_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v___x_621_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
else
{
lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_634_; 
lean_inc(v_fst_619_);
lean_dec(v_x_610_);
v_isSharedCheck_634_ = !lean_is_exclusive(v_head_614_);
if (v_isSharedCheck_634_ == 0)
{
lean_object* v_unused_635_; lean_object* v_unused_636_; 
v_unused_635_ = lean_ctor_get(v_head_614_, 1);
lean_dec(v_unused_635_);
v_unused_636_ = lean_ctor_get(v_head_614_, 0);
lean_dec(v_unused_636_);
v___x_626_ = v_head_614_;
v_isShared_627_ = v_isSharedCheck_634_;
goto v_resetjp_625_;
}
else
{
lean_dec(v_head_614_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_634_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 1, v_x_611_);
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_fst_619_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_x_611_);
v___x_629_ = v_reuseFailAlloc_633_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_631_; 
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v___x_629_);
v___x_631_ = v___x_617_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_tail_615_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_insert(lean_object* v_x_638_, lean_object* v_x_639_, lean_object* v_x_640_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Lean_KVMap_insertCore(v_x_638_, v_x_639_, v_x_640_);
return v___x_641_;
}
}
LEAN_EXPORT uint8_t l_Lean_KVMap_contains(lean_object* v_m_642_, lean_object* v_n_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Lean_KVMap_findCore(v_m_642_, v_n_643_);
if (lean_obj_tag(v___x_644_) == 0)
{
uint8_t v___x_645_; 
v___x_645_ = 0;
return v___x_645_;
}
else
{
uint8_t v___x_646_; 
lean_dec_ref(v___x_644_);
v___x_646_ = 1;
return v___x_646_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_contains___boxed(lean_object* v_m_647_, lean_object* v_n_648_){
_start:
{
uint8_t v_res_649_; lean_object* v_r_650_; 
v_res_649_ = l_Lean_KVMap_contains(v_m_647_, v_n_648_);
lean_dec(v_n_648_);
lean_dec(v_m_647_);
v_r_650_ = lean_box(v_res_649_);
return v_r_650_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_KVMap_erase_spec__0(lean_object* v_x_651_, lean_object* v_a_652_, lean_object* v_a_653_){
_start:
{
if (lean_obj_tag(v_a_652_) == 0)
{
lean_object* v___x_654_; 
v___x_654_ = l_List_reverse___redArg(v_a_653_);
return v___x_654_;
}
else
{
lean_object* v_head_655_; lean_object* v_tail_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_667_; 
v_head_655_ = lean_ctor_get(v_a_652_, 0);
v_tail_656_ = lean_ctor_get(v_a_652_, 1);
v_isSharedCheck_667_ = !lean_is_exclusive(v_a_652_);
if (v_isSharedCheck_667_ == 0)
{
v___x_658_ = v_a_652_;
v_isShared_659_ = v_isSharedCheck_667_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_tail_656_);
lean_inc(v_head_655_);
lean_dec(v_a_652_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_667_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v_fst_660_; uint8_t v___x_661_; 
v_fst_660_ = lean_ctor_get(v_head_655_, 0);
v___x_661_ = lean_name_eq(v_fst_660_, v_x_651_);
if (v___x_661_ == 0)
{
lean_object* v___x_663_; 
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 1, v_a_653_);
v___x_663_ = v___x_658_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_head_655_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v_a_653_);
v___x_663_ = v_reuseFailAlloc_665_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
v_a_652_ = v_tail_656_;
v_a_653_ = v___x_663_;
goto _start;
}
}
else
{
lean_del_object(v___x_658_);
lean_dec(v_head_655_);
v_a_652_ = v_tail_656_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_KVMap_erase_spec__0___boxed(lean_object* v_x_668_, lean_object* v_a_669_, lean_object* v_a_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_List_filterTR_loop___at___00Lean_KVMap_erase_spec__0(v_x_668_, v_a_669_, v_a_670_);
lean_dec(v_x_668_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_erase(lean_object* v_x_672_, lean_object* v_x_673_){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = lean_box(0);
v___x_675_ = l_List_filterTR_loop___at___00Lean_KVMap_erase_spec__0(v_x_673_, v_x_672_, v___x_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_erase___boxed(lean_object* v_x_676_, lean_object* v_x_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_KVMap_erase(v_x_676_, v_x_677_);
lean_dec(v_x_677_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getString(lean_object* v_m_679_, lean_object* v_k_680_, lean_object* v_defVal_681_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_Lean_KVMap_findCore(v_m_679_, v_k_680_);
if (lean_obj_tag(v___x_682_) == 1)
{
lean_object* v_val_683_; 
v_val_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc(v_val_683_);
lean_dec_ref(v___x_682_);
if (lean_obj_tag(v_val_683_) == 0)
{
lean_object* v_v_684_; 
v_v_684_ = lean_ctor_get(v_val_683_, 0);
lean_inc_ref(v_v_684_);
lean_dec_ref(v_val_683_);
return v_v_684_;
}
else
{
lean_dec(v_val_683_);
lean_inc_ref(v_defVal_681_);
return v_defVal_681_;
}
}
else
{
lean_dec(v___x_682_);
lean_inc_ref(v_defVal_681_);
return v_defVal_681_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getString___boxed(lean_object* v_m_685_, lean_object* v_k_686_, lean_object* v_defVal_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_KVMap_getString(v_m_685_, v_k_686_, v_defVal_687_);
lean_dec_ref(v_defVal_687_);
lean_dec(v_k_686_);
lean_dec(v_m_685_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getNat(lean_object* v_m_689_, lean_object* v_k_690_, lean_object* v_defVal_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Lean_KVMap_findCore(v_m_689_, v_k_690_);
if (lean_obj_tag(v___x_692_) == 1)
{
lean_object* v_val_693_; 
v_val_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_val_693_);
lean_dec_ref(v___x_692_);
if (lean_obj_tag(v_val_693_) == 3)
{
lean_object* v_v_694_; 
v_v_694_ = lean_ctor_get(v_val_693_, 0);
lean_inc(v_v_694_);
lean_dec_ref(v_val_693_);
return v_v_694_;
}
else
{
lean_dec(v_val_693_);
lean_inc(v_defVal_691_);
return v_defVal_691_;
}
}
else
{
lean_dec(v___x_692_);
lean_inc(v_defVal_691_);
return v_defVal_691_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getNat___boxed(lean_object* v_m_695_, lean_object* v_k_696_, lean_object* v_defVal_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Lean_KVMap_getNat(v_m_695_, v_k_696_, v_defVal_697_);
lean_dec(v_defVal_697_);
lean_dec(v_k_696_);
lean_dec(v_m_695_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getInt(lean_object* v_m_699_, lean_object* v_k_700_, lean_object* v_defVal_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Lean_KVMap_findCore(v_m_699_, v_k_700_);
if (lean_obj_tag(v___x_702_) == 1)
{
lean_object* v_val_703_; 
v_val_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_val_703_);
lean_dec_ref(v___x_702_);
if (lean_obj_tag(v_val_703_) == 4)
{
lean_object* v_v_704_; 
v_v_704_ = lean_ctor_get(v_val_703_, 0);
lean_inc(v_v_704_);
lean_dec_ref(v_val_703_);
return v_v_704_;
}
else
{
lean_dec(v_val_703_);
lean_inc(v_defVal_701_);
return v_defVal_701_;
}
}
else
{
lean_dec(v___x_702_);
lean_inc(v_defVal_701_);
return v_defVal_701_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getInt___boxed(lean_object* v_m_705_, lean_object* v_k_706_, lean_object* v_defVal_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_KVMap_getInt(v_m_705_, v_k_706_, v_defVal_707_);
lean_dec(v_defVal_707_);
lean_dec(v_k_706_);
lean_dec(v_m_705_);
return v_res_708_;
}
}
LEAN_EXPORT uint8_t l_Lean_KVMap_getBool(lean_object* v_m_709_, lean_object* v_k_710_, uint8_t v_defVal_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Lean_KVMap_findCore(v_m_709_, v_k_710_);
if (lean_obj_tag(v___x_712_) == 1)
{
lean_object* v_val_713_; 
v_val_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_val_713_);
lean_dec_ref(v___x_712_);
if (lean_obj_tag(v_val_713_) == 1)
{
uint8_t v_v_714_; 
v_v_714_ = lean_ctor_get_uint8(v_val_713_, 0);
lean_dec_ref(v_val_713_);
return v_v_714_;
}
else
{
lean_dec(v_val_713_);
return v_defVal_711_;
}
}
else
{
lean_dec(v___x_712_);
return v_defVal_711_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getBool___boxed(lean_object* v_m_715_, lean_object* v_k_716_, lean_object* v_defVal_717_){
_start:
{
uint8_t v_defVal_boxed_718_; uint8_t v_res_719_; lean_object* v_r_720_; 
v_defVal_boxed_718_ = lean_unbox(v_defVal_717_);
v_res_719_ = l_Lean_KVMap_getBool(v_m_715_, v_k_716_, v_defVal_boxed_718_);
lean_dec(v_k_716_);
lean_dec(v_m_715_);
v_r_720_ = lean_box(v_res_719_);
return v_r_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getName(lean_object* v_m_721_, lean_object* v_k_722_, lean_object* v_defVal_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Lean_KVMap_findCore(v_m_721_, v_k_722_);
if (lean_obj_tag(v___x_724_) == 1)
{
lean_object* v_val_725_; 
v_val_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc(v_val_725_);
lean_dec_ref(v___x_724_);
if (lean_obj_tag(v_val_725_) == 2)
{
lean_object* v_v_726_; 
v_v_726_ = lean_ctor_get(v_val_725_, 0);
lean_inc(v_v_726_);
lean_dec_ref(v_val_725_);
return v_v_726_;
}
else
{
lean_dec(v_val_725_);
lean_inc(v_defVal_723_);
return v_defVal_723_;
}
}
else
{
lean_dec(v___x_724_);
lean_inc(v_defVal_723_);
return v_defVal_723_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getName___boxed(lean_object* v_m_727_, lean_object* v_k_728_, lean_object* v_defVal_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_KVMap_getName(v_m_727_, v_k_728_, v_defVal_729_);
lean_dec(v_defVal_729_);
lean_dec(v_k_728_);
lean_dec(v_m_727_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getSyntax(lean_object* v_m_731_, lean_object* v_k_732_, lean_object* v_defVal_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_KVMap_findCore(v_m_731_, v_k_732_);
if (lean_obj_tag(v___x_734_) == 1)
{
lean_object* v_val_735_; 
v_val_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_val_735_);
lean_dec_ref(v___x_734_);
if (lean_obj_tag(v_val_735_) == 5)
{
lean_object* v_v_736_; 
v_v_736_ = lean_ctor_get(v_val_735_, 0);
lean_inc(v_v_736_);
lean_dec_ref(v_val_735_);
return v_v_736_;
}
else
{
lean_dec(v_val_735_);
lean_inc(v_defVal_733_);
return v_defVal_733_;
}
}
else
{
lean_dec(v___x_734_);
lean_inc(v_defVal_733_);
return v_defVal_733_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getSyntax___boxed(lean_object* v_m_737_, lean_object* v_k_738_, lean_object* v_defVal_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Lean_KVMap_getSyntax(v_m_737_, v_k_738_, v_defVal_739_);
lean_dec(v_defVal_739_);
lean_dec(v_k_738_);
lean_dec(v_m_737_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_setString(lean_object* v_m_741_, lean_object* v_k_742_, lean_object* v_v_743_){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_744_, 0, v_v_743_);
v___x_745_ = l_Lean_KVMap_insertCore(v_m_741_, v_k_742_, v___x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_setNat(lean_object* v_m_746_, lean_object* v_k_747_, lean_object* v_v_748_){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_749_, 0, v_v_748_);
v___x_750_ = l_Lean_KVMap_insertCore(v_m_746_, v_k_747_, v___x_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_setInt(lean_object* v_m_751_, lean_object* v_k_752_, lean_object* v_v_753_){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_754_, 0, v_v_753_);
v___x_755_ = l_Lean_KVMap_insertCore(v_m_751_, v_k_752_, v___x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_setBool(lean_object* v_m_756_, lean_object* v_k_757_, uint8_t v_v_758_){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_759_, 0, v_v_758_);
v___x_760_ = l_Lean_KVMap_insertCore(v_m_756_, v_k_757_, v___x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_setBool___boxed(lean_object* v_m_761_, lean_object* v_k_762_, lean_object* v_v_763_){
_start:
{
uint8_t v_v_boxed_764_; lean_object* v_res_765_; 
v_v_boxed_764_ = lean_unbox(v_v_763_);
v_res_765_ = l_Lean_KVMap_setBool(v_m_761_, v_k_762_, v_v_boxed_764_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_setName(lean_object* v_m_766_, lean_object* v_k_767_, lean_object* v_v_768_){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_769_, 0, v_v_768_);
v___x_770_ = l_Lean_KVMap_insertCore(v_m_766_, v_k_767_, v___x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_setSyntax(lean_object* v_m_771_, lean_object* v_k_772_, lean_object* v_v_773_){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_774_, 0, v_v_773_);
v___x_775_ = l_Lean_KVMap_insertCore(v_m_771_, v_k_772_, v___x_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_updateString(lean_object* v_m_776_, lean_object* v_k_777_, lean_object* v_f_778_){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_779_ = ((lean_object*)(l_Lean_instInhabitedDataValue_default___closed__0));
v___x_780_ = l_Lean_KVMap_getString(v_m_776_, v_k_777_, v___x_779_);
v___x_781_ = lean_apply_1(v_f_778_, v___x_780_);
v___x_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
v___x_783_ = l_Lean_KVMap_insertCore(v_m_776_, v_k_777_, v___x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_updateNat(lean_object* v_m_784_, lean_object* v_k_785_, lean_object* v_f_786_){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_787_ = lean_unsigned_to_nat(0u);
v___x_788_ = l_Lean_KVMap_getNat(v_m_784_, v_k_785_, v___x_787_);
v___x_789_ = lean_apply_1(v_f_786_, v___x_788_);
v___x_790_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
v___x_791_ = l_Lean_KVMap_insertCore(v_m_784_, v_k_785_, v___x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_updateInt(lean_object* v_m_792_, lean_object* v_k_793_, lean_object* v_f_794_){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_795_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__17, &l_Lean_instReprDataValue_repr___closed__17_once, _init_l_Lean_instReprDataValue_repr___closed__17);
v___x_796_ = l_Lean_KVMap_getInt(v_m_792_, v_k_793_, v___x_795_);
v___x_797_ = lean_apply_1(v_f_794_, v___x_796_);
v___x_798_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
v___x_799_ = l_Lean_KVMap_insertCore(v_m_792_, v_k_793_, v___x_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_updateBool(lean_object* v_m_800_, lean_object* v_k_801_, lean_object* v_f_802_){
_start:
{
uint8_t v___x_803_; uint8_t v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; uint8_t v___x_808_; lean_object* v___x_809_; 
v___x_803_ = 0;
v___x_804_ = l_Lean_KVMap_getBool(v_m_800_, v_k_801_, v___x_803_);
v___x_805_ = lean_box(v___x_804_);
v___x_806_ = lean_apply_1(v_f_802_, v___x_805_);
v___x_807_ = lean_alloc_ctor(1, 0, 1);
v___x_808_ = lean_unbox(v___x_806_);
lean_ctor_set_uint8(v___x_807_, 0, v___x_808_);
v___x_809_ = l_Lean_KVMap_insertCore(v_m_800_, v_k_801_, v___x_807_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_updateName(lean_object* v_m_810_, lean_object* v_k_811_, lean_object* v_f_812_){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_813_ = lean_box(0);
v___x_814_ = l_Lean_KVMap_getName(v_m_810_, v_k_811_, v___x_813_);
v___x_815_ = lean_apply_1(v_f_812_, v___x_814_);
v___x_816_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
v___x_817_ = l_Lean_KVMap_insertCore(v_m_810_, v_k_811_, v___x_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_updateSyntax(lean_object* v_m_818_, lean_object* v_k_819_, lean_object* v_f_820_){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_821_ = lean_box(0);
v___x_822_ = l_Lean_KVMap_getSyntax(v_m_818_, v_k_819_, v___x_821_);
v___x_823_ = lean_apply_1(v_f_820_, v___x_822_);
v___x_824_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
v___x_825_ = l_Lean_KVMap_insertCore(v_m_818_, v_k_819_, v___x_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_forIn___redArg___lam__0(lean_object* v_f_826_, lean_object* v_a_827_, lean_object* v_x_828_, lean_object* v___y_829_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = lean_apply_2(v_f_826_, v_a_827_, v___y_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_forIn___redArg(lean_object* v_inst_831_, lean_object* v_kv_832_, lean_object* v_init_833_, lean_object* v_f_834_){
_start:
{
lean_object* v___f_835_; lean_object* v___x_836_; 
v___f_835_ = lean_alloc_closure((void*)(l_Lean_KVMap_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_835_, 0, v_f_834_);
v___x_836_ = l_List_forIn_x27_loop___redArg(v_inst_831_, v___f_835_, v_kv_832_, v_init_833_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_forIn(lean_object* v_00_u03b4_837_, lean_object* v_m_838_, lean_object* v_inst_839_, lean_object* v_kv_840_, lean_object* v_init_841_, lean_object* v_f_842_){
_start:
{
lean_object* v___f_843_; lean_object* v___x_844_; 
v___f_843_ = lean_alloc_closure((void*)(l_Lean_KVMap_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_843_, 0, v_f_842_);
v___x_844_ = l_List_forIn_x27_loop___redArg(v_inst_839_, v___f_843_, v_kv_840_, v_init_841_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__0(lean_object* v___y_845_, lean_object* v_a_846_, lean_object* v_x_847_, lean_object* v___y_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = lean_apply_2(v___y_845_, v_a_846_, v___y_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__1(lean_object* v_inst_850_, lean_object* v_00_u03b2_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v___f_855_; lean_object* v___x_856_; 
v___f_855_ = lean_alloc_closure((void*)(l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_855_, 0, v___y_854_);
v___x_856_ = l_List_forIn_x27_loop___redArg(v_inst_850_, v___f_855_, v___y_852_, v___y_853_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg(lean_object* v_inst_857_){
_start:
{
lean_object* v___f_858_; 
v___f_858_ = lean_alloc_closure((void*)(l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_858_, 0, v_inst_857_);
return v___f_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instForInProdNameDataValueOfMonad(lean_object* v_m_859_, lean_object* v_inst_860_){
_start:
{
lean_object* v___f_861_; 
v___f_861_ = lean_alloc_closure((void*)(l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_861_, 0, v_inst_860_);
return v___f_861_;
}
}
LEAN_EXPORT uint8_t l_Lean_KVMap_subsetAux(lean_object* v_x_862_, lean_object* v_x_863_){
_start:
{
if (lean_obj_tag(v_x_862_) == 0)
{
uint8_t v___x_864_; 
v___x_864_ = 1;
return v___x_864_;
}
else
{
lean_object* v_head_865_; lean_object* v_tail_866_; lean_object* v_fst_867_; lean_object* v_snd_868_; lean_object* v___x_869_; 
v_head_865_ = lean_ctor_get(v_x_862_, 0);
lean_inc(v_head_865_);
v_tail_866_ = lean_ctor_get(v_x_862_, 1);
lean_inc(v_tail_866_);
lean_dec_ref(v_x_862_);
v_fst_867_ = lean_ctor_get(v_head_865_, 0);
lean_inc(v_fst_867_);
v_snd_868_ = lean_ctor_get(v_head_865_, 1);
lean_inc(v_snd_868_);
lean_dec(v_head_865_);
v___x_869_ = l_Lean_KVMap_findCore(v_x_863_, v_fst_867_);
lean_dec(v_fst_867_);
if (lean_obj_tag(v___x_869_) == 0)
{
uint8_t v___x_870_; 
lean_dec(v_snd_868_);
lean_dec(v_tail_866_);
v___x_870_ = 0;
return v___x_870_;
}
else
{
lean_object* v_val_871_; uint8_t v___x_872_; 
v_val_871_ = lean_ctor_get(v___x_869_, 0);
lean_inc(v_val_871_);
lean_dec_ref(v___x_869_);
v___x_872_ = l_Lean_instBEqDataValue_beq(v_snd_868_, v_val_871_);
if (v___x_872_ == 0)
{
lean_dec(v_tail_866_);
return v___x_872_;
}
else
{
v_x_862_ = v_tail_866_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_subsetAux___boxed(lean_object* v_x_874_, lean_object* v_x_875_){
_start:
{
uint8_t v_res_876_; lean_object* v_r_877_; 
v_res_876_ = l_Lean_KVMap_subsetAux(v_x_874_, v_x_875_);
lean_dec(v_x_875_);
v_r_877_ = lean_box(v_res_876_);
return v_r_877_;
}
}
LEAN_EXPORT uint8_t l_Lean_KVMap_subset(lean_object* v_x_878_, lean_object* v_x_879_){
_start:
{
uint8_t v___x_880_; 
v___x_880_ = l_Lean_KVMap_subsetAux(v_x_878_, v_x_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_subset___boxed(lean_object* v_x_881_, lean_object* v_x_882_){
_start:
{
uint8_t v_res_883_; lean_object* v_r_884_; 
v_res_883_ = l_Lean_KVMap_subset(v_x_881_, v_x_882_);
lean_dec(v_x_882_);
v_r_884_ = lean_box(v_res_883_);
return v_r_884_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___redArg(lean_object* v_mergeFn_885_, lean_object* v_as_x27_886_, lean_object* v_b_887_){
_start:
{
if (lean_obj_tag(v_as_x27_886_) == 0)
{
lean_dec_ref(v_mergeFn_885_);
return v_b_887_;
}
else
{
lean_object* v_head_888_; lean_object* v_tail_889_; lean_object* v_fst_890_; lean_object* v_snd_891_; lean_object* v___x_892_; 
v_head_888_ = lean_ctor_get(v_as_x27_886_, 0);
lean_inc(v_head_888_);
v_tail_889_ = lean_ctor_get(v_as_x27_886_, 1);
lean_inc(v_tail_889_);
lean_dec_ref(v_as_x27_886_);
v_fst_890_ = lean_ctor_get(v_head_888_, 0);
lean_inc(v_fst_890_);
v_snd_891_ = lean_ctor_get(v_head_888_, 1);
lean_inc(v_snd_891_);
lean_dec(v_head_888_);
v___x_892_ = l_Lean_KVMap_findCore(v_b_887_, v_fst_890_);
if (lean_obj_tag(v___x_892_) == 1)
{
lean_object* v_val_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v_val_893_ = lean_ctor_get(v___x_892_, 0);
lean_inc(v_val_893_);
lean_dec_ref(v___x_892_);
lean_inc_ref(v_mergeFn_885_);
lean_inc(v_fst_890_);
v___x_894_ = lean_apply_3(v_mergeFn_885_, v_fst_890_, v_val_893_, v_snd_891_);
v___x_895_ = l_Lean_KVMap_insertCore(v_b_887_, v_fst_890_, v___x_894_);
v_as_x27_886_ = v_tail_889_;
v_b_887_ = v___x_895_;
goto _start;
}
else
{
lean_object* v___x_897_; 
lean_dec(v___x_892_);
v___x_897_ = l_Lean_KVMap_insertCore(v_b_887_, v_fst_890_, v_snd_891_);
v_as_x27_886_ = v_tail_889_;
v_b_887_ = v___x_897_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_mergeBy(lean_object* v_mergeFn_899_, lean_object* v_l_900_, lean_object* v_r_901_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___redArg(v_mergeFn_899_, v_r_901_, v_l_900_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0(lean_object* v_mergeFn_903_, lean_object* v_as_904_, lean_object* v_as_x27_905_, lean_object* v_b_906_, lean_object* v_a_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___redArg(v_mergeFn_903_, v_as_x27_905_, v_b_906_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___boxed(lean_object* v_mergeFn_909_, lean_object* v_as_910_, lean_object* v_as_x27_911_, lean_object* v_b_912_, lean_object* v_a_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0(v_mergeFn_909_, v_as_910_, v_as_x27_911_, v_b_912_, v_a_913_);
lean_dec(v_as_910_);
return v_res_914_;
}
}
LEAN_EXPORT uint8_t l_Lean_KVMap_eqv(lean_object* v_m_u2081_915_, lean_object* v_m_u2082_916_){
_start:
{
uint8_t v___x_917_; 
lean_inc(v_m_u2081_915_);
v___x_917_ = l_Lean_KVMap_subsetAux(v_m_u2081_915_, v_m_u2082_916_);
if (v___x_917_ == 0)
{
lean_dec(v_m_u2082_916_);
lean_dec(v_m_u2081_915_);
return v___x_917_;
}
else
{
uint8_t v___x_918_; 
v___x_918_ = l_Lean_KVMap_subsetAux(v_m_u2082_916_, v_m_u2081_915_);
lean_dec(v_m_u2081_915_);
return v___x_918_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_eqv___boxed(lean_object* v_m_u2081_919_, lean_object* v_m_u2082_920_){
_start:
{
uint8_t v_res_921_; lean_object* v_r_922_; 
v_res_921_ = l_Lean_KVMap_eqv(v_m_u2081_919_, v_m_u2082_920_);
v_r_922_ = lean_box(v_res_921_);
return v_r_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_get_x3f___redArg(lean_object* v_inst_925_, lean_object* v_m_926_, lean_object* v_k_927_){
_start:
{
lean_object* v_ofDataValue_x3f_928_; lean_object* v___x_929_; 
v_ofDataValue_x3f_928_ = lean_ctor_get(v_inst_925_, 1);
lean_inc_ref(v_ofDataValue_x3f_928_);
lean_dec_ref(v_inst_925_);
v___x_929_ = l_Lean_KVMap_findCore(v_m_926_, v_k_927_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v___x_930_; 
lean_dec_ref(v_ofDataValue_x3f_928_);
v___x_930_ = lean_box(0);
return v___x_930_;
}
else
{
lean_object* v_val_931_; lean_object* v___x_932_; 
v_val_931_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_val_931_);
lean_dec_ref(v___x_929_);
v___x_932_ = lean_apply_1(v_ofDataValue_x3f_928_, v_val_931_);
return v___x_932_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_get_x3f___redArg___boxed(lean_object* v_inst_933_, lean_object* v_m_934_, lean_object* v_k_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_KVMap_get_x3f___redArg(v_inst_933_, v_m_934_, v_k_935_);
lean_dec(v_k_935_);
lean_dec(v_m_934_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_get_x3f(lean_object* v_00_u03b1_937_, lean_object* v_inst_938_, lean_object* v_m_939_, lean_object* v_k_940_){
_start:
{
lean_object* v_ofDataValue_x3f_941_; lean_object* v___x_942_; 
v_ofDataValue_x3f_941_ = lean_ctor_get(v_inst_938_, 1);
lean_inc_ref(v_ofDataValue_x3f_941_);
lean_dec_ref(v_inst_938_);
v___x_942_ = l_Lean_KVMap_findCore(v_m_939_, v_k_940_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v___x_943_; 
lean_dec_ref(v_ofDataValue_x3f_941_);
v___x_943_ = lean_box(0);
return v___x_943_;
}
else
{
lean_object* v_val_944_; lean_object* v___x_945_; 
v_val_944_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_val_944_);
lean_dec_ref(v___x_942_);
v___x_945_ = lean_apply_1(v_ofDataValue_x3f_941_, v_val_944_);
return v___x_945_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_get_x3f___boxed(lean_object* v_00_u03b1_946_, lean_object* v_inst_947_, lean_object* v_m_948_, lean_object* v_k_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_KVMap_get_x3f(v_00_u03b1_946_, v_inst_947_, v_m_948_, v_k_949_);
lean_dec(v_k_949_);
lean_dec(v_m_948_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_get___redArg(lean_object* v_inst_951_, lean_object* v_m_952_, lean_object* v_k_953_, lean_object* v_defVal_954_){
_start:
{
lean_object* v_ofDataValue_x3f_955_; lean_object* v___x_956_; 
v_ofDataValue_x3f_955_ = lean_ctor_get(v_inst_951_, 1);
lean_inc_ref(v_ofDataValue_x3f_955_);
lean_dec_ref(v_inst_951_);
v___x_956_ = l_Lean_KVMap_findCore(v_m_952_, v_k_953_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_dec_ref(v_ofDataValue_x3f_955_);
lean_inc(v_defVal_954_);
return v_defVal_954_;
}
else
{
lean_object* v_val_957_; lean_object* v___x_958_; 
v_val_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_val_957_);
lean_dec_ref(v___x_956_);
v___x_958_ = lean_apply_1(v_ofDataValue_x3f_955_, v_val_957_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_inc(v_defVal_954_);
return v_defVal_954_;
}
else
{
lean_object* v_val_959_; 
v_val_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_val_959_);
lean_dec_ref(v___x_958_);
return v_val_959_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_get___redArg___boxed(lean_object* v_inst_960_, lean_object* v_m_961_, lean_object* v_k_962_, lean_object* v_defVal_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_KVMap_get___redArg(v_inst_960_, v_m_961_, v_k_962_, v_defVal_963_);
lean_dec(v_defVal_963_);
lean_dec(v_k_962_);
lean_dec(v_m_961_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_get(lean_object* v_00_u03b1_965_, lean_object* v_inst_966_, lean_object* v_m_967_, lean_object* v_k_968_, lean_object* v_defVal_969_){
_start:
{
lean_object* v_ofDataValue_x3f_970_; lean_object* v___x_971_; 
v_ofDataValue_x3f_970_ = lean_ctor_get(v_inst_966_, 1);
lean_inc_ref(v_ofDataValue_x3f_970_);
lean_dec_ref(v_inst_966_);
v___x_971_ = l_Lean_KVMap_findCore(v_m_967_, v_k_968_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_dec_ref(v_ofDataValue_x3f_970_);
lean_inc(v_defVal_969_);
return v_defVal_969_;
}
else
{
lean_object* v_val_972_; lean_object* v___x_973_; 
v_val_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_val_972_);
lean_dec_ref(v___x_971_);
v___x_973_ = lean_apply_1(v_ofDataValue_x3f_970_, v_val_972_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_inc(v_defVal_969_);
return v_defVal_969_;
}
else
{
lean_object* v_val_974_; 
v_val_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_val_974_);
lean_dec_ref(v___x_973_);
return v_val_974_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_get___boxed(lean_object* v_00_u03b1_975_, lean_object* v_inst_976_, lean_object* v_m_977_, lean_object* v_k_978_, lean_object* v_defVal_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_KVMap_get(v_00_u03b1_975_, v_inst_976_, v_m_977_, v_k_978_, v_defVal_979_);
lean_dec(v_defVal_979_);
lean_dec(v_k_978_);
lean_dec(v_m_977_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_set___redArg(lean_object* v_inst_981_, lean_object* v_m_982_, lean_object* v_k_983_, lean_object* v_v_984_){
_start:
{
lean_object* v_toDataValue_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v_toDataValue_985_ = lean_ctor_get(v_inst_981_, 0);
lean_inc_ref(v_toDataValue_985_);
lean_dec_ref(v_inst_981_);
v___x_986_ = lean_apply_1(v_toDataValue_985_, v_v_984_);
v___x_987_ = l_Lean_KVMap_insertCore(v_m_982_, v_k_983_, v___x_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_set(lean_object* v_00_u03b1_988_, lean_object* v_inst_989_, lean_object* v_m_990_, lean_object* v_k_991_, lean_object* v_v_992_){
_start:
{
lean_object* v_toDataValue_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v_toDataValue_993_ = lean_ctor_get(v_inst_989_, 0);
lean_inc_ref(v_toDataValue_993_);
lean_dec_ref(v_inst_989_);
v___x_994_ = lean_apply_1(v_toDataValue_993_, v_v_992_);
v___x_995_ = l_Lean_KVMap_insertCore(v_m_990_, v_k_991_, v___x_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_update___redArg(lean_object* v_inst_996_, lean_object* v_m_997_, lean_object* v_k_998_, lean_object* v_f_999_){
_start:
{
lean_object* v_toDataValue_1000_; lean_object* v_ofDataValue_x3f_1001_; lean_object* v___y_1003_; lean_object* v___x_1009_; 
v_toDataValue_1000_ = lean_ctor_get(v_inst_996_, 0);
lean_inc_ref(v_toDataValue_1000_);
v_ofDataValue_x3f_1001_ = lean_ctor_get(v_inst_996_, 1);
lean_inc_ref(v_ofDataValue_x3f_1001_);
lean_dec_ref(v_inst_996_);
v___x_1009_ = l_Lean_KVMap_findCore(v_m_997_, v_k_998_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v___x_1010_; 
lean_dec_ref(v_ofDataValue_x3f_1001_);
v___x_1010_ = lean_box(0);
v___y_1003_ = v___x_1010_;
goto v___jp_1002_;
}
else
{
lean_object* v_val_1011_; lean_object* v___x_1012_; 
v_val_1011_ = lean_ctor_get(v___x_1009_, 0);
lean_inc(v_val_1011_);
lean_dec_ref(v___x_1009_);
v___x_1012_ = lean_apply_1(v_ofDataValue_x3f_1001_, v_val_1011_);
v___y_1003_ = v___x_1012_;
goto v___jp_1002_;
}
v___jp_1002_:
{
lean_object* v___x_1004_; 
v___x_1004_ = lean_apply_1(v_f_999_, v___y_1003_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v___x_1005_; 
lean_dec_ref(v_toDataValue_1000_);
v___x_1005_ = l_Lean_KVMap_erase(v_m_997_, v_k_998_);
lean_dec(v_k_998_);
return v___x_1005_;
}
else
{
lean_object* v_val_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v_val_1006_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_val_1006_);
lean_dec_ref(v___x_1004_);
v___x_1007_ = lean_apply_1(v_toDataValue_1000_, v_val_1006_);
v___x_1008_ = l_Lean_KVMap_insertCore(v_m_997_, v_k_998_, v___x_1007_);
return v___x_1008_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_update(lean_object* v_00_u03b1_1013_, lean_object* v_inst_1014_, lean_object* v_m_1015_, lean_object* v_k_1016_, lean_object* v_f_1017_){
_start:
{
lean_object* v_toDataValue_1018_; lean_object* v_ofDataValue_x3f_1019_; lean_object* v___y_1021_; lean_object* v___x_1027_; 
v_toDataValue_1018_ = lean_ctor_get(v_inst_1014_, 0);
lean_inc_ref(v_toDataValue_1018_);
v_ofDataValue_x3f_1019_ = lean_ctor_get(v_inst_1014_, 1);
lean_inc_ref(v_ofDataValue_x3f_1019_);
lean_dec_ref(v_inst_1014_);
v___x_1027_ = l_Lean_KVMap_findCore(v_m_1015_, v_k_1016_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v___x_1028_; 
lean_dec_ref(v_ofDataValue_x3f_1019_);
v___x_1028_ = lean_box(0);
v___y_1021_ = v___x_1028_;
goto v___jp_1020_;
}
else
{
lean_object* v_val_1029_; lean_object* v___x_1030_; 
v_val_1029_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_val_1029_);
lean_dec_ref(v___x_1027_);
v___x_1030_ = lean_apply_1(v_ofDataValue_x3f_1019_, v_val_1029_);
v___y_1021_ = v___x_1030_;
goto v___jp_1020_;
}
v___jp_1020_:
{
lean_object* v___x_1022_; 
v___x_1022_ = lean_apply_1(v_f_1017_, v___y_1021_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v___x_1023_; 
lean_dec_ref(v_toDataValue_1018_);
v___x_1023_ = l_Lean_KVMap_erase(v_m_1015_, v_k_1016_);
lean_dec(v_k_1016_);
return v___x_1023_;
}
else
{
lean_object* v_val_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v_val_1024_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_val_1024_);
lean_dec_ref(v___x_1022_);
v___x_1025_ = lean_apply_1(v_toDataValue_1018_, v_val_1024_);
v___x_1026_ = l_Lean_KVMap_insertCore(v_m_1015_, v_k_1016_, v___x_1025_);
return v___x_1026_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueDataValue___lam__0(lean_object* v_val_1031_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1032_, 0, v_val_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueBool___lam__1(lean_object* v_x_1039_){
_start:
{
if (lean_obj_tag(v_x_1039_) == 1)
{
uint8_t v_v_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v_v_1040_ = lean_ctor_get_uint8(v_x_1039_, 0);
v___x_1041_ = lean_box(v_v_1040_);
v___x_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
return v___x_1042_;
}
else
{
lean_object* v___x_1043_; 
v___x_1043_ = lean_box(0);
return v___x_1043_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueBool___lam__1___boxed(lean_object* v_x_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Lean_KVMap_instValueBool___lam__1(v_x_1044_);
lean_dec_ref(v_x_1044_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueNat___lam__1(lean_object* v_x_1051_){
_start:
{
if (lean_obj_tag(v_x_1051_) == 3)
{
lean_object* v_v_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
v_v_1052_ = lean_ctor_get(v_x_1051_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v_x_1051_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v_x_1051_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_v_1052_);
lean_dec(v_x_1051_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
lean_ctor_set_tag(v___x_1054_, 1);
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_v_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
else
{
lean_object* v___x_1060_; 
lean_dec_ref(v_x_1051_);
v___x_1060_ = lean_box(0);
return v___x_1060_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueInt___lam__1(lean_object* v_x_1066_){
_start:
{
if (lean_obj_tag(v_x_1066_) == 4)
{
lean_object* v_v_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
v_v_1067_ = lean_ctor_get(v_x_1066_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_x_1066_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1069_ = v_x_1066_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_v_1067_);
lean_dec(v_x_1066_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
lean_ctor_set_tag(v___x_1069_, 1);
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_v_1067_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
else
{
lean_object* v___x_1075_; 
lean_dec_ref(v_x_1066_);
v___x_1075_ = lean_box(0);
return v___x_1075_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueName___lam__1(lean_object* v_x_1081_){
_start:
{
if (lean_obj_tag(v_x_1081_) == 2)
{
lean_object* v_v_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
v_v_1082_ = lean_ctor_get(v_x_1081_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v_x_1081_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v_x_1081_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_v_1082_);
lean_dec(v_x_1081_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
lean_ctor_set_tag(v___x_1084_, 1);
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_v_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
else
{
lean_object* v___x_1090_; 
lean_dec_ref(v_x_1081_);
v___x_1090_ = lean_box(0);
return v___x_1090_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueString___lam__1(lean_object* v_x_1096_){
_start:
{
if (lean_obj_tag(v_x_1096_) == 0)
{
lean_object* v_v_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
v_v_1097_ = lean_ctor_get(v_x_1096_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v_x_1096_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v_x_1096_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_v_1097_);
lean_dec(v_x_1096_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
lean_ctor_set_tag(v___x_1099_, 1);
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_v_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
else
{
lean_object* v___x_1105_; 
lean_dec_ref(v_x_1096_);
v___x_1105_ = lean_box(0);
return v___x_1105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueSyntax___lam__1(lean_object* v_x_1111_){
_start:
{
if (lean_obj_tag(v_x_1111_) == 5)
{
lean_object* v_v_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
v_v_1112_ = lean_ctor_get(v_x_1111_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_x_1111_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v_x_1111_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_v_1112_);
lean_dec(v_x_1111_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
lean_ctor_set_tag(v___x_1114_, 1);
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_v_1112_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
else
{
lean_object* v___x_1120_; 
lean_dec_ref(v_x_1111_);
v___x_1120_ = lean_box(0);
return v___x_1120_;
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

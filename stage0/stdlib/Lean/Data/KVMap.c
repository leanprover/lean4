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
lean_object* l_List_forIn_x27_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DataValue_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_DataValue_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_DataValue_str(lean_object*);
static const lean_closure_object l_Lean_instToStringDataValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_DataValue_str, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Lean_KVMap_forIn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_instForInProdNameDataValueOfMonad(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_KVMap_subsetAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_subsetAux___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_KVMap_subset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_subset___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_mergeBy(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_KVMap_mergeBy___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_DataValue_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_DataValue_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
switch(lean_obj_tag(v_t_5_))
{
case 0:
{
lean_object* v_v_7_; lean_object* v___x_8_; 
v_v_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_v_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_v_7_);
return v___x_8_;
}
case 1:
{
uint8_t v_v_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_v_9_ = lean_ctor_get_uint8(v_t_5_, 0);
lean_dec_ref_known(v_t_5_, 0);
v___x_10_ = lean_box(v_v_9_);
v___x_11_ = lean_apply_1(v_k_6_, v___x_10_);
return v___x_11_;
}
default: 
{
lean_object* v_v_12_; lean_object* v___x_13_; 
v_v_12_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_v_12_);
lean_dec_ref(v_t_5_);
v___x_13_ = lean_apply_1(v_k_6_, v_v_12_);
return v___x_13_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_ctorElim(lean_object* v_motive_14_, lean_object* v_ctorIdx_15_, lean_object* v_t_16_, lean_object* v_h_17_, lean_object* v_k_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_DataValue_ctorElim___redArg(v_t_16_, v_k_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_ctorElim___boxed(lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_DataValue_ctorElim(v_motive_20_, v_ctorIdx_21_, v_t_22_, v_h_23_, v_k_24_);
lean_dec(v_ctorIdx_21_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_ofString_elim___redArg(lean_object* v_t_26_, lean_object* v_ofString_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Lean_DataValue_ctorElim___redArg(v_t_26_, v_ofString_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_ofString_elim(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_ofString_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_DataValue_ctorElim___redArg(v_t_30_, v_ofString_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_ofBool_elim___redArg(lean_object* v_t_34_, lean_object* v_ofBool_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_DataValue_ctorElim___redArg(v_t_34_, v_ofBool_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_ofBool_elim(lean_object* v_motive_37_, lean_object* v_t_38_, lean_object* v_h_39_, lean_object* v_ofBool_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_DataValue_ctorElim___redArg(v_t_38_, v_ofBool_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_ofName_elim___redArg(lean_object* v_t_42_, lean_object* v_ofName_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lean_DataValue_ctorElim___redArg(v_t_42_, v_ofName_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_ofName_elim(lean_object* v_motive_45_, lean_object* v_t_46_, lean_object* v_h_47_, lean_object* v_ofName_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lean_DataValue_ctorElim___redArg(v_t_46_, v_ofName_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_ofNat_elim___redArg(lean_object* v_t_50_, lean_object* v_ofNat_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Lean_DataValue_ctorElim___redArg(v_t_50_, v_ofNat_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_ofNat_elim(lean_object* v_motive_53_, lean_object* v_t_54_, lean_object* v_h_55_, lean_object* v_ofNat_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_DataValue_ctorElim___redArg(v_t_54_, v_ofNat_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_ofInt_elim___redArg(lean_object* v_t_58_, lean_object* v_ofInt_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Lean_DataValue_ctorElim___redArg(v_t_58_, v_ofInt_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_ofInt_elim(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_ofInt_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_DataValue_ctorElim___redArg(v_t_62_, v_ofInt_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_ofSyntax_elim___redArg(lean_object* v_t_66_, lean_object* v_ofSyntax_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_DataValue_ctorElim___redArg(v_t_66_, v_ofSyntax_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_ofSyntax_elim(lean_object* v_motive_69_, lean_object* v_t_70_, lean_object* v_h_71_, lean_object* v_ofSyntax_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_DataValue_ctorElim___redArg(v_t_70_, v_ofSyntax_72_);
return v___x_73_;
}
}
uint8_t l_Lean_instBEqDataValue_beq(lean_object* v_x_79_, lean_object* v_x_80_){
_start:
{
switch(lean_obj_tag(v_x_79_))
{
case 0:
{
if (lean_obj_tag(v_x_80_) == 0)
{
lean_object* v_v_81_; lean_object* v_v_82_; uint8_t v___x_83_; 
v_v_81_ = lean_ctor_get(v_x_79_, 0);
v_v_82_ = lean_ctor_get(v_x_80_, 0);
v___x_83_ = lean_string_dec_eq(v_v_81_, v_v_82_);
return v___x_83_;
}
else
{
uint8_t v___x_84_; 
v___x_84_ = 0;
return v___x_84_;
}
}
case 1:
{
if (lean_obj_tag(v_x_80_) == 1)
{
uint8_t v_v_85_; 
v_v_85_ = lean_ctor_get_uint8(v_x_80_, 0);
if (v_v_85_ == 0)
{
uint8_t v_v_86_; 
v_v_86_ = lean_ctor_get_uint8(v_x_79_, 0);
if (v_v_86_ == 0)
{
uint8_t v___x_87_; 
v___x_87_ = 1;
return v___x_87_;
}
else
{
return v_v_85_;
}
}
else
{
uint8_t v_v_88_; 
v_v_88_ = lean_ctor_get_uint8(v_x_79_, 0);
return v_v_88_;
}
}
else
{
uint8_t v___x_89_; 
v___x_89_ = 0;
return v___x_89_;
}
}
case 2:
{
if (lean_obj_tag(v_x_80_) == 2)
{
lean_object* v_v_90_; lean_object* v_v_91_; uint8_t v___x_92_; 
v_v_90_ = lean_ctor_get(v_x_79_, 0);
v_v_91_ = lean_ctor_get(v_x_80_, 0);
v___x_92_ = lean_name_eq(v_v_90_, v_v_91_);
return v___x_92_;
}
else
{
uint8_t v___x_93_; 
v___x_93_ = 0;
return v___x_93_;
}
}
case 3:
{
if (lean_obj_tag(v_x_80_) == 3)
{
lean_object* v_v_94_; lean_object* v_v_95_; uint8_t v___x_96_; 
v_v_94_ = lean_ctor_get(v_x_79_, 0);
v_v_95_ = lean_ctor_get(v_x_80_, 0);
v___x_96_ = lean_nat_dec_eq(v_v_94_, v_v_95_);
return v___x_96_;
}
else
{
uint8_t v___x_97_; 
v___x_97_ = 0;
return v___x_97_;
}
}
case 4:
{
if (lean_obj_tag(v_x_80_) == 4)
{
lean_object* v_v_98_; lean_object* v_v_99_; uint8_t v___x_100_; 
v_v_98_ = lean_ctor_get(v_x_79_, 0);
v_v_99_ = lean_ctor_get(v_x_80_, 0);
v___x_100_ = lean_int_dec_eq(v_v_98_, v_v_99_);
return v___x_100_;
}
else
{
uint8_t v___x_101_; 
v___x_101_ = 0;
return v___x_101_;
}
}
default: 
{
if (lean_obj_tag(v_x_80_) == 5)
{
lean_object* v_v_102_; lean_object* v_v_103_; uint8_t v___x_104_; 
v_v_102_ = lean_ctor_get(v_x_79_, 0);
v_v_103_ = lean_ctor_get(v_x_80_, 0);
v___x_104_ = l_Lean_Syntax_structEq(v_v_102_, v_v_103_);
return v___x_104_;
}
else
{
uint8_t v___x_105_; 
v___x_105_ = 0;
return v___x_105_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instBEqDataValue_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_79_ = stack[0].m_obj;
lean_object* v_x_80_ = stack[1].m_obj;
uint8_t v_res_106_;
v_res_106_ = l_Lean_instBEqDataValue_beq(v_x_79_, v_x_80_);
stack->m_num = v_res_106_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqDataValue_beq___boxed(lean_object* v_x_107_, lean_object* v_x_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_Lean_instBEqDataValue_beq(v_x_107_, v_x_108_);
lean_dec_ref(v_x_108_);
lean_dec_ref(v_x_107_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
static lean_object* _init_l_Lean_instReprDataValue_repr___closed__3(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_unsigned_to_nat(2u);
v___x_120_ = lean_nat_to_int(v___x_119_);
return v___x_120_;
}
}
static lean_object* _init_l_Lean_instReprDataValue_repr___closed__4(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = lean_unsigned_to_nat(1u);
v___x_122_ = lean_nat_to_int(v___x_121_);
return v___x_122_;
}
}
static lean_object* _init_l_Lean_instReprDataValue_repr___closed__17(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = lean_unsigned_to_nat(0u);
v___x_148_ = lean_nat_to_int(v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprDataValue_repr(lean_object* v_x_155_, lean_object* v_prec_156_){
_start:
{
lean_object* v___y_158_; lean_object* v___y_159_; lean_object* v___y_160_; 
switch(lean_obj_tag(v_x_155_))
{
case 0:
{
lean_object* v_v_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_186_; 
v_v_166_ = lean_ctor_get(v_x_155_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v_x_155_);
if (v_isSharedCheck_186_ == 0)
{
v___x_168_ = v_x_155_;
v_isShared_169_ = v_isSharedCheck_186_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_v_166_);
lean_dec(v_x_155_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_186_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___y_171_; lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_182_ = lean_unsigned_to_nat(1024u);
v___x_183_ = lean_nat_dec_le(v___x_182_, v_prec_156_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; 
v___x_184_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__3, &l_Lean_instReprDataValue_repr___closed__3_once, _init_l_Lean_instReprDataValue_repr___closed__3);
v___y_171_ = v___x_184_;
goto v___jp_170_;
}
else
{
lean_object* v___x_185_; 
v___x_185_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__4, &l_Lean_instReprDataValue_repr___closed__4_once, _init_l_Lean_instReprDataValue_repr___closed__4);
v___y_171_ = v___x_185_;
goto v___jp_170_;
}
v___jp_170_:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_175_; 
v___x_172_ = ((lean_object*)(l_Lean_instReprDataValue_repr___closed__2));
v___x_173_ = l_String_quote(v_v_166_);
if (v_isShared_169_ == 0)
{
lean_ctor_set_tag(v___x_168_, 3);
lean_ctor_set(v___x_168_, 0, v___x_173_);
v___x_175_ = v___x_168_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_173_);
v___x_175_ = v_reuseFailAlloc_181_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
lean_object* v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_172_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
lean_inc(v___y_171_);
v___x_177_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_177_, 0, v___y_171_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
v___x_178_ = 0;
v___x_179_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_179_, 0, v___x_177_);
lean_ctor_set_uint8(v___x_179_, sizeof(void*)*1, v___x_178_);
v___x_180_ = l_Repr_addAppParen(v___x_179_, v_prec_156_);
return v___x_180_;
}
}
}
}
case 1:
{
uint8_t v_v_187_; lean_object* v___y_189_; lean_object* v___x_197_; uint8_t v___x_198_; 
v_v_187_ = lean_ctor_get_uint8(v_x_155_, 0);
lean_dec_ref_known(v_x_155_, 0);
v___x_197_ = lean_unsigned_to_nat(1024u);
v___x_198_ = lean_nat_dec_le(v___x_197_, v_prec_156_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; 
v___x_199_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__3, &l_Lean_instReprDataValue_repr___closed__3_once, _init_l_Lean_instReprDataValue_repr___closed__3);
v___y_189_ = v___x_199_;
goto v___jp_188_;
}
else
{
lean_object* v___x_200_; 
v___x_200_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__4, &l_Lean_instReprDataValue_repr___closed__4_once, _init_l_Lean_instReprDataValue_repr___closed__4);
v___y_189_ = v___x_200_;
goto v___jp_188_;
}
v___jp_188_:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_190_ = ((lean_object*)(l_Lean_instReprDataValue_repr___closed__7));
v___x_191_ = l_Bool_repr___redArg(v_v_187_);
v___x_192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_190_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
lean_inc(v___y_189_);
v___x_193_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_193_, 0, v___y_189_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
v___x_194_ = 0;
v___x_195_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_195_, 0, v___x_193_);
lean_ctor_set_uint8(v___x_195_, sizeof(void*)*1, v___x_194_);
v___x_196_ = l_Repr_addAppParen(v___x_195_, v_prec_156_);
return v___x_196_;
}
}
case 2:
{
lean_object* v_v_201_; lean_object* v___y_203_; lean_object* v___x_212_; uint8_t v___x_213_; 
v_v_201_ = lean_ctor_get(v_x_155_, 0);
lean_inc(v_v_201_);
lean_dec_ref_known(v_x_155_, 1);
v___x_212_ = lean_unsigned_to_nat(1024u);
v___x_213_ = lean_nat_dec_le(v___x_212_, v_prec_156_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; 
v___x_214_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__3, &l_Lean_instReprDataValue_repr___closed__3_once, _init_l_Lean_instReprDataValue_repr___closed__3);
v___y_203_ = v___x_214_;
goto v___jp_202_;
}
else
{
lean_object* v___x_215_; 
v___x_215_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__4, &l_Lean_instReprDataValue_repr___closed__4_once, _init_l_Lean_instReprDataValue_repr___closed__4);
v___y_203_ = v___x_215_;
goto v___jp_202_;
}
v___jp_202_:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_204_ = ((lean_object*)(l_Lean_instReprDataValue_repr___closed__10));
v___x_205_ = lean_unsigned_to_nat(1024u);
v___x_206_ = l_Lean_Name_reprPrec(v_v_201_, v___x_205_);
v___x_207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_204_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
lean_inc(v___y_203_);
v___x_208_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_208_, 0, v___y_203_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
v___x_209_ = 0;
v___x_210_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_210_, 0, v___x_208_);
lean_ctor_set_uint8(v___x_210_, sizeof(void*)*1, v___x_209_);
v___x_211_ = l_Repr_addAppParen(v___x_210_, v_prec_156_);
return v___x_211_;
}
}
case 3:
{
lean_object* v_v_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_236_; 
v_v_216_ = lean_ctor_get(v_x_155_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v_x_155_);
if (v_isSharedCheck_236_ == 0)
{
v___x_218_ = v_x_155_;
v_isShared_219_ = v_isSharedCheck_236_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_v_216_);
lean_dec(v_x_155_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_236_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___y_221_; lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_232_ = lean_unsigned_to_nat(1024u);
v___x_233_ = lean_nat_dec_le(v___x_232_, v_prec_156_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; 
v___x_234_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__3, &l_Lean_instReprDataValue_repr___closed__3_once, _init_l_Lean_instReprDataValue_repr___closed__3);
v___y_221_ = v___x_234_;
goto v___jp_220_;
}
else
{
lean_object* v___x_235_; 
v___x_235_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__4, &l_Lean_instReprDataValue_repr___closed__4_once, _init_l_Lean_instReprDataValue_repr___closed__4);
v___y_221_ = v___x_235_;
goto v___jp_220_;
}
v___jp_220_:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_225_; 
v___x_222_ = ((lean_object*)(l_Lean_instReprDataValue_repr___closed__13));
v___x_223_ = l_Nat_reprFast(v_v_216_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 0, v___x_223_);
v___x_225_ = v___x_218_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_223_);
v___x_225_ = v_reuseFailAlloc_231_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_226_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_222_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
lean_inc(v___y_221_);
v___x_227_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_227_, 0, v___y_221_);
lean_ctor_set(v___x_227_, 1, v___x_226_);
v___x_228_ = 0;
v___x_229_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_229_, 0, v___x_227_);
lean_ctor_set_uint8(v___x_229_, sizeof(void*)*1, v___x_228_);
v___x_230_ = l_Repr_addAppParen(v___x_229_, v_prec_156_);
return v___x_230_;
}
}
}
}
case 4:
{
lean_object* v_v_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_260_; 
v_v_237_ = lean_ctor_get(v_x_155_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v_x_155_);
if (v_isSharedCheck_260_ == 0)
{
v___x_239_ = v_x_155_;
v_isShared_240_ = v_isSharedCheck_260_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_v_237_);
lean_dec(v_x_155_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_260_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___y_242_; lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_256_ = lean_unsigned_to_nat(1024u);
v___x_257_ = lean_nat_dec_le(v___x_256_, v_prec_156_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; 
v___x_258_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__3, &l_Lean_instReprDataValue_repr___closed__3_once, _init_l_Lean_instReprDataValue_repr___closed__3);
v___y_242_ = v___x_258_;
goto v___jp_241_;
}
else
{
lean_object* v___x_259_; 
v___x_259_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__4, &l_Lean_instReprDataValue_repr___closed__4_once, _init_l_Lean_instReprDataValue_repr___closed__4);
v___y_242_ = v___x_259_;
goto v___jp_241_;
}
v___jp_241_:
{
lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_243_ = ((lean_object*)(l_Lean_instReprDataValue_repr___closed__16));
v___x_244_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__17, &l_Lean_instReprDataValue_repr___closed__17_once, _init_l_Lean_instReprDataValue_repr___closed__17);
v___x_245_ = lean_int_dec_lt(v_v_237_, v___x_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_246_ = l_Int_repr(v_v_237_);
lean_dec(v_v_237_);
if (v_isShared_240_ == 0)
{
lean_ctor_set_tag(v___x_239_, 3);
lean_ctor_set(v___x_239_, 0, v___x_246_);
v___x_248_ = v___x_239_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_246_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
v___y_158_ = v___x_243_;
v___y_159_ = v___y_242_;
v___y_160_ = v___x_248_;
goto v___jp_157_;
}
}
else
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_253_; 
v___x_250_ = lean_unsigned_to_nat(1024u);
v___x_251_ = l_Int_repr(v_v_237_);
lean_dec(v_v_237_);
if (v_isShared_240_ == 0)
{
lean_ctor_set_tag(v___x_239_, 3);
lean_ctor_set(v___x_239_, 0, v___x_251_);
v___x_253_ = v___x_239_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_251_);
v___x_253_ = v_reuseFailAlloc_255_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
lean_object* v___x_254_; 
v___x_254_ = l_Repr_addAppParen(v___x_253_, v___x_250_);
v___y_158_ = v___x_243_;
v___y_159_ = v___y_242_;
v___y_160_ = v___x_254_;
goto v___jp_157_;
}
}
}
}
}
default: 
{
lean_object* v_v_261_; lean_object* v___y_263_; lean_object* v___x_272_; uint8_t v___x_273_; 
v_v_261_ = lean_ctor_get(v_x_155_, 0);
lean_inc(v_v_261_);
lean_dec_ref_known(v_x_155_, 1);
v___x_272_ = lean_unsigned_to_nat(1024u);
v___x_273_ = lean_nat_dec_le(v___x_272_, v_prec_156_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; 
v___x_274_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__3, &l_Lean_instReprDataValue_repr___closed__3_once, _init_l_Lean_instReprDataValue_repr___closed__3);
v___y_263_ = v___x_274_;
goto v___jp_262_;
}
else
{
lean_object* v___x_275_; 
v___x_275_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__4, &l_Lean_instReprDataValue_repr___closed__4_once, _init_l_Lean_instReprDataValue_repr___closed__4);
v___y_263_ = v___x_275_;
goto v___jp_262_;
}
v___jp_262_:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; uint8_t v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_264_ = ((lean_object*)(l_Lean_instReprDataValue_repr___closed__20));
v___x_265_ = lean_unsigned_to_nat(1024u);
v___x_266_ = l_Lean_Syntax_instRepr_repr(v_v_261_, v___x_265_);
v___x_267_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_264_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
lean_inc(v___y_263_);
v___x_268_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_268_, 0, v___y_263_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
v___x_269_ = 0;
v___x_270_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_270_, 0, v___x_268_);
lean_ctor_set_uint8(v___x_270_, sizeof(void*)*1, v___x_269_);
v___x_271_ = l_Repr_addAppParen(v___x_270_, v_prec_156_);
return v___x_271_;
}
}
}
v___jp_157_:
{
lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
lean_inc(v___y_158_);
v___x_161_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_161_, 0, v___y_158_);
lean_ctor_set(v___x_161_, 1, v___y_160_);
lean_inc(v___y_159_);
v___x_162_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_162_, 0, v___y_159_);
lean_ctor_set(v___x_162_, 1, v___x_161_);
v___x_163_ = 0;
v___x_164_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_164_, 0, v___x_162_);
lean_ctor_set_uint8(v___x_164_, sizeof(void*)*1, v___x_163_);
v___x_165_ = l_Repr_addAppParen(v___x_164_, v_prec_156_);
return v___x_165_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprDataValue_repr___boxed(lean_object* v_x_276_, lean_object* v_prec_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_instReprDataValue_repr(v_x_276_, v_prec_277_);
lean_dec(v_prec_277_);
return v_res_278_;
}
}
uint8_t lean_data_value_beq(lean_object* v_a_281_, lean_object* v_b_282_){
_start:
{
uint8_t v___x_283_; 
v___x_283_ = l_Lean_instBEqDataValue_beq(v_a_281_, v_b_282_);
lean_dec_ref(v_b_282_);
lean_dec_ref(v_a_281_);
return v___x_283_;
}
}
LEAN_EXPORT void lean_data_value_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_281_ = stack[0].m_obj;
lean_object* v_b_282_ = stack[1].m_obj;
uint8_t v_res_284_;
v_res_284_ = lean_data_value_beq(v_a_281_, v_b_282_);
stack->m_num = v_res_284_;
}
LEAN_EXPORT lean_object* l_Lean_DataValue_beqExp___boxed(lean_object* v_a_285_, lean_object* v_b_286_){
_start:
{
uint8_t v_res_287_; lean_object* v_r_288_; 
v_res_287_ = lean_data_value_beq(v_a_285_, v_b_286_);
v_r_288_ = lean_box(v_res_287_);
return v_r_288_;
}
}
lean_object* lean_mk_bool_data_value(uint8_t v_b_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_290_, 0, v_b_289_);
return v___x_290_;
}
}
LEAN_EXPORT void lean_mk_bool_data_value_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_289_ = stack[0].m_num;
lean_object* v_res_291_;
v_res_291_ = lean_mk_bool_data_value(v_b_289_);
stack->m_obj
 = v_res_291_;
}
LEAN_EXPORT lean_object* l_Lean_mkBoolDataValueEx___boxed(lean_object* v_b_292_){
_start:
{
uint8_t v_b_boxed_293_; lean_object* v_res_294_; 
v_b_boxed_293_ = lean_unbox(v_b_292_);
v_res_294_ = lean_mk_bool_data_value(v_b_boxed_293_);
return v_res_294_;
}
}
uint8_t lean_data_value_bool(lean_object* v_x_295_){
_start:
{
if (lean_obj_tag(v_x_295_) == 1)
{
uint8_t v_v_296_; 
v_v_296_ = lean_ctor_get_uint8(v_x_295_, 0);
lean_dec_ref_known(v_x_295_, 0);
return v_v_296_;
}
else
{
uint8_t v___x_297_; 
lean_dec_ref(v_x_295_);
v___x_297_ = 0;
return v___x_297_;
}
}
}
LEAN_EXPORT void lean_data_value_bool_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_295_ = stack[0].m_obj;
uint8_t v_res_298_;
v_res_298_ = lean_data_value_bool(v_x_295_);
stack->m_num = v_res_298_;
}
LEAN_EXPORT lean_object* l_Lean_DataValue_getBoolEx___boxed(lean_object* v_x_299_){
_start:
{
uint8_t v_res_300_; lean_object* v_r_301_; 
v_res_300_ = lean_data_value_bool(v_x_299_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
}
}
uint8_t l_Lean_DataValue_sameCtor(lean_object* v_x_302_, lean_object* v_x_303_){
_start:
{
switch(lean_obj_tag(v_x_302_))
{
case 0:
{
if (lean_obj_tag(v_x_303_) == 0)
{
uint8_t v___x_304_; 
v___x_304_ = 1;
return v___x_304_;
}
else
{
uint8_t v___x_305_; 
v___x_305_ = 0;
return v___x_305_;
}
}
case 1:
{
if (lean_obj_tag(v_x_303_) == 1)
{
uint8_t v___x_306_; 
v___x_306_ = 1;
return v___x_306_;
}
else
{
uint8_t v___x_307_; 
v___x_307_ = 0;
return v___x_307_;
}
}
case 2:
{
if (lean_obj_tag(v_x_303_) == 2)
{
uint8_t v___x_308_; 
v___x_308_ = 1;
return v___x_308_;
}
else
{
uint8_t v___x_309_; 
v___x_309_ = 0;
return v___x_309_;
}
}
case 3:
{
if (lean_obj_tag(v_x_303_) == 3)
{
uint8_t v___x_310_; 
v___x_310_ = 1;
return v___x_310_;
}
else
{
uint8_t v___x_311_; 
v___x_311_ = 0;
return v___x_311_;
}
}
case 4:
{
if (lean_obj_tag(v_x_303_) == 4)
{
uint8_t v___x_312_; 
v___x_312_ = 1;
return v___x_312_;
}
else
{
uint8_t v___x_313_; 
v___x_313_ = 0;
return v___x_313_;
}
}
default: 
{
if (lean_obj_tag(v_x_303_) == 5)
{
uint8_t v___x_314_; 
v___x_314_ = 1;
return v___x_314_;
}
else
{
uint8_t v___x_315_; 
v___x_315_ = 0;
return v___x_315_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_DataValue_sameCtor_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_302_ = stack[0].m_obj;
lean_object* v_x_303_ = stack[1].m_obj;
uint8_t v_res_316_;
v_res_316_ = l_Lean_DataValue_sameCtor(v_x_302_, v_x_303_);
stack->m_num = v_res_316_;
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
LEAN_EXPORT lean_object* l_Lean_DataValue_str(lean_object* v_x_323_){
_start:
{
switch(lean_obj_tag(v_x_323_))
{
case 0:
{
lean_object* v_v_324_; 
v_v_324_ = lean_ctor_get(v_x_323_, 0);
lean_inc_ref(v_v_324_);
lean_dec_ref_known(v_x_323_, 1);
return v_v_324_;
}
case 1:
{
uint8_t v_v_325_; 
v_v_325_ = lean_ctor_get_uint8(v_x_323_, 0);
lean_dec_ref_known(v_x_323_, 0);
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
lean_dec_ref_known(v_x_323_, 1);
v___x_329_ = 1;
v___x_330_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_328_, v___x_329_);
return v___x_330_;
}
case 3:
{
lean_object* v_v_331_; lean_object* v___x_332_; 
v_v_331_ = lean_ctor_get(v_x_323_, 0);
lean_inc(v_v_331_);
lean_dec_ref_known(v_x_323_, 1);
v___x_332_ = l_Nat_reprFast(v_v_331_);
return v___x_332_;
}
case 4:
{
lean_object* v_v_333_; lean_object* v___x_334_; 
v_v_333_ = lean_ctor_get(v_x_323_, 0);
lean_inc(v_v_333_);
lean_dec_ref_known(v_x_323_, 1);
v___x_334_ = l_Int_repr(v_v_333_);
lean_dec(v_v_333_);
return v___x_334_;
}
default: 
{
lean_object* v_v_335_; lean_object* v___x_336_; uint8_t v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v_v_335_ = lean_ctor_get(v_x_323_, 0);
lean_inc(v_v_335_);
lean_dec_ref_known(v_x_323_, 1);
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
lean_object* l_Lean_instCoeBoolDataValue___lam__0(uint8_t v_v_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_349_, 0, v_v_348_);
return v___x_349_;
}
}
LEAN_EXPORT void l_Lean_instCoeBoolDataValue___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_v_348_ = stack[0].m_num;
lean_object* v_res_350_;
v_res_350_ = l_Lean_instCoeBoolDataValue___lam__0(v_v_348_);
stack->m_obj
 = v_res_350_;
}
LEAN_EXPORT lean_object* l_Lean_instCoeBoolDataValue___lam__0___boxed(lean_object* v_v_351_){
_start:
{
uint8_t v_v_boxed_352_; lean_object* v_res_353_; 
v_v_boxed_352_ = lean_unbox(v_v_351_);
v_res_353_ = l_Lean_instCoeBoolDataValue___lam__0(v_v_boxed_352_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeNameDataValue___lam__0(lean_object* v_v_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_357_, 0, v_v_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeNatDataValue___lam__0(lean_object* v_v_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_361_, 0, v_v_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeIntDataValue___lam__0(lean_object* v_v_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_365_, 0, v_v_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeSyntaxDataValue___lam__0(lean_object* v_v_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_369_, 0, v_v_368_);
return v___x_369_;
}
}
static lean_object* _init_l_Lean_instInhabitedKVMap_default(void){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = lean_box(0);
return v___x_372_;
}
}
static lean_object* _init_l_Lean_instInhabitedKVMap(void){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = lean_box(0);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprKVMap_repr_spec__1(lean_object* v_a_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = lean_nat_to_int(v_a_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_376_, lean_object* v_x_377_, lean_object* v_x_378_){
_start:
{
if (lean_obj_tag(v_x_378_) == 0)
{
lean_dec(v_x_376_);
return v_x_377_;
}
else
{
lean_object* v_head_379_; lean_object* v_tail_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_389_; 
v_head_379_ = lean_ctor_get(v_x_378_, 0);
v_tail_380_ = lean_ctor_get(v_x_378_, 1);
v_isSharedCheck_389_ = !lean_is_exclusive(v_x_378_);
if (v_isSharedCheck_389_ == 0)
{
v___x_382_ = v_x_378_;
v_isShared_383_ = v_isSharedCheck_389_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_tail_380_);
lean_inc(v_head_379_);
lean_dec(v_x_378_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_389_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
lean_inc(v_x_376_);
if (v_isShared_383_ == 0)
{
lean_ctor_set_tag(v___x_382_, 5);
lean_ctor_set(v___x_382_, 1, v_x_376_);
lean_ctor_set(v___x_382_, 0, v_x_377_);
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_x_377_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_x_376_);
v___x_385_ = v_reuseFailAlloc_388_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
lean_object* v___x_386_; 
v___x_386_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
lean_ctor_set(v___x_386_, 1, v_head_379_);
v_x_377_ = v___x_386_;
v_x_378_ = v_tail_380_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0_spec__2(lean_object* v_x_390_, lean_object* v_x_391_){
_start:
{
if (lean_obj_tag(v_x_390_) == 0)
{
lean_object* v___x_392_; 
lean_dec(v_x_391_);
v___x_392_ = lean_box(0);
return v___x_392_;
}
else
{
lean_object* v_tail_393_; 
v_tail_393_ = lean_ctor_get(v_x_390_, 1);
if (lean_obj_tag(v_tail_393_) == 0)
{
lean_object* v_head_394_; 
lean_dec(v_x_391_);
v_head_394_ = lean_ctor_get(v_x_390_, 0);
lean_inc(v_head_394_);
lean_dec_ref_known(v_x_390_, 2);
return v_head_394_;
}
else
{
lean_object* v_head_395_; lean_object* v___x_396_; 
lean_inc(v_tail_393_);
v_head_395_ = lean_ctor_get(v_x_390_, 0);
lean_inc(v_head_395_);
lean_dec_ref_known(v_x_390_, 2);
v___x_396_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0_spec__2_spec__3(v_x_391_, v_head_395_, v_tail_393_);
return v___x_396_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__0));
v___x_406_ = lean_string_length(v___x_405_);
return v___x_406_;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__5, &l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__5_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__5);
v___x_408_ = lean_nat_to_int(v___x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(lean_object* v_x_413_){
_start:
{
lean_object* v_fst_414_; lean_object* v_snd_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_438_; 
v_fst_414_ = lean_ctor_get(v_x_413_, 0);
v_snd_415_ = lean_ctor_get(v_x_413_, 1);
v_isSharedCheck_438_ = !lean_is_exclusive(v_x_413_);
if (v_isSharedCheck_438_ == 0)
{
v___x_417_ = v_x_413_;
v_isShared_418_ = v_isSharedCheck_438_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_snd_415_);
lean_inc(v_fst_414_);
lean_dec(v_x_413_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_438_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_419_ = lean_unsigned_to_nat(0u);
v___x_420_ = l_Lean_Name_reprPrec(v_fst_414_, v___x_419_);
v___x_421_ = lean_box(0);
if (v_isShared_418_ == 0)
{
lean_ctor_set_tag(v___x_417_, 1);
lean_ctor_set(v___x_417_, 1, v___x_421_);
lean_ctor_set(v___x_417_, 0, v___x_420_);
v___x_423_ = v___x_417_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_420_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v___x_421_);
v___x_423_ = v_reuseFailAlloc_437_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; uint8_t v___x_435_; lean_object* v___x_436_; 
v___x_424_ = l_Lean_instReprDataValue_repr(v_snd_415_, v___x_419_);
v___x_425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
lean_ctor_set(v___x_425_, 1, v___x_423_);
v___x_426_ = l_List_reverse___redArg(v___x_425_);
v___x_427_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__3));
v___x_428_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0_spec__2(v___x_426_, v___x_427_);
v___x_429_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__6, &l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__6_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__6);
v___x_430_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__7));
v___x_431_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
lean_ctor_set(v___x_431_, 1, v___x_428_);
v___x_432_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__8));
v___x_433_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_431_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
v___x_434_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_429_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
v___x_435_ = 0;
v___x_436_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_436_, 0, v___x_434_);
lean_ctor_set_uint8(v___x_436_, sizeof(void*)*1, v___x_435_);
return v___x_436_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1_spec__4_spec__6(lean_object* v_x_439_, lean_object* v_x_440_, lean_object* v_x_441_){
_start:
{
if (lean_obj_tag(v_x_441_) == 0)
{
lean_dec(v_x_439_);
return v_x_440_;
}
else
{
lean_object* v_head_442_; lean_object* v_tail_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_453_; 
v_head_442_ = lean_ctor_get(v_x_441_, 0);
v_tail_443_ = lean_ctor_get(v_x_441_, 1);
v_isSharedCheck_453_ = !lean_is_exclusive(v_x_441_);
if (v_isSharedCheck_453_ == 0)
{
v___x_445_ = v_x_441_;
v_isShared_446_ = v_isSharedCheck_453_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_tail_443_);
lean_inc(v_head_442_);
lean_dec(v_x_441_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_453_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
lean_inc(v_x_439_);
if (v_isShared_446_ == 0)
{
lean_ctor_set_tag(v___x_445_, 5);
lean_ctor_set(v___x_445_, 1, v_x_439_);
lean_ctor_set(v___x_445_, 0, v_x_440_);
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_x_440_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_x_439_);
v___x_448_ = v_reuseFailAlloc_452_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(v_head_442_);
v___x_450_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_450_, 0, v___x_448_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
v_x_440_ = v___x_450_;
v_x_441_ = v_tail_443_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1_spec__4(lean_object* v_x_454_, lean_object* v_x_455_, lean_object* v_x_456_){
_start:
{
if (lean_obj_tag(v_x_456_) == 0)
{
lean_dec(v_x_454_);
return v_x_455_;
}
else
{
lean_object* v_head_457_; lean_object* v_tail_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_468_; 
v_head_457_ = lean_ctor_get(v_x_456_, 0);
v_tail_458_ = lean_ctor_get(v_x_456_, 1);
v_isSharedCheck_468_ = !lean_is_exclusive(v_x_456_);
if (v_isSharedCheck_468_ == 0)
{
v___x_460_ = v_x_456_;
v_isShared_461_ = v_isSharedCheck_468_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_tail_458_);
lean_inc(v_head_457_);
lean_dec(v_x_456_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_468_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
lean_inc(v_x_454_);
if (v_isShared_461_ == 0)
{
lean_ctor_set_tag(v___x_460_, 5);
lean_ctor_set(v___x_460_, 1, v_x_454_);
lean_ctor_set(v___x_460_, 0, v_x_455_);
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_x_455_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v_x_454_);
v___x_463_ = v_reuseFailAlloc_467_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_464_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(v_head_457_);
v___x_465_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_463_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
v___x_466_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1_spec__4_spec__6(v_x_454_, v___x_465_, v_tail_458_);
return v___x_466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1(lean_object* v_x_469_, lean_object* v_x_470_){
_start:
{
if (lean_obj_tag(v_x_469_) == 0)
{
lean_object* v___x_471_; 
lean_dec(v_x_470_);
v___x_471_ = lean_box(0);
return v___x_471_;
}
else
{
lean_object* v_tail_472_; 
v_tail_472_ = lean_ctor_get(v_x_469_, 1);
if (lean_obj_tag(v_tail_472_) == 0)
{
lean_object* v_head_473_; lean_object* v___x_474_; 
lean_dec(v_x_470_);
v_head_473_ = lean_ctor_get(v_x_469_, 0);
lean_inc(v_head_473_);
lean_dec_ref_known(v_x_469_, 2);
v___x_474_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(v_head_473_);
return v___x_474_;
}
else
{
lean_object* v_head_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
lean_inc(v_tail_472_);
v_head_475_ = lean_ctor_get(v_x_469_, 0);
lean_inc(v_head_475_);
lean_dec_ref_known(v_x_469_, 2);
v___x_476_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(v_head_475_);
v___x_477_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1_spec__4(v_x_470_, v___x_476_, v_tail_472_);
return v___x_477_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = ((lean_object*)(l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__2));
v___x_484_ = lean_string_length(v___x_483_);
return v___x_484_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_obj_once(&l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__4, &l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__4_once, _init_l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__4);
v___x_486_ = lean_nat_to_int(v___x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg(lean_object* v_a_491_){
_start:
{
if (lean_obj_tag(v_a_491_) == 0)
{
lean_object* v___x_492_; 
v___x_492_ = ((lean_object*)(l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__1));
return v___x_492_;
}
else
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; lean_object* v___x_502_; 
v___x_493_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__3));
v___x_494_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1(v_a_491_, v___x_493_);
v___x_495_ = lean_obj_once(&l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__5, &l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__5_once, _init_l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__5);
v___x_496_ = ((lean_object*)(l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__6));
v___x_497_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
lean_ctor_set(v___x_497_, 1, v___x_494_);
v___x_498_ = ((lean_object*)(l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__7));
v___x_499_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_497_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
v___x_500_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_495_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
v___x_501_ = 0;
v___x_502_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_502_, 0, v___x_500_);
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*1, v___x_501_);
return v___x_502_;
}
}
}
static lean_object* _init_l_Lean_instReprKVMap_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_unsigned_to_nat(11u);
v___x_517_ = lean_nat_to_int(v___x_516_);
return v___x_517_;
}
}
static lean_object* _init_l_Lean_instReprKVMap_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = ((lean_object*)(l_Lean_instReprKVMap_repr___redArg___closed__0));
v___x_520_ = lean_string_length(v___x_519_);
return v___x_520_;
}
}
static lean_object* _init_l_Lean_instReprKVMap_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_obj_once(&l_Lean_instReprKVMap_repr___redArg___closed__9, &l_Lean_instReprKVMap_repr___redArg___closed__9_once, _init_l_Lean_instReprKVMap_repr___redArg___closed__9);
v___x_522_ = lean_nat_to_int(v___x_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprKVMap_repr___redArg(lean_object* v_x_527_){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; uint8_t v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_528_ = ((lean_object*)(l_Lean_instReprKVMap_repr___redArg___closed__6));
v___x_529_ = lean_obj_once(&l_Lean_instReprKVMap_repr___redArg___closed__7, &l_Lean_instReprKVMap_repr___redArg___closed__7_once, _init_l_Lean_instReprKVMap_repr___redArg___closed__7);
v___x_530_ = l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg(v_x_527_);
v___x_531_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_529_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = 0;
v___x_533_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_533_, 0, v___x_531_);
lean_ctor_set_uint8(v___x_533_, sizeof(void*)*1, v___x_532_);
v___x_534_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_528_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = lean_obj_once(&l_Lean_instReprKVMap_repr___redArg___closed__10, &l_Lean_instReprKVMap_repr___redArg___closed__10_once, _init_l_Lean_instReprKVMap_repr___redArg___closed__10);
v___x_536_ = ((lean_object*)(l_Lean_instReprKVMap_repr___redArg___closed__11));
v___x_537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
lean_ctor_set(v___x_537_, 1, v___x_534_);
v___x_538_ = ((lean_object*)(l_Lean_instReprKVMap_repr___redArg___closed__12));
v___x_539_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_537_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_535_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_541_, 0, v___x_540_);
lean_ctor_set_uint8(v___x_541_, sizeof(void*)*1, v___x_532_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprKVMap_repr(lean_object* v_x_542_, lean_object* v_prec_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Lean_instReprKVMap_repr___redArg(v_x_542_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprKVMap_repr___boxed(lean_object* v_x_545_, lean_object* v_prec_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_instReprKVMap_repr(v_x_545_, v_prec_546_);
lean_dec(v_prec_546_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprKVMap_repr_spec__0(lean_object* v_a_548_, lean_object* v_n_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg(v_a_548_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___boxed(lean_object* v_a_551_, lean_object* v_n_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_List_repr___at___00Lean_instReprKVMap_repr_spec__0(v_a_551_, v_n_552_);
lean_dec(v_n_552_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0(lean_object* v_x_554_, lean_object* v_x_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(v_x_554_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___boxed(lean_object* v_x_557_, lean_object* v_x_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0(v_x_557_, v_x_558_);
lean_dec(v_x_558_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instToString___lam__0(lean_object* v___f_562_, lean_object* v_m_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l_List_toString___redArg(v___f_562_, v_m_563_);
return v___x_564_;
}
}
static lean_object* _init_l_Lean_KVMap_empty(void){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = lean_box(0);
return v___x_572_;
}
}
uint8_t l_Lean_KVMap_isEmpty(lean_object* v_x_573_){
_start:
{
uint8_t v___x_574_; 
v___x_574_ = l_List_isEmpty___redArg(v_x_573_);
return v___x_574_;
}
}
LEAN_EXPORT void l_Lean_KVMap_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_573_ = stack[0].m_obj;
uint8_t v_res_575_;
v_res_575_ = l_Lean_KVMap_isEmpty(v_x_573_);
stack->m_num = v_res_575_;
}
LEAN_EXPORT lean_object* l_Lean_KVMap_isEmpty___boxed(lean_object* v_x_576_){
_start:
{
uint8_t v_res_577_; lean_object* v_r_578_; 
v_res_577_ = l_Lean_KVMap_isEmpty(v_x_576_);
lean_dec(v_x_576_);
v_r_578_ = lean_box(v_res_577_);
return v_r_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_size(lean_object* v_m_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_List_lengthTR___redArg(v_m_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_size___boxed(lean_object* v_m_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Lean_KVMap_size(v_m_581_);
lean_dec(v_m_581_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_findCore(lean_object* v_x_583_, lean_object* v_x_584_){
_start:
{
if (lean_obj_tag(v_x_583_) == 0)
{
lean_object* v___x_585_; 
v___x_585_ = lean_box(0);
return v___x_585_;
}
else
{
lean_object* v_head_586_; lean_object* v_tail_587_; lean_object* v_fst_588_; lean_object* v_snd_589_; uint8_t v___x_590_; 
v_head_586_ = lean_ctor_get(v_x_583_, 0);
v_tail_587_ = lean_ctor_get(v_x_583_, 1);
v_fst_588_ = lean_ctor_get(v_head_586_, 0);
v_snd_589_ = lean_ctor_get(v_head_586_, 1);
v___x_590_ = lean_name_eq(v_fst_588_, v_x_584_);
if (v___x_590_ == 0)
{
v_x_583_ = v_tail_587_;
goto _start;
}
else
{
lean_object* v___x_592_; 
lean_inc(v_snd_589_);
v___x_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_592_, 0, v_snd_589_);
return v___x_592_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_findCore___boxed(lean_object* v_x_593_, lean_object* v_x_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_KVMap_findCore(v_x_593_, v_x_594_);
lean_dec(v_x_594_);
lean_dec(v_x_593_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_find(lean_object* v_x_596_, lean_object* v_x_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_KVMap_findCore(v_x_596_, v_x_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_find___boxed(lean_object* v_x_599_, lean_object* v_x_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_KVMap_find(v_x_599_, v_x_600_);
lean_dec(v_x_600_);
lean_dec(v_x_599_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_findD(lean_object* v_m_602_, lean_object* v_k_603_, lean_object* v_d_u2080_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_KVMap_findCore(v_m_602_, v_k_603_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_inc_ref(v_d_u2080_604_);
return v_d_u2080_604_;
}
else
{
lean_object* v_val_606_; 
v_val_606_ = lean_ctor_get(v___x_605_, 0);
lean_inc(v_val_606_);
lean_dec_ref_known(v___x_605_, 1);
return v_val_606_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_findD___boxed(lean_object* v_m_607_, lean_object* v_k_608_, lean_object* v_d_u2080_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lean_KVMap_findD(v_m_607_, v_k_608_, v_d_u2080_609_);
lean_dec_ref(v_d_u2080_609_);
lean_dec(v_k_608_);
lean_dec(v_m_607_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_insertCore(lean_object* v_x_611_, lean_object* v_x_612_, lean_object* v_x_613_){
_start:
{
if (lean_obj_tag(v_x_611_) == 0)
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v_x_612_);
lean_ctor_set(v___x_614_, 1, v_x_613_);
v___x_615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
lean_ctor_set(v___x_615_, 1, v_x_611_);
return v___x_615_;
}
else
{
lean_object* v_head_616_; lean_object* v_tail_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_639_; 
v_head_616_ = lean_ctor_get(v_x_611_, 0);
v_tail_617_ = lean_ctor_get(v_x_611_, 1);
v_isSharedCheck_639_ = !lean_is_exclusive(v_x_611_);
if (v_isSharedCheck_639_ == 0)
{
v___x_619_ = v_x_611_;
v_isShared_620_ = v_isSharedCheck_639_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_tail_617_);
lean_inc(v_head_616_);
lean_dec(v_x_611_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_639_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v_fst_621_; uint8_t v___x_622_; 
v_fst_621_ = lean_ctor_get(v_head_616_, 0);
v___x_622_ = lean_name_eq(v_fst_621_, v_x_612_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v___x_625_; 
v___x_623_ = l_Lean_KVMap_insertCore(v_tail_617_, v_x_612_, v_x_613_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 1, v___x_623_);
v___x_625_ = v___x_619_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_head_616_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v___x_623_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
else
{
lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_636_; 
lean_inc(v_fst_621_);
lean_dec(v_x_612_);
v_isSharedCheck_636_ = !lean_is_exclusive(v_head_616_);
if (v_isSharedCheck_636_ == 0)
{
lean_object* v_unused_637_; lean_object* v_unused_638_; 
v_unused_637_ = lean_ctor_get(v_head_616_, 1);
lean_dec(v_unused_637_);
v_unused_638_ = lean_ctor_get(v_head_616_, 0);
lean_dec(v_unused_638_);
v___x_628_ = v_head_616_;
v_isShared_629_ = v_isSharedCheck_636_;
goto v_resetjp_627_;
}
else
{
lean_dec(v_head_616_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_636_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 1, v_x_613_);
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_fst_621_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v_x_613_);
v___x_631_ = v_reuseFailAlloc_635_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_633_; 
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v___x_631_);
v___x_633_ = v___x_619_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_631_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_tail_617_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_insert(lean_object* v_x_640_, lean_object* v_x_641_, lean_object* v_x_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Lean_KVMap_insertCore(v_x_640_, v_x_641_, v_x_642_);
return v___x_643_;
}
}
uint8_t l_Lean_KVMap_contains(lean_object* v_m_644_, lean_object* v_n_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Lean_KVMap_findCore(v_m_644_, v_n_645_);
if (lean_obj_tag(v___x_646_) == 0)
{
uint8_t v___x_647_; 
v___x_647_ = 0;
return v___x_647_;
}
else
{
uint8_t v___x_648_; 
lean_dec_ref_known(v___x_646_, 1);
v___x_648_ = 1;
return v___x_648_;
}
}
}
LEAN_EXPORT void l_Lean_KVMap_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_644_ = stack[0].m_obj;
lean_object* v_n_645_ = stack[1].m_obj;
uint8_t v_res_649_;
v_res_649_ = l_Lean_KVMap_contains(v_m_644_, v_n_645_);
stack->m_num = v_res_649_;
}
LEAN_EXPORT lean_object* l_Lean_KVMap_contains___boxed(lean_object* v_m_650_, lean_object* v_n_651_){
_start:
{
uint8_t v_res_652_; lean_object* v_r_653_; 
v_res_652_ = l_Lean_KVMap_contains(v_m_650_, v_n_651_);
lean_dec(v_n_651_);
lean_dec(v_m_650_);
v_r_653_ = lean_box(v_res_652_);
return v_r_653_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_KVMap_erase_spec__0(lean_object* v_x_654_, lean_object* v_a_655_, lean_object* v_a_656_){
_start:
{
if (lean_obj_tag(v_a_655_) == 0)
{
lean_object* v___x_657_; 
v___x_657_ = l_List_reverse___redArg(v_a_656_);
return v___x_657_;
}
else
{
lean_object* v_head_658_; lean_object* v_tail_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_670_; 
v_head_658_ = lean_ctor_get(v_a_655_, 0);
v_tail_659_ = lean_ctor_get(v_a_655_, 1);
v_isSharedCheck_670_ = !lean_is_exclusive(v_a_655_);
if (v_isSharedCheck_670_ == 0)
{
v___x_661_ = v_a_655_;
v_isShared_662_ = v_isSharedCheck_670_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_tail_659_);
lean_inc(v_head_658_);
lean_dec(v_a_655_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_670_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v_fst_663_; uint8_t v___x_664_; 
v_fst_663_ = lean_ctor_get(v_head_658_, 0);
v___x_664_ = lean_name_eq(v_fst_663_, v_x_654_);
if (v___x_664_ == 0)
{
lean_object* v___x_666_; 
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 1, v_a_656_);
v___x_666_ = v___x_661_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_head_658_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_a_656_);
v___x_666_ = v_reuseFailAlloc_668_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
v_a_655_ = v_tail_659_;
v_a_656_ = v___x_666_;
goto _start;
}
}
else
{
lean_del_object(v___x_661_);
lean_dec(v_head_658_);
v_a_655_ = v_tail_659_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_KVMap_erase_spec__0___boxed(lean_object* v_x_671_, lean_object* v_a_672_, lean_object* v_a_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_List_filterTR_loop___at___00Lean_KVMap_erase_spec__0(v_x_671_, v_a_672_, v_a_673_);
lean_dec(v_x_671_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_erase(lean_object* v_x_675_, lean_object* v_x_676_){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = lean_box(0);
v___x_678_ = l_List_filterTR_loop___at___00Lean_KVMap_erase_spec__0(v_x_676_, v_x_675_, v___x_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_erase___boxed(lean_object* v_x_679_, lean_object* v_x_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_KVMap_erase(v_x_679_, v_x_680_);
lean_dec(v_x_680_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getString(lean_object* v_m_682_, lean_object* v_k_683_, lean_object* v_defVal_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Lean_KVMap_findCore(v_m_682_, v_k_683_);
if (lean_obj_tag(v___x_685_) == 1)
{
lean_object* v_val_686_; 
v_val_686_ = lean_ctor_get(v___x_685_, 0);
lean_inc(v_val_686_);
lean_dec_ref_known(v___x_685_, 1);
if (lean_obj_tag(v_val_686_) == 0)
{
lean_object* v_v_687_; 
v_v_687_ = lean_ctor_get(v_val_686_, 0);
lean_inc_ref(v_v_687_);
lean_dec_ref_known(v_val_686_, 1);
return v_v_687_;
}
else
{
lean_dec(v_val_686_);
lean_inc_ref(v_defVal_684_);
return v_defVal_684_;
}
}
else
{
lean_dec(v___x_685_);
lean_inc_ref(v_defVal_684_);
return v_defVal_684_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getString___boxed(lean_object* v_m_688_, lean_object* v_k_689_, lean_object* v_defVal_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_KVMap_getString(v_m_688_, v_k_689_, v_defVal_690_);
lean_dec_ref(v_defVal_690_);
lean_dec(v_k_689_);
lean_dec(v_m_688_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getNat(lean_object* v_m_692_, lean_object* v_k_693_, lean_object* v_defVal_694_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_KVMap_findCore(v_m_692_, v_k_693_);
if (lean_obj_tag(v___x_695_) == 1)
{
lean_object* v_val_696_; 
v_val_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_val_696_);
lean_dec_ref_known(v___x_695_, 1);
if (lean_obj_tag(v_val_696_) == 3)
{
lean_object* v_v_697_; 
v_v_697_ = lean_ctor_get(v_val_696_, 0);
lean_inc(v_v_697_);
lean_dec_ref_known(v_val_696_, 1);
return v_v_697_;
}
else
{
lean_dec(v_val_696_);
lean_inc(v_defVal_694_);
return v_defVal_694_;
}
}
else
{
lean_dec(v___x_695_);
lean_inc(v_defVal_694_);
return v_defVal_694_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getNat___boxed(lean_object* v_m_698_, lean_object* v_k_699_, lean_object* v_defVal_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_KVMap_getNat(v_m_698_, v_k_699_, v_defVal_700_);
lean_dec(v_defVal_700_);
lean_dec(v_k_699_);
lean_dec(v_m_698_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getInt(lean_object* v_m_702_, lean_object* v_k_703_, lean_object* v_defVal_704_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l_Lean_KVMap_findCore(v_m_702_, v_k_703_);
if (lean_obj_tag(v___x_705_) == 1)
{
lean_object* v_val_706_; 
v_val_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_val_706_);
lean_dec_ref_known(v___x_705_, 1);
if (lean_obj_tag(v_val_706_) == 4)
{
lean_object* v_v_707_; 
v_v_707_ = lean_ctor_get(v_val_706_, 0);
lean_inc(v_v_707_);
lean_dec_ref_known(v_val_706_, 1);
return v_v_707_;
}
else
{
lean_dec(v_val_706_);
lean_inc(v_defVal_704_);
return v_defVal_704_;
}
}
else
{
lean_dec(v___x_705_);
lean_inc(v_defVal_704_);
return v_defVal_704_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getInt___boxed(lean_object* v_m_708_, lean_object* v_k_709_, lean_object* v_defVal_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_KVMap_getInt(v_m_708_, v_k_709_, v_defVal_710_);
lean_dec(v_defVal_710_);
lean_dec(v_k_709_);
lean_dec(v_m_708_);
return v_res_711_;
}
}
uint8_t l_Lean_KVMap_getBool(lean_object* v_m_712_, lean_object* v_k_713_, uint8_t v_defVal_714_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Lean_KVMap_findCore(v_m_712_, v_k_713_);
if (lean_obj_tag(v___x_715_) == 1)
{
lean_object* v_val_716_; 
v_val_716_ = lean_ctor_get(v___x_715_, 0);
lean_inc(v_val_716_);
lean_dec_ref_known(v___x_715_, 1);
if (lean_obj_tag(v_val_716_) == 1)
{
uint8_t v_v_717_; 
v_v_717_ = lean_ctor_get_uint8(v_val_716_, 0);
lean_dec_ref_known(v_val_716_, 0);
return v_v_717_;
}
else
{
lean_dec(v_val_716_);
return v_defVal_714_;
}
}
else
{
lean_dec(v___x_715_);
return v_defVal_714_;
}
}
}
LEAN_EXPORT void l_Lean_KVMap_getBool_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_712_ = stack[0].m_obj;
lean_object* v_k_713_ = stack[1].m_obj;
uint8_t v_defVal_714_ = stack[2].m_num;
uint8_t v_res_718_;
v_res_718_ = l_Lean_KVMap_getBool(v_m_712_, v_k_713_, v_defVal_714_);
stack->m_num = v_res_718_;
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getBool___boxed(lean_object* v_m_719_, lean_object* v_k_720_, lean_object* v_defVal_721_){
_start:
{
uint8_t v_defVal_boxed_722_; uint8_t v_res_723_; lean_object* v_r_724_; 
v_defVal_boxed_722_ = lean_unbox(v_defVal_721_);
v_res_723_ = l_Lean_KVMap_getBool(v_m_719_, v_k_720_, v_defVal_boxed_722_);
lean_dec(v_k_720_);
lean_dec(v_m_719_);
v_r_724_ = lean_box(v_res_723_);
return v_r_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getName(lean_object* v_m_725_, lean_object* v_k_726_, lean_object* v_defVal_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l_Lean_KVMap_findCore(v_m_725_, v_k_726_);
if (lean_obj_tag(v___x_728_) == 1)
{
lean_object* v_val_729_; 
v_val_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_val_729_);
lean_dec_ref_known(v___x_728_, 1);
if (lean_obj_tag(v_val_729_) == 2)
{
lean_object* v_v_730_; 
v_v_730_ = lean_ctor_get(v_val_729_, 0);
lean_inc(v_v_730_);
lean_dec_ref_known(v_val_729_, 1);
return v_v_730_;
}
else
{
lean_dec(v_val_729_);
lean_inc(v_defVal_727_);
return v_defVal_727_;
}
}
else
{
lean_dec(v___x_728_);
lean_inc(v_defVal_727_);
return v_defVal_727_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getName___boxed(lean_object* v_m_731_, lean_object* v_k_732_, lean_object* v_defVal_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_KVMap_getName(v_m_731_, v_k_732_, v_defVal_733_);
lean_dec(v_defVal_733_);
lean_dec(v_k_732_);
lean_dec(v_m_731_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getSyntax(lean_object* v_m_735_, lean_object* v_k_736_, lean_object* v_defVal_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_KVMap_findCore(v_m_735_, v_k_736_);
if (lean_obj_tag(v___x_738_) == 1)
{
lean_object* v_val_739_; 
v_val_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_val_739_);
lean_dec_ref_known(v___x_738_, 1);
if (lean_obj_tag(v_val_739_) == 5)
{
lean_object* v_v_740_; 
v_v_740_ = lean_ctor_get(v_val_739_, 0);
lean_inc(v_v_740_);
lean_dec_ref_known(v_val_739_, 1);
return v_v_740_;
}
else
{
lean_dec(v_val_739_);
lean_inc(v_defVal_737_);
return v_defVal_737_;
}
}
else
{
lean_dec(v___x_738_);
lean_inc(v_defVal_737_);
return v_defVal_737_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getSyntax___boxed(lean_object* v_m_741_, lean_object* v_k_742_, lean_object* v_defVal_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lean_KVMap_getSyntax(v_m_741_, v_k_742_, v_defVal_743_);
lean_dec(v_defVal_743_);
lean_dec(v_k_742_);
lean_dec(v_m_741_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_setString(lean_object* v_m_745_, lean_object* v_k_746_, lean_object* v_v_747_){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_748_, 0, v_v_747_);
v___x_749_ = l_Lean_KVMap_insertCore(v_m_745_, v_k_746_, v___x_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_setNat(lean_object* v_m_750_, lean_object* v_k_751_, lean_object* v_v_752_){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_753_, 0, v_v_752_);
v___x_754_ = l_Lean_KVMap_insertCore(v_m_750_, v_k_751_, v___x_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_setInt(lean_object* v_m_755_, lean_object* v_k_756_, lean_object* v_v_757_){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_758_, 0, v_v_757_);
v___x_759_ = l_Lean_KVMap_insertCore(v_m_755_, v_k_756_, v___x_758_);
return v___x_759_;
}
}
lean_object* l_Lean_KVMap_setBool(lean_object* v_m_760_, lean_object* v_k_761_, uint8_t v_v_762_){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_763_, 0, v_v_762_);
v___x_764_ = l_Lean_KVMap_insertCore(v_m_760_, v_k_761_, v___x_763_);
return v___x_764_;
}
}
LEAN_EXPORT void l_Lean_KVMap_setBool_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_760_ = stack[0].m_obj;
lean_object* v_k_761_ = stack[1].m_obj;
uint8_t v_v_762_ = stack[2].m_num;
lean_object* v_res_765_;
v_res_765_ = l_Lean_KVMap_setBool(v_m_760_, v_k_761_, v_v_762_);
stack->m_obj
 = v_res_765_;
}
LEAN_EXPORT lean_object* l_Lean_KVMap_setBool___boxed(lean_object* v_m_766_, lean_object* v_k_767_, lean_object* v_v_768_){
_start:
{
uint8_t v_v_boxed_769_; lean_object* v_res_770_; 
v_v_boxed_769_ = lean_unbox(v_v_768_);
v_res_770_ = l_Lean_KVMap_setBool(v_m_766_, v_k_767_, v_v_boxed_769_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_setName(lean_object* v_m_771_, lean_object* v_k_772_, lean_object* v_v_773_){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_774_, 0, v_v_773_);
v___x_775_ = l_Lean_KVMap_insertCore(v_m_771_, v_k_772_, v___x_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_setSyntax(lean_object* v_m_776_, lean_object* v_k_777_, lean_object* v_v_778_){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_779_, 0, v_v_778_);
v___x_780_ = l_Lean_KVMap_insertCore(v_m_776_, v_k_777_, v___x_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_updateString(lean_object* v_m_781_, lean_object* v_k_782_, lean_object* v_f_783_){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_784_ = ((lean_object*)(l_Lean_instInhabitedDataValue_default___closed__0));
v___x_785_ = l_Lean_KVMap_getString(v_m_781_, v_k_782_, v___x_784_);
v___x_786_ = lean_apply_1(v_f_783_, v___x_785_);
v___x_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
v___x_788_ = l_Lean_KVMap_insertCore(v_m_781_, v_k_782_, v___x_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_updateNat(lean_object* v_m_789_, lean_object* v_k_790_, lean_object* v_f_791_){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_792_ = lean_unsigned_to_nat(0u);
v___x_793_ = l_Lean_KVMap_getNat(v_m_789_, v_k_790_, v___x_792_);
v___x_794_ = lean_apply_1(v_f_791_, v___x_793_);
v___x_795_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
v___x_796_ = l_Lean_KVMap_insertCore(v_m_789_, v_k_790_, v___x_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_updateInt(lean_object* v_m_797_, lean_object* v_k_798_, lean_object* v_f_799_){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_800_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__17, &l_Lean_instReprDataValue_repr___closed__17_once, _init_l_Lean_instReprDataValue_repr___closed__17);
v___x_801_ = l_Lean_KVMap_getInt(v_m_797_, v_k_798_, v___x_800_);
v___x_802_ = lean_apply_1(v_f_799_, v___x_801_);
v___x_803_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
v___x_804_ = l_Lean_KVMap_insertCore(v_m_797_, v_k_798_, v___x_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_updateBool(lean_object* v_m_805_, lean_object* v_k_806_, lean_object* v_f_807_){
_start:
{
uint8_t v___x_808_; uint8_t v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; uint8_t v___x_813_; lean_object* v___x_814_; 
v___x_808_ = 0;
v___x_809_ = l_Lean_KVMap_getBool(v_m_805_, v_k_806_, v___x_808_);
v___x_810_ = lean_box(v___x_809_);
v___x_811_ = lean_apply_1(v_f_807_, v___x_810_);
v___x_812_ = lean_alloc_ctor(1, 0, 1);
v___x_813_ = lean_unbox(v___x_811_);
lean_ctor_set_uint8(v___x_812_, 0, v___x_813_);
v___x_814_ = l_Lean_KVMap_insertCore(v_m_805_, v_k_806_, v___x_812_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_updateName(lean_object* v_m_815_, lean_object* v_k_816_, lean_object* v_f_817_){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_818_ = lean_box(0);
v___x_819_ = l_Lean_KVMap_getName(v_m_815_, v_k_816_, v___x_818_);
v___x_820_ = lean_apply_1(v_f_817_, v___x_819_);
v___x_821_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
v___x_822_ = l_Lean_KVMap_insertCore(v_m_815_, v_k_816_, v___x_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_updateSyntax(lean_object* v_m_823_, lean_object* v_k_824_, lean_object* v_f_825_){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_826_ = lean_box(0);
v___x_827_ = l_Lean_KVMap_getSyntax(v_m_823_, v_k_824_, v___x_826_);
v___x_828_ = lean_apply_1(v_f_825_, v___x_827_);
v___x_829_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
v___x_830_ = l_Lean_KVMap_insertCore(v_m_823_, v_k_824_, v___x_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_forIn___redArg___lam__0(lean_object* v_f_831_, lean_object* v_a_832_, lean_object* v_x_833_, lean_object* v___y_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = lean_apply_2(v_f_831_, v_a_832_, v___y_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_forIn___redArg(lean_object* v_inst_836_, lean_object* v_kv_837_, lean_object* v_init_838_, lean_object* v_f_839_){
_start:
{
lean_object* v___f_840_; lean_object* v___x_841_; 
v___f_840_ = lean_alloc_closure((void*)(l_Lean_KVMap_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_840_, 0, v_f_839_);
v___x_841_ = l_List_forIn_x27_loop___redArg(v_inst_836_, v___f_840_, v_kv_837_, v_init_838_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_forIn___redArg___boxed(lean_object* v_inst_842_, lean_object* v_kv_843_, lean_object* v_init_844_, lean_object* v_f_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_KVMap_forIn___redArg(v_inst_842_, v_kv_843_, v_init_844_, v_f_845_);
lean_dec(v_kv_843_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_forIn(lean_object* v_00_u03b4_847_, lean_object* v_m_848_, lean_object* v_inst_849_, lean_object* v_kv_850_, lean_object* v_init_851_, lean_object* v_f_852_){
_start:
{
lean_object* v___f_853_; lean_object* v___x_854_; 
v___f_853_ = lean_alloc_closure((void*)(l_Lean_KVMap_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_853_, 0, v_f_852_);
v___x_854_ = l_List_forIn_x27_loop___redArg(v_inst_849_, v___f_853_, v_kv_850_, v_init_851_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_forIn___boxed(lean_object* v_00_u03b4_855_, lean_object* v_m_856_, lean_object* v_inst_857_, lean_object* v_kv_858_, lean_object* v_init_859_, lean_object* v_f_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lean_KVMap_forIn(v_00_u03b4_855_, v_m_856_, v_inst_857_, v_kv_858_, v_init_859_, v_f_860_);
lean_dec(v_kv_858_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__0(lean_object* v___y_862_, lean_object* v_a_863_, lean_object* v_x_864_, lean_object* v___y_865_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = lean_apply_2(v___y_862_, v_a_863_, v___y_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__1(lean_object* v_inst_867_, lean_object* v_00_u03b2_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v___f_872_; lean_object* v___x_873_; 
v___f_872_ = lean_alloc_closure((void*)(l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_872_, 0, v___y_871_);
v___x_873_ = l_List_forIn_x27_loop___redArg(v_inst_867_, v___f_872_, v___y_869_, v___y_870_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__1___boxed(lean_object* v_inst_874_, lean_object* v_00_u03b2_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__1(v_inst_874_, v_00_u03b2_875_, v___y_876_, v___y_877_, v___y_878_);
lean_dec(v___y_876_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg(lean_object* v_inst_880_){
_start:
{
lean_object* v___f_881_; 
v___f_881_ = lean_alloc_closure((void*)(l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__1___boxed), 5, 1);
lean_closure_set(v___f_881_, 0, v_inst_880_);
return v___f_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instForInProdNameDataValueOfMonad(lean_object* v_m_882_, lean_object* v_inst_883_){
_start:
{
lean_object* v___f_884_; 
v___f_884_ = lean_alloc_closure((void*)(l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__1___boxed), 5, 1);
lean_closure_set(v___f_884_, 0, v_inst_883_);
return v___f_884_;
}
}
uint8_t l_Lean_KVMap_subsetAux(lean_object* v_x_885_, lean_object* v_x_886_){
_start:
{
if (lean_obj_tag(v_x_885_) == 0)
{
uint8_t v___x_887_; 
v___x_887_ = 1;
return v___x_887_;
}
else
{
lean_object* v_head_888_; lean_object* v_tail_889_; lean_object* v_fst_890_; lean_object* v_snd_891_; lean_object* v___x_892_; 
v_head_888_ = lean_ctor_get(v_x_885_, 0);
v_tail_889_ = lean_ctor_get(v_x_885_, 1);
v_fst_890_ = lean_ctor_get(v_head_888_, 0);
v_snd_891_ = lean_ctor_get(v_head_888_, 1);
v___x_892_ = l_Lean_KVMap_findCore(v_x_886_, v_fst_890_);
if (lean_obj_tag(v___x_892_) == 0)
{
uint8_t v___x_893_; 
v___x_893_ = 0;
return v___x_893_;
}
else
{
lean_object* v_val_894_; uint8_t v___x_895_; 
v_val_894_ = lean_ctor_get(v___x_892_, 0);
lean_inc(v_val_894_);
lean_dec_ref_known(v___x_892_, 1);
v___x_895_ = l_Lean_instBEqDataValue_beq(v_snd_891_, v_val_894_);
lean_dec(v_val_894_);
if (v___x_895_ == 0)
{
return v___x_895_;
}
else
{
v_x_885_ = v_tail_889_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_Lean_KVMap_subsetAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_885_ = stack[0].m_obj;
lean_object* v_x_886_ = stack[1].m_obj;
uint8_t v_res_897_;
v_res_897_ = l_Lean_KVMap_subsetAux(v_x_885_, v_x_886_);
stack->m_num = v_res_897_;
}
LEAN_EXPORT lean_object* l_Lean_KVMap_subsetAux___boxed(lean_object* v_x_898_, lean_object* v_x_899_){
_start:
{
uint8_t v_res_900_; lean_object* v_r_901_; 
v_res_900_ = l_Lean_KVMap_subsetAux(v_x_898_, v_x_899_);
lean_dec(v_x_899_);
lean_dec(v_x_898_);
v_r_901_ = lean_box(v_res_900_);
return v_r_901_;
}
}
uint8_t l_Lean_KVMap_subset(lean_object* v_x_902_, lean_object* v_x_903_){
_start:
{
uint8_t v___x_904_; 
v___x_904_ = l_Lean_KVMap_subsetAux(v_x_902_, v_x_903_);
return v___x_904_;
}
}
LEAN_EXPORT void l_Lean_KVMap_subset_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_902_ = stack[0].m_obj;
lean_object* v_x_903_ = stack[1].m_obj;
uint8_t v_res_905_;
v_res_905_ = l_Lean_KVMap_subset(v_x_902_, v_x_903_);
stack->m_num = v_res_905_;
}
LEAN_EXPORT lean_object* l_Lean_KVMap_subset___boxed(lean_object* v_x_906_, lean_object* v_x_907_){
_start:
{
uint8_t v_res_908_; lean_object* v_r_909_; 
v_res_908_ = l_Lean_KVMap_subset(v_x_906_, v_x_907_);
lean_dec(v_x_907_);
lean_dec(v_x_906_);
v_r_909_ = lean_box(v_res_908_);
return v_r_909_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___redArg(lean_object* v_mergeFn_910_, lean_object* v_as_x27_911_, lean_object* v_b_912_){
_start:
{
if (lean_obj_tag(v_as_x27_911_) == 0)
{
lean_dec_ref(v_mergeFn_910_);
return v_b_912_;
}
else
{
lean_object* v_head_913_; lean_object* v_tail_914_; lean_object* v_fst_915_; lean_object* v_snd_916_; lean_object* v___x_917_; 
v_head_913_ = lean_ctor_get(v_as_x27_911_, 0);
v_tail_914_ = lean_ctor_get(v_as_x27_911_, 1);
v_fst_915_ = lean_ctor_get(v_head_913_, 0);
v_snd_916_ = lean_ctor_get(v_head_913_, 1);
v___x_917_ = l_Lean_KVMap_findCore(v_b_912_, v_fst_915_);
if (lean_obj_tag(v___x_917_) == 1)
{
lean_object* v_val_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v_val_918_ = lean_ctor_get(v___x_917_, 0);
lean_inc(v_val_918_);
lean_dec_ref_known(v___x_917_, 1);
lean_inc_ref(v_mergeFn_910_);
lean_inc(v_snd_916_);
lean_inc_n(v_fst_915_, 2);
v___x_919_ = lean_apply_3(v_mergeFn_910_, v_fst_915_, v_val_918_, v_snd_916_);
v___x_920_ = l_Lean_KVMap_insertCore(v_b_912_, v_fst_915_, v___x_919_);
v_as_x27_911_ = v_tail_914_;
v_b_912_ = v___x_920_;
goto _start;
}
else
{
lean_object* v___x_922_; 
lean_dec(v___x_917_);
lean_inc(v_snd_916_);
lean_inc(v_fst_915_);
v___x_922_ = l_Lean_KVMap_insertCore(v_b_912_, v_fst_915_, v_snd_916_);
v_as_x27_911_ = v_tail_914_;
v_b_912_ = v___x_922_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___redArg___boxed(lean_object* v_mergeFn_924_, lean_object* v_as_x27_925_, lean_object* v_b_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___redArg(v_mergeFn_924_, v_as_x27_925_, v_b_926_);
lean_dec(v_as_x27_925_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_mergeBy(lean_object* v_mergeFn_928_, lean_object* v_l_929_, lean_object* v_r_930_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___redArg(v_mergeFn_928_, v_r_930_, v_l_929_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_mergeBy___boxed(lean_object* v_mergeFn_932_, lean_object* v_l_933_, lean_object* v_r_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Lean_KVMap_mergeBy(v_mergeFn_932_, v_l_933_, v_r_934_);
lean_dec(v_r_934_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0(lean_object* v_mergeFn_936_, lean_object* v_as_937_, lean_object* v_as_x27_938_, lean_object* v_b_939_, lean_object* v_a_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___redArg(v_mergeFn_936_, v_as_x27_938_, v_b_939_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___boxed(lean_object* v_mergeFn_942_, lean_object* v_as_943_, lean_object* v_as_x27_944_, lean_object* v_b_945_, lean_object* v_a_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0(v_mergeFn_942_, v_as_943_, v_as_x27_944_, v_b_945_, v_a_946_);
lean_dec(v_as_x27_944_);
lean_dec(v_as_943_);
return v_res_947_;
}
}
uint8_t l_Lean_KVMap_eqv(lean_object* v_m_u2081_948_, lean_object* v_m_u2082_949_){
_start:
{
uint8_t v___x_950_; 
v___x_950_ = l_Lean_KVMap_subsetAux(v_m_u2081_948_, v_m_u2082_949_);
if (v___x_950_ == 0)
{
return v___x_950_;
}
else
{
uint8_t v___x_951_; 
v___x_951_ = l_Lean_KVMap_subsetAux(v_m_u2082_949_, v_m_u2081_948_);
return v___x_951_;
}
}
}
LEAN_EXPORT void l_Lean_KVMap_eqv_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_u2081_948_ = stack[0].m_obj;
lean_object* v_m_u2082_949_ = stack[1].m_obj;
uint8_t v_res_952_;
v_res_952_ = l_Lean_KVMap_eqv(v_m_u2081_948_, v_m_u2082_949_);
stack->m_num = v_res_952_;
}
LEAN_EXPORT lean_object* l_Lean_KVMap_eqv___boxed(lean_object* v_m_u2081_953_, lean_object* v_m_u2082_954_){
_start:
{
uint8_t v_res_955_; lean_object* v_r_956_; 
v_res_955_ = l_Lean_KVMap_eqv(v_m_u2081_953_, v_m_u2082_954_);
lean_dec(v_m_u2082_954_);
lean_dec(v_m_u2081_953_);
v_r_956_ = lean_box(v_res_955_);
return v_r_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_get_x3f___redArg(lean_object* v_inst_959_, lean_object* v_m_960_, lean_object* v_k_961_){
_start:
{
lean_object* v_ofDataValue_x3f_962_; lean_object* v___x_963_; 
v_ofDataValue_x3f_962_ = lean_ctor_get(v_inst_959_, 1);
lean_inc_ref(v_ofDataValue_x3f_962_);
lean_dec_ref(v_inst_959_);
v___x_963_ = l_Lean_KVMap_findCore(v_m_960_, v_k_961_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v___x_964_; 
lean_dec_ref(v_ofDataValue_x3f_962_);
v___x_964_ = lean_box(0);
return v___x_964_;
}
else
{
lean_object* v_val_965_; lean_object* v___x_966_; 
v_val_965_ = lean_ctor_get(v___x_963_, 0);
lean_inc(v_val_965_);
lean_dec_ref_known(v___x_963_, 1);
v___x_966_ = lean_apply_1(v_ofDataValue_x3f_962_, v_val_965_);
return v___x_966_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_get_x3f___redArg___boxed(lean_object* v_inst_967_, lean_object* v_m_968_, lean_object* v_k_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Lean_KVMap_get_x3f___redArg(v_inst_967_, v_m_968_, v_k_969_);
lean_dec(v_k_969_);
lean_dec(v_m_968_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_get_x3f(lean_object* v_00_u03b1_971_, lean_object* v_inst_972_, lean_object* v_m_973_, lean_object* v_k_974_){
_start:
{
lean_object* v_ofDataValue_x3f_975_; lean_object* v___x_976_; 
v_ofDataValue_x3f_975_ = lean_ctor_get(v_inst_972_, 1);
lean_inc_ref(v_ofDataValue_x3f_975_);
lean_dec_ref(v_inst_972_);
v___x_976_ = l_Lean_KVMap_findCore(v_m_973_, v_k_974_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v___x_977_; 
lean_dec_ref(v_ofDataValue_x3f_975_);
v___x_977_ = lean_box(0);
return v___x_977_;
}
else
{
lean_object* v_val_978_; lean_object* v___x_979_; 
v_val_978_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_val_978_);
lean_dec_ref_known(v___x_976_, 1);
v___x_979_ = lean_apply_1(v_ofDataValue_x3f_975_, v_val_978_);
return v___x_979_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_get_x3f___boxed(lean_object* v_00_u03b1_980_, lean_object* v_inst_981_, lean_object* v_m_982_, lean_object* v_k_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_KVMap_get_x3f(v_00_u03b1_980_, v_inst_981_, v_m_982_, v_k_983_);
lean_dec(v_k_983_);
lean_dec(v_m_982_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_get___redArg(lean_object* v_inst_985_, lean_object* v_m_986_, lean_object* v_k_987_, lean_object* v_defVal_988_){
_start:
{
lean_object* v_ofDataValue_x3f_989_; lean_object* v___x_990_; 
v_ofDataValue_x3f_989_ = lean_ctor_get(v_inst_985_, 1);
lean_inc_ref(v_ofDataValue_x3f_989_);
lean_dec_ref(v_inst_985_);
v___x_990_ = l_Lean_KVMap_findCore(v_m_986_, v_k_987_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_dec_ref(v_ofDataValue_x3f_989_);
lean_inc(v_defVal_988_);
return v_defVal_988_;
}
else
{
lean_object* v_val_991_; lean_object* v___x_992_; 
v_val_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_val_991_);
lean_dec_ref_known(v___x_990_, 1);
v___x_992_ = lean_apply_1(v_ofDataValue_x3f_989_, v_val_991_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_inc(v_defVal_988_);
return v_defVal_988_;
}
else
{
lean_object* v_val_993_; 
v_val_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_val_993_);
lean_dec_ref_known(v___x_992_, 1);
return v_val_993_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_get___redArg___boxed(lean_object* v_inst_994_, lean_object* v_m_995_, lean_object* v_k_996_, lean_object* v_defVal_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lean_KVMap_get___redArg(v_inst_994_, v_m_995_, v_k_996_, v_defVal_997_);
lean_dec(v_defVal_997_);
lean_dec(v_k_996_);
lean_dec(v_m_995_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_get(lean_object* v_00_u03b1_999_, lean_object* v_inst_1000_, lean_object* v_m_1001_, lean_object* v_k_1002_, lean_object* v_defVal_1003_){
_start:
{
lean_object* v_ofDataValue_x3f_1004_; lean_object* v___x_1005_; 
v_ofDataValue_x3f_1004_ = lean_ctor_get(v_inst_1000_, 1);
lean_inc_ref(v_ofDataValue_x3f_1004_);
lean_dec_ref(v_inst_1000_);
v___x_1005_ = l_Lean_KVMap_findCore(v_m_1001_, v_k_1002_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_dec_ref(v_ofDataValue_x3f_1004_);
lean_inc(v_defVal_1003_);
return v_defVal_1003_;
}
else
{
lean_object* v_val_1006_; lean_object* v___x_1007_; 
v_val_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_val_1006_);
lean_dec_ref_known(v___x_1005_, 1);
v___x_1007_ = lean_apply_1(v_ofDataValue_x3f_1004_, v_val_1006_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_inc(v_defVal_1003_);
return v_defVal_1003_;
}
else
{
lean_object* v_val_1008_; 
v_val_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_val_1008_);
lean_dec_ref_known(v___x_1007_, 1);
return v_val_1008_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_get___boxed(lean_object* v_00_u03b1_1009_, lean_object* v_inst_1010_, lean_object* v_m_1011_, lean_object* v_k_1012_, lean_object* v_defVal_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Lean_KVMap_get(v_00_u03b1_1009_, v_inst_1010_, v_m_1011_, v_k_1012_, v_defVal_1013_);
lean_dec(v_defVal_1013_);
lean_dec(v_k_1012_);
lean_dec(v_m_1011_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_set___redArg(lean_object* v_inst_1015_, lean_object* v_m_1016_, lean_object* v_k_1017_, lean_object* v_v_1018_){
_start:
{
lean_object* v_toDataValue_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v_toDataValue_1019_ = lean_ctor_get(v_inst_1015_, 0);
lean_inc_ref(v_toDataValue_1019_);
lean_dec_ref(v_inst_1015_);
v___x_1020_ = lean_apply_1(v_toDataValue_1019_, v_v_1018_);
v___x_1021_ = l_Lean_KVMap_insertCore(v_m_1016_, v_k_1017_, v___x_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_set(lean_object* v_00_u03b1_1022_, lean_object* v_inst_1023_, lean_object* v_m_1024_, lean_object* v_k_1025_, lean_object* v_v_1026_){
_start:
{
lean_object* v_toDataValue_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v_toDataValue_1027_ = lean_ctor_get(v_inst_1023_, 0);
lean_inc_ref(v_toDataValue_1027_);
lean_dec_ref(v_inst_1023_);
v___x_1028_ = lean_apply_1(v_toDataValue_1027_, v_v_1026_);
v___x_1029_ = l_Lean_KVMap_insertCore(v_m_1024_, v_k_1025_, v___x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_update___redArg(lean_object* v_inst_1030_, lean_object* v_m_1031_, lean_object* v_k_1032_, lean_object* v_f_1033_){
_start:
{
lean_object* v_toDataValue_1034_; lean_object* v_ofDataValue_x3f_1035_; lean_object* v___y_1037_; lean_object* v___x_1043_; 
v_toDataValue_1034_ = lean_ctor_get(v_inst_1030_, 0);
lean_inc_ref(v_toDataValue_1034_);
v_ofDataValue_x3f_1035_ = lean_ctor_get(v_inst_1030_, 1);
lean_inc_ref(v_ofDataValue_x3f_1035_);
lean_dec_ref(v_inst_1030_);
v___x_1043_ = l_Lean_KVMap_findCore(v_m_1031_, v_k_1032_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v___x_1044_; 
lean_dec_ref(v_ofDataValue_x3f_1035_);
v___x_1044_ = lean_box(0);
v___y_1037_ = v___x_1044_;
goto v___jp_1036_;
}
else
{
lean_object* v_val_1045_; lean_object* v___x_1046_; 
v_val_1045_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_val_1045_);
lean_dec_ref_known(v___x_1043_, 1);
v___x_1046_ = lean_apply_1(v_ofDataValue_x3f_1035_, v_val_1045_);
v___y_1037_ = v___x_1046_;
goto v___jp_1036_;
}
v___jp_1036_:
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_apply_1(v_f_1033_, v___y_1037_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v___x_1039_; 
lean_dec_ref(v_toDataValue_1034_);
v___x_1039_ = l_Lean_KVMap_erase(v_m_1031_, v_k_1032_);
lean_dec(v_k_1032_);
return v___x_1039_;
}
else
{
lean_object* v_val_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v_val_1040_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_val_1040_);
lean_dec_ref_known(v___x_1038_, 1);
v___x_1041_ = lean_apply_1(v_toDataValue_1034_, v_val_1040_);
v___x_1042_ = l_Lean_KVMap_insertCore(v_m_1031_, v_k_1032_, v___x_1041_);
return v___x_1042_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_update(lean_object* v_00_u03b1_1047_, lean_object* v_inst_1048_, lean_object* v_m_1049_, lean_object* v_k_1050_, lean_object* v_f_1051_){
_start:
{
lean_object* v_toDataValue_1052_; lean_object* v_ofDataValue_x3f_1053_; lean_object* v___y_1055_; lean_object* v___x_1061_; 
v_toDataValue_1052_ = lean_ctor_get(v_inst_1048_, 0);
lean_inc_ref(v_toDataValue_1052_);
v_ofDataValue_x3f_1053_ = lean_ctor_get(v_inst_1048_, 1);
lean_inc_ref(v_ofDataValue_x3f_1053_);
lean_dec_ref(v_inst_1048_);
v___x_1061_ = l_Lean_KVMap_findCore(v_m_1049_, v_k_1050_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v___x_1062_; 
lean_dec_ref(v_ofDataValue_x3f_1053_);
v___x_1062_ = lean_box(0);
v___y_1055_ = v___x_1062_;
goto v___jp_1054_;
}
else
{
lean_object* v_val_1063_; lean_object* v___x_1064_; 
v_val_1063_ = lean_ctor_get(v___x_1061_, 0);
lean_inc(v_val_1063_);
lean_dec_ref_known(v___x_1061_, 1);
v___x_1064_ = lean_apply_1(v_ofDataValue_x3f_1053_, v_val_1063_);
v___y_1055_ = v___x_1064_;
goto v___jp_1054_;
}
v___jp_1054_:
{
lean_object* v___x_1056_; 
v___x_1056_ = lean_apply_1(v_f_1051_, v___y_1055_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v___x_1057_; 
lean_dec_ref(v_toDataValue_1052_);
v___x_1057_ = l_Lean_KVMap_erase(v_m_1049_, v_k_1050_);
lean_dec(v_k_1050_);
return v___x_1057_;
}
else
{
lean_object* v_val_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v_val_1058_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_val_1058_);
lean_dec_ref_known(v___x_1056_, 1);
v___x_1059_ = lean_apply_1(v_toDataValue_1052_, v_val_1058_);
v___x_1060_ = l_Lean_KVMap_insertCore(v_m_1049_, v_k_1050_, v___x_1059_);
return v___x_1060_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueDataValue___lam__0(lean_object* v_val_1065_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1066_, 0, v_val_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueBool___lam__1(lean_object* v_x_1073_){
_start:
{
if (lean_obj_tag(v_x_1073_) == 1)
{
uint8_t v_v_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v_v_1074_ = lean_ctor_get_uint8(v_x_1073_, 0);
v___x_1075_ = lean_box(v_v_1074_);
v___x_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
return v___x_1076_;
}
else
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_box(0);
return v___x_1077_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueBool___lam__1___boxed(lean_object* v_x_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_KVMap_instValueBool___lam__1(v_x_1078_);
lean_dec_ref(v_x_1078_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueNat___lam__1(lean_object* v_x_1085_){
_start:
{
if (lean_obj_tag(v_x_1085_) == 3)
{
lean_object* v_v_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
v_v_1086_ = lean_ctor_get(v_x_1085_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_x_1085_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v_x_1085_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_v_1086_);
lean_dec(v_x_1085_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
lean_ctor_set_tag(v___x_1088_, 1);
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_v_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
else
{
lean_object* v___x_1094_; 
lean_dec_ref(v_x_1085_);
v___x_1094_ = lean_box(0);
return v___x_1094_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueInt___lam__1(lean_object* v_x_1100_){
_start:
{
if (lean_obj_tag(v_x_1100_) == 4)
{
lean_object* v_v_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
v_v_1101_ = lean_ctor_get(v_x_1100_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v_x_1100_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v_x_1100_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_v_1101_);
lean_dec(v_x_1100_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
lean_ctor_set_tag(v___x_1103_, 1);
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_v_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
else
{
lean_object* v___x_1109_; 
lean_dec_ref(v_x_1100_);
v___x_1109_ = lean_box(0);
return v___x_1109_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueName___lam__1(lean_object* v_x_1115_){
_start:
{
if (lean_obj_tag(v_x_1115_) == 2)
{
lean_object* v_v_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
v_v_1116_ = lean_ctor_get(v_x_1115_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v_x_1115_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v_x_1115_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_v_1116_);
lean_dec(v_x_1115_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
lean_ctor_set_tag(v___x_1118_, 1);
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_v_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
else
{
lean_object* v___x_1124_; 
lean_dec_ref(v_x_1115_);
v___x_1124_ = lean_box(0);
return v___x_1124_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueString___lam__1(lean_object* v_x_1130_){
_start:
{
if (lean_obj_tag(v_x_1130_) == 0)
{
lean_object* v_v_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
v_v_1131_ = lean_ctor_get(v_x_1130_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v_x_1130_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v_x_1130_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_v_1131_);
lean_dec(v_x_1130_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
lean_ctor_set_tag(v___x_1133_, 1);
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_v_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
else
{
lean_object* v___x_1139_; 
lean_dec_ref(v_x_1130_);
v___x_1139_ = lean_box(0);
return v___x_1139_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueSyntax___lam__1(lean_object* v_x_1145_){
_start:
{
if (lean_obj_tag(v_x_1145_) == 5)
{
lean_object* v_v_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
v_v_1146_ = lean_ctor_get(v_x_1145_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_x_1145_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v_x_1145_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_v_1146_);
lean_dec(v_x_1145_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set_tag(v___x_1148_, 1);
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_v_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
else
{
lean_object* v___x_1154_; 
lean_dec_ref(v_x_1145_);
v___x_1154_ = lean_box(0);
return v___x_1154_;
}
}
}
lean_object* runtime_initialize_Init_Data_Format_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Name(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Extra(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_KVMap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

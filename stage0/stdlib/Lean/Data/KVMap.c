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
LEAN_EXPORT uint8_t l_Lean_instBEqDataValue_beq(lean_object* v_x_79_, lean_object* v_x_80_){
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
LEAN_EXPORT lean_object* l_Lean_instBEqDataValue_beq___boxed(lean_object* v_x_106_, lean_object* v_x_107_){
_start:
{
uint8_t v_res_108_; lean_object* v_r_109_; 
v_res_108_ = l_Lean_instBEqDataValue_beq(v_x_106_, v_x_107_);
lean_dec_ref(v_x_107_);
lean_dec_ref(v_x_106_);
v_r_109_ = lean_box(v_res_108_);
return v_r_109_;
}
}
static lean_object* _init_l_Lean_instReprDataValue_repr___closed__3(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = lean_unsigned_to_nat(2u);
v___x_119_ = lean_nat_to_int(v___x_118_);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_instReprDataValue_repr___closed__4(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = lean_unsigned_to_nat(1u);
v___x_121_ = lean_nat_to_int(v___x_120_);
return v___x_121_;
}
}
static lean_object* _init_l_Lean_instReprDataValue_repr___closed__17(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = lean_unsigned_to_nat(0u);
v___x_147_ = lean_nat_to_int(v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprDataValue_repr(lean_object* v_x_154_, lean_object* v_prec_155_){
_start:
{
lean_object* v___y_157_; lean_object* v___y_158_; lean_object* v___y_159_; 
switch(lean_obj_tag(v_x_154_))
{
case 0:
{
lean_object* v_v_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_185_; 
v_v_165_ = lean_ctor_get(v_x_154_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v_x_154_);
if (v_isSharedCheck_185_ == 0)
{
v___x_167_ = v_x_154_;
v_isShared_168_ = v_isSharedCheck_185_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_v_165_);
lean_dec(v_x_154_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_185_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___y_170_; lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_181_ = lean_unsigned_to_nat(1024u);
v___x_182_ = lean_nat_dec_le(v___x_181_, v_prec_155_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; 
v___x_183_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__3, &l_Lean_instReprDataValue_repr___closed__3_once, _init_l_Lean_instReprDataValue_repr___closed__3);
v___y_170_ = v___x_183_;
goto v___jp_169_;
}
else
{
lean_object* v___x_184_; 
v___x_184_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__4, &l_Lean_instReprDataValue_repr___closed__4_once, _init_l_Lean_instReprDataValue_repr___closed__4);
v___y_170_ = v___x_184_;
goto v___jp_169_;
}
v___jp_169_:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_174_; 
v___x_171_ = ((lean_object*)(l_Lean_instReprDataValue_repr___closed__2));
v___x_172_ = l_String_quote(v_v_165_);
if (v_isShared_168_ == 0)
{
lean_ctor_set_tag(v___x_167_, 3);
lean_ctor_set(v___x_167_, 0, v___x_172_);
v___x_174_ = v___x_167_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_172_);
v___x_174_ = v_reuseFailAlloc_180_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
lean_object* v___x_175_; lean_object* v___x_176_; uint8_t v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_175_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_171_);
lean_ctor_set(v___x_175_, 1, v___x_174_);
lean_inc(v___y_170_);
v___x_176_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_176_, 0, v___y_170_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
v___x_177_ = 0;
v___x_178_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_178_, 0, v___x_176_);
lean_ctor_set_uint8(v___x_178_, sizeof(void*)*1, v___x_177_);
v___x_179_ = l_Repr_addAppParen(v___x_178_, v_prec_155_);
return v___x_179_;
}
}
}
}
case 1:
{
uint8_t v_v_186_; lean_object* v___y_188_; lean_object* v___x_196_; uint8_t v___x_197_; 
v_v_186_ = lean_ctor_get_uint8(v_x_154_, 0);
lean_dec_ref_known(v_x_154_, 0);
v___x_196_ = lean_unsigned_to_nat(1024u);
v___x_197_ = lean_nat_dec_le(v___x_196_, v_prec_155_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; 
v___x_198_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__3, &l_Lean_instReprDataValue_repr___closed__3_once, _init_l_Lean_instReprDataValue_repr___closed__3);
v___y_188_ = v___x_198_;
goto v___jp_187_;
}
else
{
lean_object* v___x_199_; 
v___x_199_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__4, &l_Lean_instReprDataValue_repr___closed__4_once, _init_l_Lean_instReprDataValue_repr___closed__4);
v___y_188_ = v___x_199_;
goto v___jp_187_;
}
v___jp_187_:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_189_ = ((lean_object*)(l_Lean_instReprDataValue_repr___closed__7));
v___x_190_ = l_Bool_repr___redArg(v_v_186_);
v___x_191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_189_);
lean_ctor_set(v___x_191_, 1, v___x_190_);
lean_inc(v___y_188_);
v___x_192_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_192_, 0, v___y_188_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
v___x_193_ = 0;
v___x_194_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_194_, 0, v___x_192_);
lean_ctor_set_uint8(v___x_194_, sizeof(void*)*1, v___x_193_);
v___x_195_ = l_Repr_addAppParen(v___x_194_, v_prec_155_);
return v___x_195_;
}
}
case 2:
{
lean_object* v_v_200_; lean_object* v___y_202_; lean_object* v___x_211_; uint8_t v___x_212_; 
v_v_200_ = lean_ctor_get(v_x_154_, 0);
lean_inc(v_v_200_);
lean_dec_ref_known(v_x_154_, 1);
v___x_211_ = lean_unsigned_to_nat(1024u);
v___x_212_ = lean_nat_dec_le(v___x_211_, v_prec_155_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; 
v___x_213_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__3, &l_Lean_instReprDataValue_repr___closed__3_once, _init_l_Lean_instReprDataValue_repr___closed__3);
v___y_202_ = v___x_213_;
goto v___jp_201_;
}
else
{
lean_object* v___x_214_; 
v___x_214_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__4, &l_Lean_instReprDataValue_repr___closed__4_once, _init_l_Lean_instReprDataValue_repr___closed__4);
v___y_202_ = v___x_214_;
goto v___jp_201_;
}
v___jp_201_:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_203_ = ((lean_object*)(l_Lean_instReprDataValue_repr___closed__10));
v___x_204_ = lean_unsigned_to_nat(1024u);
v___x_205_ = l_Lean_Name_reprPrec(v_v_200_, v___x_204_);
v___x_206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_203_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
lean_inc(v___y_202_);
v___x_207_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_207_, 0, v___y_202_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
v___x_208_ = 0;
v___x_209_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_209_, 0, v___x_207_);
lean_ctor_set_uint8(v___x_209_, sizeof(void*)*1, v___x_208_);
v___x_210_ = l_Repr_addAppParen(v___x_209_, v_prec_155_);
return v___x_210_;
}
}
case 3:
{
lean_object* v_v_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_235_; 
v_v_215_ = lean_ctor_get(v_x_154_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v_x_154_);
if (v_isSharedCheck_235_ == 0)
{
v___x_217_ = v_x_154_;
v_isShared_218_ = v_isSharedCheck_235_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_v_215_);
lean_dec(v_x_154_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_235_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___y_220_; lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_231_ = lean_unsigned_to_nat(1024u);
v___x_232_ = lean_nat_dec_le(v___x_231_, v_prec_155_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; 
v___x_233_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__3, &l_Lean_instReprDataValue_repr___closed__3_once, _init_l_Lean_instReprDataValue_repr___closed__3);
v___y_220_ = v___x_233_;
goto v___jp_219_;
}
else
{
lean_object* v___x_234_; 
v___x_234_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__4, &l_Lean_instReprDataValue_repr___closed__4_once, _init_l_Lean_instReprDataValue_repr___closed__4);
v___y_220_ = v___x_234_;
goto v___jp_219_;
}
v___jp_219_:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_221_ = ((lean_object*)(l_Lean_instReprDataValue_repr___closed__13));
v___x_222_ = l_Nat_reprFast(v_v_215_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v___x_222_);
v___x_224_ = v___x_217_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_222_);
v___x_224_ = v_reuseFailAlloc_230_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_225_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_221_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
lean_inc(v___y_220_);
v___x_226_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_226_, 0, v___y_220_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
v___x_227_ = 0;
v___x_228_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_228_, 0, v___x_226_);
lean_ctor_set_uint8(v___x_228_, sizeof(void*)*1, v___x_227_);
v___x_229_ = l_Repr_addAppParen(v___x_228_, v_prec_155_);
return v___x_229_;
}
}
}
}
case 4:
{
lean_object* v_v_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_259_; 
v_v_236_ = lean_ctor_get(v_x_154_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v_x_154_);
if (v_isSharedCheck_259_ == 0)
{
v___x_238_ = v_x_154_;
v_isShared_239_ = v_isSharedCheck_259_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_v_236_);
lean_dec(v_x_154_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_259_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___y_241_; lean_object* v___x_255_; uint8_t v___x_256_; 
v___x_255_ = lean_unsigned_to_nat(1024u);
v___x_256_ = lean_nat_dec_le(v___x_255_, v_prec_155_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; 
v___x_257_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__3, &l_Lean_instReprDataValue_repr___closed__3_once, _init_l_Lean_instReprDataValue_repr___closed__3);
v___y_241_ = v___x_257_;
goto v___jp_240_;
}
else
{
lean_object* v___x_258_; 
v___x_258_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__4, &l_Lean_instReprDataValue_repr___closed__4_once, _init_l_Lean_instReprDataValue_repr___closed__4);
v___y_241_ = v___x_258_;
goto v___jp_240_;
}
v___jp_240_:
{
lean_object* v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; 
v___x_242_ = ((lean_object*)(l_Lean_instReprDataValue_repr___closed__16));
v___x_243_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__17, &l_Lean_instReprDataValue_repr___closed__17_once, _init_l_Lean_instReprDataValue_repr___closed__17);
v___x_244_ = lean_int_dec_lt(v_v_236_, v___x_243_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; lean_object* v___x_247_; 
v___x_245_ = l_Int_repr(v_v_236_);
lean_dec(v_v_236_);
if (v_isShared_239_ == 0)
{
lean_ctor_set_tag(v___x_238_, 3);
lean_ctor_set(v___x_238_, 0, v___x_245_);
v___x_247_ = v___x_238_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_245_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
v___y_157_ = v___y_241_;
v___y_158_ = v___x_242_;
v___y_159_ = v___x_247_;
goto v___jp_156_;
}
}
else
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_252_; 
v___x_249_ = lean_unsigned_to_nat(1024u);
v___x_250_ = l_Int_repr(v_v_236_);
lean_dec(v_v_236_);
if (v_isShared_239_ == 0)
{
lean_ctor_set_tag(v___x_238_, 3);
lean_ctor_set(v___x_238_, 0, v___x_250_);
v___x_252_ = v___x_238_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_250_);
v___x_252_ = v_reuseFailAlloc_254_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_253_; 
v___x_253_ = l_Repr_addAppParen(v___x_252_, v___x_249_);
v___y_157_ = v___y_241_;
v___y_158_ = v___x_242_;
v___y_159_ = v___x_253_;
goto v___jp_156_;
}
}
}
}
}
default: 
{
lean_object* v_v_260_; lean_object* v___y_262_; lean_object* v___x_271_; uint8_t v___x_272_; 
v_v_260_ = lean_ctor_get(v_x_154_, 0);
lean_inc(v_v_260_);
lean_dec_ref_known(v_x_154_, 1);
v___x_271_ = lean_unsigned_to_nat(1024u);
v___x_272_ = lean_nat_dec_le(v___x_271_, v_prec_155_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; 
v___x_273_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__3, &l_Lean_instReprDataValue_repr___closed__3_once, _init_l_Lean_instReprDataValue_repr___closed__3);
v___y_262_ = v___x_273_;
goto v___jp_261_;
}
else
{
lean_object* v___x_274_; 
v___x_274_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__4, &l_Lean_instReprDataValue_repr___closed__4_once, _init_l_Lean_instReprDataValue_repr___closed__4);
v___y_262_ = v___x_274_;
goto v___jp_261_;
}
v___jp_261_:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; uint8_t v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_263_ = ((lean_object*)(l_Lean_instReprDataValue_repr___closed__20));
v___x_264_ = lean_unsigned_to_nat(1024u);
v___x_265_ = l_Lean_Syntax_instRepr_repr(v_v_260_, v___x_264_);
v___x_266_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_263_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
lean_inc(v___y_262_);
v___x_267_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_267_, 0, v___y_262_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
v___x_268_ = 0;
v___x_269_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_269_, 0, v___x_267_);
lean_ctor_set_uint8(v___x_269_, sizeof(void*)*1, v___x_268_);
v___x_270_ = l_Repr_addAppParen(v___x_269_, v_prec_155_);
return v___x_270_;
}
}
}
v___jp_156_:
{
lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
lean_inc(v___y_158_);
v___x_160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_160_, 0, v___y_158_);
lean_ctor_set(v___x_160_, 1, v___y_159_);
lean_inc(v___y_157_);
v___x_161_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_161_, 0, v___y_157_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
v___x_162_ = 0;
v___x_163_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_163_, 0, v___x_161_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*1, v___x_162_);
v___x_164_ = l_Repr_addAppParen(v___x_163_, v_prec_155_);
return v___x_164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprDataValue_repr___boxed(lean_object* v_x_275_, lean_object* v_prec_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_instReprDataValue_repr(v_x_275_, v_prec_276_);
lean_dec(v_prec_276_);
return v_res_277_;
}
}
LEAN_EXPORT uint8_t lean_data_value_beq(lean_object* v_a_280_, lean_object* v_b_281_){
_start:
{
uint8_t v___x_282_; 
v___x_282_ = l_Lean_instBEqDataValue_beq(v_a_280_, v_b_281_);
lean_dec_ref(v_b_281_);
lean_dec_ref(v_a_280_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_beqExp___boxed(lean_object* v_a_283_, lean_object* v_b_284_){
_start:
{
uint8_t v_res_285_; lean_object* v_r_286_; 
v_res_285_ = lean_data_value_beq(v_a_283_, v_b_284_);
v_r_286_ = lean_box(v_res_285_);
return v_r_286_;
}
}
LEAN_EXPORT lean_object* lean_mk_bool_data_value(uint8_t v_b_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_288_, 0, v_b_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBoolDataValueEx___boxed(lean_object* v_b_289_){
_start:
{
uint8_t v_b_boxed_290_; lean_object* v_res_291_; 
v_b_boxed_290_ = lean_unbox(v_b_289_);
v_res_291_ = lean_mk_bool_data_value(v_b_boxed_290_);
return v_res_291_;
}
}
LEAN_EXPORT uint8_t lean_data_value_bool(lean_object* v_x_292_){
_start:
{
if (lean_obj_tag(v_x_292_) == 1)
{
uint8_t v_v_293_; 
v_v_293_ = lean_ctor_get_uint8(v_x_292_, 0);
lean_dec_ref_known(v_x_292_, 0);
return v_v_293_;
}
else
{
uint8_t v___x_294_; 
lean_dec_ref(v_x_292_);
v___x_294_ = 0;
return v___x_294_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_getBoolEx___boxed(lean_object* v_x_295_){
_start:
{
uint8_t v_res_296_; lean_object* v_r_297_; 
v_res_296_ = lean_data_value_bool(v_x_295_);
v_r_297_ = lean_box(v_res_296_);
return v_r_297_;
}
}
LEAN_EXPORT uint8_t l_Lean_DataValue_sameCtor(lean_object* v_x_298_, lean_object* v_x_299_){
_start:
{
switch(lean_obj_tag(v_x_298_))
{
case 0:
{
if (lean_obj_tag(v_x_299_) == 0)
{
uint8_t v___x_300_; 
v___x_300_ = 1;
return v___x_300_;
}
else
{
uint8_t v___x_301_; 
v___x_301_ = 0;
return v___x_301_;
}
}
case 1:
{
if (lean_obj_tag(v_x_299_) == 1)
{
uint8_t v___x_302_; 
v___x_302_ = 1;
return v___x_302_;
}
else
{
uint8_t v___x_303_; 
v___x_303_ = 0;
return v___x_303_;
}
}
case 2:
{
if (lean_obj_tag(v_x_299_) == 2)
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
case 3:
{
if (lean_obj_tag(v_x_299_) == 3)
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
case 4:
{
if (lean_obj_tag(v_x_299_) == 4)
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
default: 
{
if (lean_obj_tag(v_x_299_) == 5)
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_sameCtor___boxed(lean_object* v_x_312_, lean_object* v_x_313_){
_start:
{
uint8_t v_res_314_; lean_object* v_r_315_; 
v_res_314_ = l_Lean_DataValue_sameCtor(v_x_312_, v_x_313_);
lean_dec_ref(v_x_313_);
lean_dec_ref(v_x_312_);
v_r_315_ = lean_box(v_res_314_);
return v_r_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_DataValue_str(lean_object* v_x_318_){
_start:
{
switch(lean_obj_tag(v_x_318_))
{
case 0:
{
lean_object* v_v_319_; 
v_v_319_ = lean_ctor_get(v_x_318_, 0);
lean_inc_ref(v_v_319_);
lean_dec_ref_known(v_x_318_, 1);
return v_v_319_;
}
case 1:
{
uint8_t v_v_320_; 
v_v_320_ = lean_ctor_get_uint8(v_x_318_, 0);
lean_dec_ref_known(v_x_318_, 0);
if (v_v_320_ == 0)
{
lean_object* v___x_321_; 
v___x_321_ = ((lean_object*)(l_Lean_DataValue_str___closed__0));
return v___x_321_;
}
else
{
lean_object* v___x_322_; 
v___x_322_ = ((lean_object*)(l_Lean_DataValue_str___closed__1));
return v___x_322_;
}
}
case 2:
{
lean_object* v_v_323_; uint8_t v___x_324_; lean_object* v___x_325_; 
v_v_323_ = lean_ctor_get(v_x_318_, 0);
lean_inc(v_v_323_);
lean_dec_ref_known(v_x_318_, 1);
v___x_324_ = 1;
v___x_325_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_323_, v___x_324_);
return v___x_325_;
}
case 3:
{
lean_object* v_v_326_; lean_object* v___x_327_; 
v_v_326_ = lean_ctor_get(v_x_318_, 0);
lean_inc(v_v_326_);
lean_dec_ref_known(v_x_318_, 1);
v___x_327_ = l_Nat_reprFast(v_v_326_);
return v___x_327_;
}
case 4:
{
lean_object* v_v_328_; lean_object* v___x_329_; 
v_v_328_ = lean_ctor_get(v_x_318_, 0);
lean_inc(v_v_328_);
lean_dec_ref_known(v_x_318_, 1);
v___x_329_ = l_Int_repr(v_v_328_);
lean_dec(v_v_328_);
return v___x_329_;
}
default: 
{
lean_object* v_v_330_; lean_object* v___x_331_; uint8_t v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v_v_330_ = lean_ctor_get(v_x_318_, 0);
lean_inc(v_v_330_);
lean_dec_ref_known(v_x_318_, 1);
v___x_331_ = lean_box(0);
v___x_332_ = 0;
v___x_333_ = l_Lean_Syntax_formatStx(v_v_330_, v___x_331_, v___x_332_);
v___x_334_ = l_Std_Format_defWidth;
v___x_335_ = lean_unsigned_to_nat(0u);
v___x_336_ = l_Std_Format_pretty(v___x_333_, v___x_334_, v___x_335_, v___x_335_);
return v___x_336_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeStringDataValue___lam__0(lean_object* v_v_339_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_340_, 0, v_v_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeBoolDataValue___lam__0(uint8_t v_v_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_344_, 0, v_v_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeBoolDataValue___lam__0___boxed(lean_object* v_v_345_){
_start:
{
uint8_t v_v_boxed_346_; lean_object* v_res_347_; 
v_v_boxed_346_ = lean_unbox(v_v_345_);
v_res_347_ = l_Lean_instCoeBoolDataValue___lam__0(v_v_boxed_346_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeNameDataValue___lam__0(lean_object* v_v_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_351_, 0, v_v_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeNatDataValue___lam__0(lean_object* v_v_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_355_, 0, v_v_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeIntDataValue___lam__0(lean_object* v_v_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_359_, 0, v_v_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeSyntaxDataValue___lam__0(lean_object* v_v_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_363_, 0, v_v_362_);
return v___x_363_;
}
}
static lean_object* _init_l_Lean_instInhabitedKVMap_default(void){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = lean_box(0);
return v___x_366_;
}
}
static lean_object* _init_l_Lean_instInhabitedKVMap(void){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = lean_box(0);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprKVMap_repr_spec__1(lean_object* v_a_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = lean_nat_to_int(v_a_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_370_, lean_object* v_x_371_, lean_object* v_x_372_){
_start:
{
if (lean_obj_tag(v_x_372_) == 0)
{
lean_dec(v_x_370_);
return v_x_371_;
}
else
{
lean_object* v_head_373_; lean_object* v_tail_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_383_; 
v_head_373_ = lean_ctor_get(v_x_372_, 0);
v_tail_374_ = lean_ctor_get(v_x_372_, 1);
v_isSharedCheck_383_ = !lean_is_exclusive(v_x_372_);
if (v_isSharedCheck_383_ == 0)
{
v___x_376_ = v_x_372_;
v_isShared_377_ = v_isSharedCheck_383_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_tail_374_);
lean_inc(v_head_373_);
lean_dec(v_x_372_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_383_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
lean_inc(v_x_370_);
if (v_isShared_377_ == 0)
{
lean_ctor_set_tag(v___x_376_, 5);
lean_ctor_set(v___x_376_, 1, v_x_370_);
lean_ctor_set(v___x_376_, 0, v_x_371_);
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_x_371_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_x_370_);
v___x_379_ = v_reuseFailAlloc_382_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_380_; 
v___x_380_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
lean_ctor_set(v___x_380_, 1, v_head_373_);
v_x_371_ = v___x_380_;
v_x_372_ = v_tail_374_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0_spec__2(lean_object* v_x_384_, lean_object* v_x_385_){
_start:
{
if (lean_obj_tag(v_x_384_) == 0)
{
lean_object* v___x_386_; 
lean_dec(v_x_385_);
v___x_386_ = lean_box(0);
return v___x_386_;
}
else
{
lean_object* v_tail_387_; 
v_tail_387_ = lean_ctor_get(v_x_384_, 1);
if (lean_obj_tag(v_tail_387_) == 0)
{
lean_object* v_head_388_; 
lean_dec(v_x_385_);
v_head_388_ = lean_ctor_get(v_x_384_, 0);
lean_inc(v_head_388_);
lean_dec_ref_known(v_x_384_, 2);
return v_head_388_;
}
else
{
lean_object* v_head_389_; lean_object* v___x_390_; 
lean_inc(v_tail_387_);
v_head_389_ = lean_ctor_get(v_x_384_, 0);
lean_inc(v_head_389_);
lean_dec_ref_known(v_x_384_, 2);
v___x_390_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0_spec__2_spec__3(v_x_385_, v_head_389_, v_tail_387_);
return v___x_390_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__0));
v___x_400_ = lean_string_length(v___x_399_);
return v___x_400_;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__5, &l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__5_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__5);
v___x_402_ = lean_nat_to_int(v___x_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(lean_object* v_x_407_){
_start:
{
lean_object* v_fst_408_; lean_object* v_snd_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_432_; 
v_fst_408_ = lean_ctor_get(v_x_407_, 0);
v_snd_409_ = lean_ctor_get(v_x_407_, 1);
v_isSharedCheck_432_ = !lean_is_exclusive(v_x_407_);
if (v_isSharedCheck_432_ == 0)
{
v___x_411_ = v_x_407_;
v_isShared_412_ = v_isSharedCheck_432_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_snd_409_);
lean_inc(v_fst_408_);
lean_dec(v_x_407_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_432_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_413_ = lean_unsigned_to_nat(0u);
v___x_414_ = l_Lean_Name_reprPrec(v_fst_408_, v___x_413_);
v___x_415_ = lean_box(0);
if (v_isShared_412_ == 0)
{
lean_ctor_set_tag(v___x_411_, 1);
lean_ctor_set(v___x_411_, 1, v___x_415_);
lean_ctor_set(v___x_411_, 0, v___x_414_);
v___x_417_ = v___x_411_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_414_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v___x_415_);
v___x_417_ = v_reuseFailAlloc_431_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; lean_object* v___x_430_; 
v___x_418_ = l_Lean_instReprDataValue_repr(v_snd_409_, v___x_413_);
v___x_419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
lean_ctor_set(v___x_419_, 1, v___x_417_);
v___x_420_ = l_List_reverse___redArg(v___x_419_);
v___x_421_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__3));
v___x_422_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0_spec__2(v___x_420_, v___x_421_);
v___x_423_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__6, &l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__6_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__6);
v___x_424_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__7));
v___x_425_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
lean_ctor_set(v___x_425_, 1, v___x_422_);
v___x_426_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__8));
v___x_427_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_425_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
v___x_428_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_423_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
v___x_429_ = 0;
v___x_430_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_430_, 0, v___x_428_);
lean_ctor_set_uint8(v___x_430_, sizeof(void*)*1, v___x_429_);
return v___x_430_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1_spec__4_spec__6(lean_object* v_x_433_, lean_object* v_x_434_, lean_object* v_x_435_){
_start:
{
if (lean_obj_tag(v_x_435_) == 0)
{
lean_dec(v_x_433_);
return v_x_434_;
}
else
{
lean_object* v_head_436_; lean_object* v_tail_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_447_; 
v_head_436_ = lean_ctor_get(v_x_435_, 0);
v_tail_437_ = lean_ctor_get(v_x_435_, 1);
v_isSharedCheck_447_ = !lean_is_exclusive(v_x_435_);
if (v_isSharedCheck_447_ == 0)
{
v___x_439_ = v_x_435_;
v_isShared_440_ = v_isSharedCheck_447_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_tail_437_);
lean_inc(v_head_436_);
lean_dec(v_x_435_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_447_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
lean_inc(v_x_433_);
if (v_isShared_440_ == 0)
{
lean_ctor_set_tag(v___x_439_, 5);
lean_ctor_set(v___x_439_, 1, v_x_433_);
lean_ctor_set(v___x_439_, 0, v_x_434_);
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_x_434_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_x_433_);
v___x_442_ = v_reuseFailAlloc_446_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(v_head_436_);
v___x_444_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_442_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
v_x_434_ = v___x_444_;
v_x_435_ = v_tail_437_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1_spec__4(lean_object* v_x_448_, lean_object* v_x_449_, lean_object* v_x_450_){
_start:
{
if (lean_obj_tag(v_x_450_) == 0)
{
lean_dec(v_x_448_);
return v_x_449_;
}
else
{
lean_object* v_head_451_; lean_object* v_tail_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_462_; 
v_head_451_ = lean_ctor_get(v_x_450_, 0);
v_tail_452_ = lean_ctor_get(v_x_450_, 1);
v_isSharedCheck_462_ = !lean_is_exclusive(v_x_450_);
if (v_isSharedCheck_462_ == 0)
{
v___x_454_ = v_x_450_;
v_isShared_455_ = v_isSharedCheck_462_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_tail_452_);
lean_inc(v_head_451_);
lean_dec(v_x_450_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_462_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
lean_inc(v_x_448_);
if (v_isShared_455_ == 0)
{
lean_ctor_set_tag(v___x_454_, 5);
lean_ctor_set(v___x_454_, 1, v_x_448_);
lean_ctor_set(v___x_454_, 0, v_x_449_);
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_x_449_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v_x_448_);
v___x_457_ = v_reuseFailAlloc_461_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_458_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(v_head_451_);
v___x_459_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_457_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
v___x_460_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1_spec__4_spec__6(v_x_448_, v___x_459_, v_tail_452_);
return v___x_460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1(lean_object* v_x_463_, lean_object* v_x_464_){
_start:
{
if (lean_obj_tag(v_x_463_) == 0)
{
lean_object* v___x_465_; 
lean_dec(v_x_464_);
v___x_465_ = lean_box(0);
return v___x_465_;
}
else
{
lean_object* v_tail_466_; 
v_tail_466_ = lean_ctor_get(v_x_463_, 1);
if (lean_obj_tag(v_tail_466_) == 0)
{
lean_object* v_head_467_; lean_object* v___x_468_; 
lean_dec(v_x_464_);
v_head_467_ = lean_ctor_get(v_x_463_, 0);
lean_inc(v_head_467_);
lean_dec_ref_known(v_x_463_, 2);
v___x_468_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(v_head_467_);
return v___x_468_;
}
else
{
lean_object* v_head_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
lean_inc(v_tail_466_);
v_head_469_ = lean_ctor_get(v_x_463_, 0);
lean_inc(v_head_469_);
lean_dec_ref_known(v_x_463_, 2);
v___x_470_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(v_head_469_);
v___x_471_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1_spec__4(v_x_464_, v___x_470_, v_tail_466_);
return v___x_471_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = ((lean_object*)(l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__2));
v___x_478_ = lean_string_length(v___x_477_);
return v___x_478_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = lean_obj_once(&l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__4, &l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__4_once, _init_l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__4);
v___x_480_ = lean_nat_to_int(v___x_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg(lean_object* v_a_485_){
_start:
{
if (lean_obj_tag(v_a_485_) == 0)
{
lean_object* v___x_486_; 
v___x_486_ = ((lean_object*)(l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__1));
return v___x_486_;
}
else
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; uint8_t v___x_495_; lean_object* v___x_496_; 
v___x_487_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__3));
v___x_488_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1(v_a_485_, v___x_487_);
v___x_489_ = lean_obj_once(&l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__5, &l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__5_once, _init_l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__5);
v___x_490_ = ((lean_object*)(l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__6));
v___x_491_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
lean_ctor_set(v___x_491_, 1, v___x_488_);
v___x_492_ = ((lean_object*)(l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__7));
v___x_493_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_491_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
v___x_494_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_489_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = 0;
v___x_496_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_496_, 0, v___x_494_);
lean_ctor_set_uint8(v___x_496_, sizeof(void*)*1, v___x_495_);
return v___x_496_;
}
}
}
static lean_object* _init_l_Lean_instReprKVMap_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = lean_unsigned_to_nat(11u);
v___x_511_ = lean_nat_to_int(v___x_510_);
return v___x_511_;
}
}
static lean_object* _init_l_Lean_instReprKVMap_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = ((lean_object*)(l_Lean_instReprKVMap_repr___redArg___closed__0));
v___x_514_ = lean_string_length(v___x_513_);
return v___x_514_;
}
}
static lean_object* _init_l_Lean_instReprKVMap_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_obj_once(&l_Lean_instReprKVMap_repr___redArg___closed__9, &l_Lean_instReprKVMap_repr___redArg___closed__9_once, _init_l_Lean_instReprKVMap_repr___redArg___closed__9);
v___x_516_ = lean_nat_to_int(v___x_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprKVMap_repr___redArg(lean_object* v_x_521_){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_522_ = ((lean_object*)(l_Lean_instReprKVMap_repr___redArg___closed__6));
v___x_523_ = lean_obj_once(&l_Lean_instReprKVMap_repr___redArg___closed__7, &l_Lean_instReprKVMap_repr___redArg___closed__7_once, _init_l_Lean_instReprKVMap_repr___redArg___closed__7);
v___x_524_ = l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg(v_x_521_);
v___x_525_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_523_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = 0;
v___x_527_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_527_, 0, v___x_525_);
lean_ctor_set_uint8(v___x_527_, sizeof(void*)*1, v___x_526_);
v___x_528_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_522_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
v___x_529_ = lean_obj_once(&l_Lean_instReprKVMap_repr___redArg___closed__10, &l_Lean_instReprKVMap_repr___redArg___closed__10_once, _init_l_Lean_instReprKVMap_repr___redArg___closed__10);
v___x_530_ = ((lean_object*)(l_Lean_instReprKVMap_repr___redArg___closed__11));
v___x_531_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
lean_ctor_set(v___x_531_, 1, v___x_528_);
v___x_532_ = ((lean_object*)(l_Lean_instReprKVMap_repr___redArg___closed__12));
v___x_533_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_531_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_529_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_535_, 0, v___x_534_);
lean_ctor_set_uint8(v___x_535_, sizeof(void*)*1, v___x_526_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprKVMap_repr(lean_object* v_x_536_, lean_object* v_prec_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Lean_instReprKVMap_repr___redArg(v_x_536_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprKVMap_repr___boxed(lean_object* v_x_539_, lean_object* v_prec_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lean_instReprKVMap_repr(v_x_539_, v_prec_540_);
lean_dec(v_prec_540_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprKVMap_repr_spec__0(lean_object* v_a_542_, lean_object* v_n_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg(v_a_542_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___boxed(lean_object* v_a_545_, lean_object* v_n_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_List_repr___at___00Lean_instReprKVMap_repr_spec__0(v_a_545_, v_n_546_);
lean_dec(v_n_546_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0(lean_object* v_x_548_, lean_object* v_x_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(v_x_548_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___boxed(lean_object* v_x_551_, lean_object* v_x_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0(v_x_551_, v_x_552_);
lean_dec(v_x_552_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instToString___lam__0(lean_object* v___f_556_, lean_object* v_m_557_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_List_toString___redArg(v___f_556_, v_m_557_);
return v___x_558_;
}
}
static lean_object* _init_l_Lean_KVMap_empty(void){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = lean_box(0);
return v___x_566_;
}
}
LEAN_EXPORT uint8_t l_Lean_KVMap_isEmpty(lean_object* v_x_567_){
_start:
{
uint8_t v___x_568_; 
v___x_568_ = l_List_isEmpty___redArg(v_x_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_isEmpty___boxed(lean_object* v_x_569_){
_start:
{
uint8_t v_res_570_; lean_object* v_r_571_; 
v_res_570_ = l_Lean_KVMap_isEmpty(v_x_569_);
lean_dec(v_x_569_);
v_r_571_ = lean_box(v_res_570_);
return v_r_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_size(lean_object* v_m_572_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_List_lengthTR___redArg(v_m_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_size___boxed(lean_object* v_m_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_KVMap_size(v_m_574_);
lean_dec(v_m_574_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_findCore(lean_object* v_x_576_, lean_object* v_x_577_){
_start:
{
if (lean_obj_tag(v_x_576_) == 0)
{
lean_object* v___x_578_; 
v___x_578_ = lean_box(0);
return v___x_578_;
}
else
{
lean_object* v_head_579_; lean_object* v_tail_580_; lean_object* v_fst_581_; lean_object* v_snd_582_; uint8_t v___x_583_; 
v_head_579_ = lean_ctor_get(v_x_576_, 0);
v_tail_580_ = lean_ctor_get(v_x_576_, 1);
v_fst_581_ = lean_ctor_get(v_head_579_, 0);
v_snd_582_ = lean_ctor_get(v_head_579_, 1);
v___x_583_ = lean_name_eq(v_fst_581_, v_x_577_);
if (v___x_583_ == 0)
{
v_x_576_ = v_tail_580_;
goto _start;
}
else
{
lean_object* v___x_585_; 
lean_inc(v_snd_582_);
v___x_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_585_, 0, v_snd_582_);
return v___x_585_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_findCore___boxed(lean_object* v_x_586_, lean_object* v_x_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lean_KVMap_findCore(v_x_586_, v_x_587_);
lean_dec(v_x_587_);
lean_dec(v_x_586_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_find(lean_object* v_x_589_, lean_object* v_x_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_KVMap_findCore(v_x_589_, v_x_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_find___boxed(lean_object* v_x_592_, lean_object* v_x_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_KVMap_find(v_x_592_, v_x_593_);
lean_dec(v_x_593_);
lean_dec(v_x_592_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_findD(lean_object* v_m_595_, lean_object* v_k_596_, lean_object* v_d_u2080_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_KVMap_findCore(v_m_595_, v_k_596_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_inc_ref(v_d_u2080_597_);
return v_d_u2080_597_;
}
else
{
lean_object* v_val_599_; 
v_val_599_ = lean_ctor_get(v___x_598_, 0);
lean_inc(v_val_599_);
lean_dec_ref_known(v___x_598_, 1);
return v_val_599_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_findD___boxed(lean_object* v_m_600_, lean_object* v_k_601_, lean_object* v_d_u2080_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Lean_KVMap_findD(v_m_600_, v_k_601_, v_d_u2080_602_);
lean_dec_ref(v_d_u2080_602_);
lean_dec(v_k_601_);
lean_dec(v_m_600_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_insertCore(lean_object* v_x_604_, lean_object* v_x_605_, lean_object* v_x_606_){
_start:
{
if (lean_obj_tag(v_x_604_) == 0)
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_607_, 0, v_x_605_);
lean_ctor_set(v___x_607_, 1, v_x_606_);
v___x_608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
lean_ctor_set(v___x_608_, 1, v_x_604_);
return v___x_608_;
}
else
{
lean_object* v_head_609_; lean_object* v_tail_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_632_; 
v_head_609_ = lean_ctor_get(v_x_604_, 0);
v_tail_610_ = lean_ctor_get(v_x_604_, 1);
v_isSharedCheck_632_ = !lean_is_exclusive(v_x_604_);
if (v_isSharedCheck_632_ == 0)
{
v___x_612_ = v_x_604_;
v_isShared_613_ = v_isSharedCheck_632_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_tail_610_);
lean_inc(v_head_609_);
lean_dec(v_x_604_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_632_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v_fst_614_; uint8_t v___x_615_; 
v_fst_614_ = lean_ctor_get(v_head_609_, 0);
v___x_615_ = lean_name_eq(v_fst_614_, v_x_605_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; lean_object* v___x_618_; 
v___x_616_ = l_Lean_KVMap_insertCore(v_tail_610_, v_x_605_, v_x_606_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 1, v___x_616_);
v___x_618_ = v___x_612_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_head_609_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v___x_616_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
else
{
lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_629_; 
lean_inc(v_fst_614_);
lean_dec(v_x_605_);
v_isSharedCheck_629_ = !lean_is_exclusive(v_head_609_);
if (v_isSharedCheck_629_ == 0)
{
lean_object* v_unused_630_; lean_object* v_unused_631_; 
v_unused_630_ = lean_ctor_get(v_head_609_, 1);
lean_dec(v_unused_630_);
v_unused_631_ = lean_ctor_get(v_head_609_, 0);
lean_dec(v_unused_631_);
v___x_621_ = v_head_609_;
v_isShared_622_ = v_isSharedCheck_629_;
goto v_resetjp_620_;
}
else
{
lean_dec(v_head_609_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_629_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 1, v_x_606_);
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_fst_614_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v_x_606_);
v___x_624_ = v_reuseFailAlloc_628_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_626_; 
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 0, v___x_624_);
v___x_626_ = v___x_612_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_tail_610_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_insert(lean_object* v_x_633_, lean_object* v_x_634_, lean_object* v_x_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_KVMap_insertCore(v_x_633_, v_x_634_, v_x_635_);
return v___x_636_;
}
}
LEAN_EXPORT uint8_t l_Lean_KVMap_contains(lean_object* v_m_637_, lean_object* v_n_638_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Lean_KVMap_findCore(v_m_637_, v_n_638_);
if (lean_obj_tag(v___x_639_) == 0)
{
uint8_t v___x_640_; 
v___x_640_ = 0;
return v___x_640_;
}
else
{
uint8_t v___x_641_; 
lean_dec_ref_known(v___x_639_, 1);
v___x_641_ = 1;
return v___x_641_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_contains___boxed(lean_object* v_m_642_, lean_object* v_n_643_){
_start:
{
uint8_t v_res_644_; lean_object* v_r_645_; 
v_res_644_ = l_Lean_KVMap_contains(v_m_642_, v_n_643_);
lean_dec(v_n_643_);
lean_dec(v_m_642_);
v_r_645_ = lean_box(v_res_644_);
return v_r_645_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_KVMap_erase_spec__0(lean_object* v_x_646_, lean_object* v_a_647_, lean_object* v_a_648_){
_start:
{
if (lean_obj_tag(v_a_647_) == 0)
{
lean_object* v___x_649_; 
v___x_649_ = l_List_reverse___redArg(v_a_648_);
return v___x_649_;
}
else
{
lean_object* v_head_650_; lean_object* v_tail_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_662_; 
v_head_650_ = lean_ctor_get(v_a_647_, 0);
v_tail_651_ = lean_ctor_get(v_a_647_, 1);
v_isSharedCheck_662_ = !lean_is_exclusive(v_a_647_);
if (v_isSharedCheck_662_ == 0)
{
v___x_653_ = v_a_647_;
v_isShared_654_ = v_isSharedCheck_662_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_tail_651_);
lean_inc(v_head_650_);
lean_dec(v_a_647_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_662_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v_fst_655_; uint8_t v___x_656_; 
v_fst_655_ = lean_ctor_get(v_head_650_, 0);
v___x_656_ = lean_name_eq(v_fst_655_, v_x_646_);
if (v___x_656_ == 0)
{
lean_object* v___x_658_; 
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 1, v_a_648_);
v___x_658_ = v___x_653_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_head_650_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v_a_648_);
v___x_658_ = v_reuseFailAlloc_660_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
v_a_647_ = v_tail_651_;
v_a_648_ = v___x_658_;
goto _start;
}
}
else
{
lean_del_object(v___x_653_);
lean_dec(v_head_650_);
v_a_647_ = v_tail_651_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_KVMap_erase_spec__0___boxed(lean_object* v_x_663_, lean_object* v_a_664_, lean_object* v_a_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_List_filterTR_loop___at___00Lean_KVMap_erase_spec__0(v_x_663_, v_a_664_, v_a_665_);
lean_dec(v_x_663_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_erase(lean_object* v_x_667_, lean_object* v_x_668_){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = lean_box(0);
v___x_670_ = l_List_filterTR_loop___at___00Lean_KVMap_erase_spec__0(v_x_668_, v_x_667_, v___x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_erase___boxed(lean_object* v_x_671_, lean_object* v_x_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_KVMap_erase(v_x_671_, v_x_672_);
lean_dec(v_x_672_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getString(lean_object* v_m_674_, lean_object* v_k_675_, lean_object* v_defVal_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Lean_KVMap_findCore(v_m_674_, v_k_675_);
if (lean_obj_tag(v___x_677_) == 1)
{
lean_object* v_val_678_; 
v_val_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_val_678_);
lean_dec_ref_known(v___x_677_, 1);
if (lean_obj_tag(v_val_678_) == 0)
{
lean_object* v_v_679_; 
v_v_679_ = lean_ctor_get(v_val_678_, 0);
lean_inc_ref(v_v_679_);
lean_dec_ref_known(v_val_678_, 1);
return v_v_679_;
}
else
{
lean_dec(v_val_678_);
lean_inc_ref(v_defVal_676_);
return v_defVal_676_;
}
}
else
{
lean_dec(v___x_677_);
lean_inc_ref(v_defVal_676_);
return v_defVal_676_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getString___boxed(lean_object* v_m_680_, lean_object* v_k_681_, lean_object* v_defVal_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_KVMap_getString(v_m_680_, v_k_681_, v_defVal_682_);
lean_dec_ref(v_defVal_682_);
lean_dec(v_k_681_);
lean_dec(v_m_680_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getNat(lean_object* v_m_684_, lean_object* v_k_685_, lean_object* v_defVal_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Lean_KVMap_findCore(v_m_684_, v_k_685_);
if (lean_obj_tag(v___x_687_) == 1)
{
lean_object* v_val_688_; 
v_val_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_val_688_);
lean_dec_ref_known(v___x_687_, 1);
if (lean_obj_tag(v_val_688_) == 3)
{
lean_object* v_v_689_; 
v_v_689_ = lean_ctor_get(v_val_688_, 0);
lean_inc(v_v_689_);
lean_dec_ref_known(v_val_688_, 1);
return v_v_689_;
}
else
{
lean_dec(v_val_688_);
lean_inc(v_defVal_686_);
return v_defVal_686_;
}
}
else
{
lean_dec(v___x_687_);
lean_inc(v_defVal_686_);
return v_defVal_686_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getNat___boxed(lean_object* v_m_690_, lean_object* v_k_691_, lean_object* v_defVal_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_KVMap_getNat(v_m_690_, v_k_691_, v_defVal_692_);
lean_dec(v_defVal_692_);
lean_dec(v_k_691_);
lean_dec(v_m_690_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getInt(lean_object* v_m_694_, lean_object* v_k_695_, lean_object* v_defVal_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Lean_KVMap_findCore(v_m_694_, v_k_695_);
if (lean_obj_tag(v___x_697_) == 1)
{
lean_object* v_val_698_; 
v_val_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_val_698_);
lean_dec_ref_known(v___x_697_, 1);
if (lean_obj_tag(v_val_698_) == 4)
{
lean_object* v_v_699_; 
v_v_699_ = lean_ctor_get(v_val_698_, 0);
lean_inc(v_v_699_);
lean_dec_ref_known(v_val_698_, 1);
return v_v_699_;
}
else
{
lean_dec(v_val_698_);
lean_inc(v_defVal_696_);
return v_defVal_696_;
}
}
else
{
lean_dec(v___x_697_);
lean_inc(v_defVal_696_);
return v_defVal_696_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getInt___boxed(lean_object* v_m_700_, lean_object* v_k_701_, lean_object* v_defVal_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Lean_KVMap_getInt(v_m_700_, v_k_701_, v_defVal_702_);
lean_dec(v_defVal_702_);
lean_dec(v_k_701_);
lean_dec(v_m_700_);
return v_res_703_;
}
}
LEAN_EXPORT uint8_t l_Lean_KVMap_getBool(lean_object* v_m_704_, lean_object* v_k_705_, uint8_t v_defVal_706_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = l_Lean_KVMap_findCore(v_m_704_, v_k_705_);
if (lean_obj_tag(v___x_707_) == 1)
{
lean_object* v_val_708_; 
v_val_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_val_708_);
lean_dec_ref_known(v___x_707_, 1);
if (lean_obj_tag(v_val_708_) == 1)
{
uint8_t v_v_709_; 
v_v_709_ = lean_ctor_get_uint8(v_val_708_, 0);
lean_dec_ref_known(v_val_708_, 0);
return v_v_709_;
}
else
{
lean_dec(v_val_708_);
return v_defVal_706_;
}
}
else
{
lean_dec(v___x_707_);
return v_defVal_706_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getBool___boxed(lean_object* v_m_710_, lean_object* v_k_711_, lean_object* v_defVal_712_){
_start:
{
uint8_t v_defVal_boxed_713_; uint8_t v_res_714_; lean_object* v_r_715_; 
v_defVal_boxed_713_ = lean_unbox(v_defVal_712_);
v_res_714_ = l_Lean_KVMap_getBool(v_m_710_, v_k_711_, v_defVal_boxed_713_);
lean_dec(v_k_711_);
lean_dec(v_m_710_);
v_r_715_ = lean_box(v_res_714_);
return v_r_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getName(lean_object* v_m_716_, lean_object* v_k_717_, lean_object* v_defVal_718_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Lean_KVMap_findCore(v_m_716_, v_k_717_);
if (lean_obj_tag(v___x_719_) == 1)
{
lean_object* v_val_720_; 
v_val_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_val_720_);
lean_dec_ref_known(v___x_719_, 1);
if (lean_obj_tag(v_val_720_) == 2)
{
lean_object* v_v_721_; 
v_v_721_ = lean_ctor_get(v_val_720_, 0);
lean_inc(v_v_721_);
lean_dec_ref_known(v_val_720_, 1);
return v_v_721_;
}
else
{
lean_dec(v_val_720_);
lean_inc(v_defVal_718_);
return v_defVal_718_;
}
}
else
{
lean_dec(v___x_719_);
lean_inc(v_defVal_718_);
return v_defVal_718_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getName___boxed(lean_object* v_m_722_, lean_object* v_k_723_, lean_object* v_defVal_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Lean_KVMap_getName(v_m_722_, v_k_723_, v_defVal_724_);
lean_dec(v_defVal_724_);
lean_dec(v_k_723_);
lean_dec(v_m_722_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getSyntax(lean_object* v_m_726_, lean_object* v_k_727_, lean_object* v_defVal_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Lean_KVMap_findCore(v_m_726_, v_k_727_);
if (lean_obj_tag(v___x_729_) == 1)
{
lean_object* v_val_730_; 
v_val_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_val_730_);
lean_dec_ref_known(v___x_729_, 1);
if (lean_obj_tag(v_val_730_) == 5)
{
lean_object* v_v_731_; 
v_v_731_ = lean_ctor_get(v_val_730_, 0);
lean_inc(v_v_731_);
lean_dec_ref_known(v_val_730_, 1);
return v_v_731_;
}
else
{
lean_dec(v_val_730_);
lean_inc(v_defVal_728_);
return v_defVal_728_;
}
}
else
{
lean_dec(v___x_729_);
lean_inc(v_defVal_728_);
return v_defVal_728_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_getSyntax___boxed(lean_object* v_m_732_, lean_object* v_k_733_, lean_object* v_defVal_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lean_KVMap_getSyntax(v_m_732_, v_k_733_, v_defVal_734_);
lean_dec(v_defVal_734_);
lean_dec(v_k_733_);
lean_dec(v_m_732_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_setString(lean_object* v_m_736_, lean_object* v_k_737_, lean_object* v_v_738_){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_739_, 0, v_v_738_);
v___x_740_ = l_Lean_KVMap_insertCore(v_m_736_, v_k_737_, v___x_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_setNat(lean_object* v_m_741_, lean_object* v_k_742_, lean_object* v_v_743_){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_744_, 0, v_v_743_);
v___x_745_ = l_Lean_KVMap_insertCore(v_m_741_, v_k_742_, v___x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_setInt(lean_object* v_m_746_, lean_object* v_k_747_, lean_object* v_v_748_){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_749_, 0, v_v_748_);
v___x_750_ = l_Lean_KVMap_insertCore(v_m_746_, v_k_747_, v___x_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_setBool(lean_object* v_m_751_, lean_object* v_k_752_, uint8_t v_v_753_){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_754_, 0, v_v_753_);
v___x_755_ = l_Lean_KVMap_insertCore(v_m_751_, v_k_752_, v___x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_setBool___boxed(lean_object* v_m_756_, lean_object* v_k_757_, lean_object* v_v_758_){
_start:
{
uint8_t v_v_boxed_759_; lean_object* v_res_760_; 
v_v_boxed_759_ = lean_unbox(v_v_758_);
v_res_760_ = l_Lean_KVMap_setBool(v_m_756_, v_k_757_, v_v_boxed_759_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_setName(lean_object* v_m_761_, lean_object* v_k_762_, lean_object* v_v_763_){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_764_, 0, v_v_763_);
v___x_765_ = l_Lean_KVMap_insertCore(v_m_761_, v_k_762_, v___x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_setSyntax(lean_object* v_m_766_, lean_object* v_k_767_, lean_object* v_v_768_){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_769_, 0, v_v_768_);
v___x_770_ = l_Lean_KVMap_insertCore(v_m_766_, v_k_767_, v___x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_updateString(lean_object* v_m_771_, lean_object* v_k_772_, lean_object* v_f_773_){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_774_ = ((lean_object*)(l_Lean_instInhabitedDataValue_default___closed__0));
v___x_775_ = l_Lean_KVMap_getString(v_m_771_, v_k_772_, v___x_774_);
v___x_776_ = lean_apply_1(v_f_773_, v___x_775_);
v___x_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
v___x_778_ = l_Lean_KVMap_insertCore(v_m_771_, v_k_772_, v___x_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_updateNat(lean_object* v_m_779_, lean_object* v_k_780_, lean_object* v_f_781_){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_782_ = lean_unsigned_to_nat(0u);
v___x_783_ = l_Lean_KVMap_getNat(v_m_779_, v_k_780_, v___x_782_);
v___x_784_ = lean_apply_1(v_f_781_, v___x_783_);
v___x_785_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
v___x_786_ = l_Lean_KVMap_insertCore(v_m_779_, v_k_780_, v___x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_updateInt(lean_object* v_m_787_, lean_object* v_k_788_, lean_object* v_f_789_){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_790_ = lean_obj_once(&l_Lean_instReprDataValue_repr___closed__17, &l_Lean_instReprDataValue_repr___closed__17_once, _init_l_Lean_instReprDataValue_repr___closed__17);
v___x_791_ = l_Lean_KVMap_getInt(v_m_787_, v_k_788_, v___x_790_);
v___x_792_ = lean_apply_1(v_f_789_, v___x_791_);
v___x_793_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
v___x_794_ = l_Lean_KVMap_insertCore(v_m_787_, v_k_788_, v___x_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_updateBool(lean_object* v_m_795_, lean_object* v_k_796_, lean_object* v_f_797_){
_start:
{
uint8_t v___x_798_; uint8_t v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; lean_object* v___x_804_; 
v___x_798_ = 0;
v___x_799_ = l_Lean_KVMap_getBool(v_m_795_, v_k_796_, v___x_798_);
v___x_800_ = lean_box(v___x_799_);
v___x_801_ = lean_apply_1(v_f_797_, v___x_800_);
v___x_802_ = lean_alloc_ctor(1, 0, 1);
v___x_803_ = lean_unbox(v___x_801_);
lean_ctor_set_uint8(v___x_802_, 0, v___x_803_);
v___x_804_ = l_Lean_KVMap_insertCore(v_m_795_, v_k_796_, v___x_802_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_updateName(lean_object* v_m_805_, lean_object* v_k_806_, lean_object* v_f_807_){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_808_ = lean_box(0);
v___x_809_ = l_Lean_KVMap_getName(v_m_805_, v_k_806_, v___x_808_);
v___x_810_ = lean_apply_1(v_f_807_, v___x_809_);
v___x_811_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
v___x_812_ = l_Lean_KVMap_insertCore(v_m_805_, v_k_806_, v___x_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_updateSyntax(lean_object* v_m_813_, lean_object* v_k_814_, lean_object* v_f_815_){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_816_ = lean_box(0);
v___x_817_ = l_Lean_KVMap_getSyntax(v_m_813_, v_k_814_, v___x_816_);
v___x_818_ = lean_apply_1(v_f_815_, v___x_817_);
v___x_819_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
v___x_820_ = l_Lean_KVMap_insertCore(v_m_813_, v_k_814_, v___x_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_forIn___redArg___lam__0(lean_object* v_f_821_, lean_object* v_a_822_, lean_object* v_x_823_, lean_object* v___y_824_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = lean_apply_2(v_f_821_, v_a_822_, v___y_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_forIn___redArg(lean_object* v_inst_826_, lean_object* v_kv_827_, lean_object* v_init_828_, lean_object* v_f_829_){
_start:
{
lean_object* v___f_830_; lean_object* v___x_831_; 
v___f_830_ = lean_alloc_closure((void*)(l_Lean_KVMap_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_830_, 0, v_f_829_);
v___x_831_ = l_List_forIn_x27_loop___redArg(v_inst_826_, v___f_830_, v_kv_827_, v_init_828_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_forIn___redArg___boxed(lean_object* v_inst_832_, lean_object* v_kv_833_, lean_object* v_init_834_, lean_object* v_f_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Lean_KVMap_forIn___redArg(v_inst_832_, v_kv_833_, v_init_834_, v_f_835_);
lean_dec(v_kv_833_);
return v_res_836_;
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
LEAN_EXPORT lean_object* l_Lean_KVMap_forIn___boxed(lean_object* v_00_u03b4_845_, lean_object* v_m_846_, lean_object* v_inst_847_, lean_object* v_kv_848_, lean_object* v_init_849_, lean_object* v_f_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_KVMap_forIn(v_00_u03b4_845_, v_m_846_, v_inst_847_, v_kv_848_, v_init_849_, v_f_850_);
lean_dec(v_kv_848_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__0(lean_object* v___y_852_, lean_object* v_a_853_, lean_object* v_x_854_, lean_object* v___y_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = lean_apply_2(v___y_852_, v_a_853_, v___y_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__1(lean_object* v_inst_857_, lean_object* v_00_u03b2_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v___f_862_; lean_object* v___x_863_; 
v___f_862_ = lean_alloc_closure((void*)(l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_862_, 0, v___y_861_);
v___x_863_ = l_List_forIn_x27_loop___redArg(v_inst_857_, v___f_862_, v___y_859_, v___y_860_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__1___boxed(lean_object* v_inst_864_, lean_object* v_00_u03b2_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__1(v_inst_864_, v_00_u03b2_865_, v___y_866_, v___y_867_, v___y_868_);
lean_dec(v___y_866_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg(lean_object* v_inst_870_){
_start:
{
lean_object* v___f_871_; 
v___f_871_ = lean_alloc_closure((void*)(l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__1___boxed), 5, 1);
lean_closure_set(v___f_871_, 0, v_inst_870_);
return v___f_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instForInProdNameDataValueOfMonad(lean_object* v_m_872_, lean_object* v_inst_873_){
_start:
{
lean_object* v___f_874_; 
v___f_874_ = lean_alloc_closure((void*)(l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__1___boxed), 5, 1);
lean_closure_set(v___f_874_, 0, v_inst_873_);
return v___f_874_;
}
}
LEAN_EXPORT uint8_t l_Lean_KVMap_subsetAux(lean_object* v_x_875_, lean_object* v_x_876_){
_start:
{
if (lean_obj_tag(v_x_875_) == 0)
{
uint8_t v___x_877_; 
v___x_877_ = 1;
return v___x_877_;
}
else
{
lean_object* v_head_878_; lean_object* v_tail_879_; lean_object* v_fst_880_; lean_object* v_snd_881_; lean_object* v___x_882_; 
v_head_878_ = lean_ctor_get(v_x_875_, 0);
v_tail_879_ = lean_ctor_get(v_x_875_, 1);
v_fst_880_ = lean_ctor_get(v_head_878_, 0);
v_snd_881_ = lean_ctor_get(v_head_878_, 1);
v___x_882_ = l_Lean_KVMap_findCore(v_x_876_, v_fst_880_);
if (lean_obj_tag(v___x_882_) == 0)
{
uint8_t v___x_883_; 
v___x_883_ = 0;
return v___x_883_;
}
else
{
lean_object* v_val_884_; uint8_t v___x_885_; 
v_val_884_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_val_884_);
lean_dec_ref_known(v___x_882_, 1);
v___x_885_ = l_Lean_instBEqDataValue_beq(v_snd_881_, v_val_884_);
lean_dec(v_val_884_);
if (v___x_885_ == 0)
{
return v___x_885_;
}
else
{
v_x_875_ = v_tail_879_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_subsetAux___boxed(lean_object* v_x_887_, lean_object* v_x_888_){
_start:
{
uint8_t v_res_889_; lean_object* v_r_890_; 
v_res_889_ = l_Lean_KVMap_subsetAux(v_x_887_, v_x_888_);
lean_dec(v_x_888_);
lean_dec(v_x_887_);
v_r_890_ = lean_box(v_res_889_);
return v_r_890_;
}
}
LEAN_EXPORT uint8_t l_Lean_KVMap_subset(lean_object* v_x_891_, lean_object* v_x_892_){
_start:
{
uint8_t v___x_893_; 
v___x_893_ = l_Lean_KVMap_subsetAux(v_x_891_, v_x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_subset___boxed(lean_object* v_x_894_, lean_object* v_x_895_){
_start:
{
uint8_t v_res_896_; lean_object* v_r_897_; 
v_res_896_ = l_Lean_KVMap_subset(v_x_894_, v_x_895_);
lean_dec(v_x_895_);
lean_dec(v_x_894_);
v_r_897_ = lean_box(v_res_896_);
return v_r_897_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___redArg(lean_object* v_mergeFn_898_, lean_object* v_as_x27_899_, lean_object* v_b_900_){
_start:
{
if (lean_obj_tag(v_as_x27_899_) == 0)
{
lean_dec_ref(v_mergeFn_898_);
return v_b_900_;
}
else
{
lean_object* v_head_901_; lean_object* v_tail_902_; lean_object* v_fst_903_; lean_object* v_snd_904_; lean_object* v___x_905_; 
v_head_901_ = lean_ctor_get(v_as_x27_899_, 0);
v_tail_902_ = lean_ctor_get(v_as_x27_899_, 1);
v_fst_903_ = lean_ctor_get(v_head_901_, 0);
v_snd_904_ = lean_ctor_get(v_head_901_, 1);
v___x_905_ = l_Lean_KVMap_findCore(v_b_900_, v_fst_903_);
if (lean_obj_tag(v___x_905_) == 1)
{
lean_object* v_val_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v_val_906_ = lean_ctor_get(v___x_905_, 0);
lean_inc(v_val_906_);
lean_dec_ref_known(v___x_905_, 1);
lean_inc_ref(v_mergeFn_898_);
lean_inc(v_snd_904_);
lean_inc_n(v_fst_903_, 2);
v___x_907_ = lean_apply_3(v_mergeFn_898_, v_fst_903_, v_val_906_, v_snd_904_);
v___x_908_ = l_Lean_KVMap_insertCore(v_b_900_, v_fst_903_, v___x_907_);
v_as_x27_899_ = v_tail_902_;
v_b_900_ = v___x_908_;
goto _start;
}
else
{
lean_object* v___x_910_; 
lean_dec(v___x_905_);
lean_inc(v_snd_904_);
lean_inc(v_fst_903_);
v___x_910_ = l_Lean_KVMap_insertCore(v_b_900_, v_fst_903_, v_snd_904_);
v_as_x27_899_ = v_tail_902_;
v_b_900_ = v___x_910_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___redArg___boxed(lean_object* v_mergeFn_912_, lean_object* v_as_x27_913_, lean_object* v_b_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___redArg(v_mergeFn_912_, v_as_x27_913_, v_b_914_);
lean_dec(v_as_x27_913_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_mergeBy(lean_object* v_mergeFn_916_, lean_object* v_l_917_, lean_object* v_r_918_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___redArg(v_mergeFn_916_, v_r_918_, v_l_917_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_mergeBy___boxed(lean_object* v_mergeFn_920_, lean_object* v_l_921_, lean_object* v_r_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_KVMap_mergeBy(v_mergeFn_920_, v_l_921_, v_r_922_);
lean_dec(v_r_922_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0(lean_object* v_mergeFn_924_, lean_object* v_as_925_, lean_object* v_as_x27_926_, lean_object* v_b_927_, lean_object* v_a_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___redArg(v_mergeFn_924_, v_as_x27_926_, v_b_927_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___boxed(lean_object* v_mergeFn_930_, lean_object* v_as_931_, lean_object* v_as_x27_932_, lean_object* v_b_933_, lean_object* v_a_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0(v_mergeFn_930_, v_as_931_, v_as_x27_932_, v_b_933_, v_a_934_);
lean_dec(v_as_x27_932_);
lean_dec(v_as_931_);
return v_res_935_;
}
}
LEAN_EXPORT uint8_t l_Lean_KVMap_eqv(lean_object* v_m_u2081_936_, lean_object* v_m_u2082_937_){
_start:
{
uint8_t v___x_938_; 
v___x_938_ = l_Lean_KVMap_subsetAux(v_m_u2081_936_, v_m_u2082_937_);
if (v___x_938_ == 0)
{
return v___x_938_;
}
else
{
uint8_t v___x_939_; 
v___x_939_ = l_Lean_KVMap_subsetAux(v_m_u2082_937_, v_m_u2081_936_);
return v___x_939_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_eqv___boxed(lean_object* v_m_u2081_940_, lean_object* v_m_u2082_941_){
_start:
{
uint8_t v_res_942_; lean_object* v_r_943_; 
v_res_942_ = l_Lean_KVMap_eqv(v_m_u2081_940_, v_m_u2082_941_);
lean_dec(v_m_u2082_941_);
lean_dec(v_m_u2081_940_);
v_r_943_ = lean_box(v_res_942_);
return v_r_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_get_x3f___redArg(lean_object* v_inst_946_, lean_object* v_m_947_, lean_object* v_k_948_){
_start:
{
lean_object* v_ofDataValue_x3f_949_; lean_object* v___x_950_; 
v_ofDataValue_x3f_949_ = lean_ctor_get(v_inst_946_, 1);
lean_inc_ref(v_ofDataValue_x3f_949_);
lean_dec_ref(v_inst_946_);
v___x_950_ = l_Lean_KVMap_findCore(v_m_947_, v_k_948_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v___x_951_; 
lean_dec_ref(v_ofDataValue_x3f_949_);
v___x_951_ = lean_box(0);
return v___x_951_;
}
else
{
lean_object* v_val_952_; lean_object* v___x_953_; 
v_val_952_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_val_952_);
lean_dec_ref_known(v___x_950_, 1);
v___x_953_ = lean_apply_1(v_ofDataValue_x3f_949_, v_val_952_);
return v___x_953_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_get_x3f___redArg___boxed(lean_object* v_inst_954_, lean_object* v_m_955_, lean_object* v_k_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_KVMap_get_x3f___redArg(v_inst_954_, v_m_955_, v_k_956_);
lean_dec(v_k_956_);
lean_dec(v_m_955_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_get_x3f(lean_object* v_00_u03b1_958_, lean_object* v_inst_959_, lean_object* v_m_960_, lean_object* v_k_961_){
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
LEAN_EXPORT lean_object* l_Lean_KVMap_get_x3f___boxed(lean_object* v_00_u03b1_967_, lean_object* v_inst_968_, lean_object* v_m_969_, lean_object* v_k_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lean_KVMap_get_x3f(v_00_u03b1_967_, v_inst_968_, v_m_969_, v_k_970_);
lean_dec(v_k_970_);
lean_dec(v_m_969_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_get___redArg(lean_object* v_inst_972_, lean_object* v_m_973_, lean_object* v_k_974_, lean_object* v_defVal_975_){
_start:
{
lean_object* v_ofDataValue_x3f_976_; lean_object* v___x_977_; 
v_ofDataValue_x3f_976_ = lean_ctor_get(v_inst_972_, 1);
lean_inc_ref(v_ofDataValue_x3f_976_);
lean_dec_ref(v_inst_972_);
v___x_977_ = l_Lean_KVMap_findCore(v_m_973_, v_k_974_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_dec_ref(v_ofDataValue_x3f_976_);
lean_inc(v_defVal_975_);
return v_defVal_975_;
}
else
{
lean_object* v_val_978_; lean_object* v___x_979_; 
v_val_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_val_978_);
lean_dec_ref_known(v___x_977_, 1);
v___x_979_ = lean_apply_1(v_ofDataValue_x3f_976_, v_val_978_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_inc(v_defVal_975_);
return v_defVal_975_;
}
else
{
lean_object* v_val_980_; 
v_val_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_val_980_);
lean_dec_ref_known(v___x_979_, 1);
return v_val_980_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_get___redArg___boxed(lean_object* v_inst_981_, lean_object* v_m_982_, lean_object* v_k_983_, lean_object* v_defVal_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Lean_KVMap_get___redArg(v_inst_981_, v_m_982_, v_k_983_, v_defVal_984_);
lean_dec(v_defVal_984_);
lean_dec(v_k_983_);
lean_dec(v_m_982_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_get(lean_object* v_00_u03b1_986_, lean_object* v_inst_987_, lean_object* v_m_988_, lean_object* v_k_989_, lean_object* v_defVal_990_){
_start:
{
lean_object* v_ofDataValue_x3f_991_; lean_object* v___x_992_; 
v_ofDataValue_x3f_991_ = lean_ctor_get(v_inst_987_, 1);
lean_inc_ref(v_ofDataValue_x3f_991_);
lean_dec_ref(v_inst_987_);
v___x_992_ = l_Lean_KVMap_findCore(v_m_988_, v_k_989_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_dec_ref(v_ofDataValue_x3f_991_);
lean_inc(v_defVal_990_);
return v_defVal_990_;
}
else
{
lean_object* v_val_993_; lean_object* v___x_994_; 
v_val_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_val_993_);
lean_dec_ref_known(v___x_992_, 1);
v___x_994_ = lean_apply_1(v_ofDataValue_x3f_991_, v_val_993_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_inc(v_defVal_990_);
return v_defVal_990_;
}
else
{
lean_object* v_val_995_; 
v_val_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_val_995_);
lean_dec_ref_known(v___x_994_, 1);
return v_val_995_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_get___boxed(lean_object* v_00_u03b1_996_, lean_object* v_inst_997_, lean_object* v_m_998_, lean_object* v_k_999_, lean_object* v_defVal_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lean_KVMap_get(v_00_u03b1_996_, v_inst_997_, v_m_998_, v_k_999_, v_defVal_1000_);
lean_dec(v_defVal_1000_);
lean_dec(v_k_999_);
lean_dec(v_m_998_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_set___redArg(lean_object* v_inst_1002_, lean_object* v_m_1003_, lean_object* v_k_1004_, lean_object* v_v_1005_){
_start:
{
lean_object* v_toDataValue_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v_toDataValue_1006_ = lean_ctor_get(v_inst_1002_, 0);
lean_inc_ref(v_toDataValue_1006_);
lean_dec_ref(v_inst_1002_);
v___x_1007_ = lean_apply_1(v_toDataValue_1006_, v_v_1005_);
v___x_1008_ = l_Lean_KVMap_insertCore(v_m_1003_, v_k_1004_, v___x_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_set(lean_object* v_00_u03b1_1009_, lean_object* v_inst_1010_, lean_object* v_m_1011_, lean_object* v_k_1012_, lean_object* v_v_1013_){
_start:
{
lean_object* v_toDataValue_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v_toDataValue_1014_ = lean_ctor_get(v_inst_1010_, 0);
lean_inc_ref(v_toDataValue_1014_);
lean_dec_ref(v_inst_1010_);
v___x_1015_ = lean_apply_1(v_toDataValue_1014_, v_v_1013_);
v___x_1016_ = l_Lean_KVMap_insertCore(v_m_1011_, v_k_1012_, v___x_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_update___redArg(lean_object* v_inst_1017_, lean_object* v_m_1018_, lean_object* v_k_1019_, lean_object* v_f_1020_){
_start:
{
lean_object* v_toDataValue_1021_; lean_object* v_ofDataValue_x3f_1022_; lean_object* v___y_1024_; lean_object* v___x_1030_; 
v_toDataValue_1021_ = lean_ctor_get(v_inst_1017_, 0);
lean_inc_ref(v_toDataValue_1021_);
v_ofDataValue_x3f_1022_ = lean_ctor_get(v_inst_1017_, 1);
lean_inc_ref(v_ofDataValue_x3f_1022_);
lean_dec_ref(v_inst_1017_);
v___x_1030_ = l_Lean_KVMap_findCore(v_m_1018_, v_k_1019_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v___x_1031_; 
lean_dec_ref(v_ofDataValue_x3f_1022_);
v___x_1031_ = lean_box(0);
v___y_1024_ = v___x_1031_;
goto v___jp_1023_;
}
else
{
lean_object* v_val_1032_; lean_object* v___x_1033_; 
v_val_1032_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_val_1032_);
lean_dec_ref_known(v___x_1030_, 1);
v___x_1033_ = lean_apply_1(v_ofDataValue_x3f_1022_, v_val_1032_);
v___y_1024_ = v___x_1033_;
goto v___jp_1023_;
}
v___jp_1023_:
{
lean_object* v___x_1025_; 
v___x_1025_ = lean_apply_1(v_f_1020_, v___y_1024_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v___x_1026_; 
lean_dec_ref(v_toDataValue_1021_);
v___x_1026_ = l_Lean_KVMap_erase(v_m_1018_, v_k_1019_);
lean_dec(v_k_1019_);
return v___x_1026_;
}
else
{
lean_object* v_val_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v_val_1027_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_val_1027_);
lean_dec_ref_known(v___x_1025_, 1);
v___x_1028_ = lean_apply_1(v_toDataValue_1021_, v_val_1027_);
v___x_1029_ = l_Lean_KVMap_insertCore(v_m_1018_, v_k_1019_, v___x_1028_);
return v___x_1029_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_update(lean_object* v_00_u03b1_1034_, lean_object* v_inst_1035_, lean_object* v_m_1036_, lean_object* v_k_1037_, lean_object* v_f_1038_){
_start:
{
lean_object* v_toDataValue_1039_; lean_object* v_ofDataValue_x3f_1040_; lean_object* v___y_1042_; lean_object* v___x_1048_; 
v_toDataValue_1039_ = lean_ctor_get(v_inst_1035_, 0);
lean_inc_ref(v_toDataValue_1039_);
v_ofDataValue_x3f_1040_ = lean_ctor_get(v_inst_1035_, 1);
lean_inc_ref(v_ofDataValue_x3f_1040_);
lean_dec_ref(v_inst_1035_);
v___x_1048_ = l_Lean_KVMap_findCore(v_m_1036_, v_k_1037_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v___x_1049_; 
lean_dec_ref(v_ofDataValue_x3f_1040_);
v___x_1049_ = lean_box(0);
v___y_1042_ = v___x_1049_;
goto v___jp_1041_;
}
else
{
lean_object* v_val_1050_; lean_object* v___x_1051_; 
v_val_1050_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_val_1050_);
lean_dec_ref_known(v___x_1048_, 1);
v___x_1051_ = lean_apply_1(v_ofDataValue_x3f_1040_, v_val_1050_);
v___y_1042_ = v___x_1051_;
goto v___jp_1041_;
}
v___jp_1041_:
{
lean_object* v___x_1043_; 
v___x_1043_ = lean_apply_1(v_f_1038_, v___y_1042_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v___x_1044_; 
lean_dec_ref(v_toDataValue_1039_);
v___x_1044_ = l_Lean_KVMap_erase(v_m_1036_, v_k_1037_);
lean_dec(v_k_1037_);
return v___x_1044_;
}
else
{
lean_object* v_val_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v_val_1045_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_val_1045_);
lean_dec_ref_known(v___x_1043_, 1);
v___x_1046_ = lean_apply_1(v_toDataValue_1039_, v_val_1045_);
v___x_1047_ = l_Lean_KVMap_insertCore(v_m_1036_, v_k_1037_, v___x_1046_);
return v___x_1047_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueDataValue___lam__0(lean_object* v_val_1052_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1053_, 0, v_val_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueBool___lam__1(lean_object* v_x_1060_){
_start:
{
if (lean_obj_tag(v_x_1060_) == 1)
{
uint8_t v_v_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v_v_1061_ = lean_ctor_get_uint8(v_x_1060_, 0);
v___x_1062_ = lean_box(v_v_1061_);
v___x_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
return v___x_1063_;
}
else
{
lean_object* v___x_1064_; 
v___x_1064_ = lean_box(0);
return v___x_1064_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueBool___lam__1___boxed(lean_object* v_x_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Lean_KVMap_instValueBool___lam__1(v_x_1065_);
lean_dec_ref(v_x_1065_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueNat___lam__1(lean_object* v_x_1072_){
_start:
{
if (lean_obj_tag(v_x_1072_) == 3)
{
lean_object* v_v_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
v_v_1073_ = lean_ctor_get(v_x_1072_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_x_1072_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v_x_1072_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_v_1073_);
lean_dec(v_x_1072_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
lean_ctor_set_tag(v___x_1075_, 1);
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_v_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
else
{
lean_object* v___x_1081_; 
lean_dec_ref(v_x_1072_);
v___x_1081_ = lean_box(0);
return v___x_1081_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueInt___lam__1(lean_object* v_x_1087_){
_start:
{
if (lean_obj_tag(v_x_1087_) == 4)
{
lean_object* v_v_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
v_v_1088_ = lean_ctor_get(v_x_1087_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v_x_1087_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v_x_1087_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_v_1088_);
lean_dec(v_x_1087_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
lean_ctor_set_tag(v___x_1090_, 1);
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_v_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
else
{
lean_object* v___x_1096_; 
lean_dec_ref(v_x_1087_);
v___x_1096_ = lean_box(0);
return v___x_1096_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueName___lam__1(lean_object* v_x_1102_){
_start:
{
if (lean_obj_tag(v_x_1102_) == 2)
{
lean_object* v_v_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
v_v_1103_ = lean_ctor_get(v_x_1102_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v_x_1102_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v_x_1102_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_v_1103_);
lean_dec(v_x_1102_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
lean_ctor_set_tag(v___x_1105_, 1);
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_v_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
else
{
lean_object* v___x_1111_; 
lean_dec_ref(v_x_1102_);
v___x_1111_ = lean_box(0);
return v___x_1111_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueString___lam__1(lean_object* v_x_1117_){
_start:
{
if (lean_obj_tag(v_x_1117_) == 0)
{
lean_object* v_v_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
v_v_1118_ = lean_ctor_get(v_x_1117_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_x_1117_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v_x_1117_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_v_1118_);
lean_dec(v_x_1117_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set_tag(v___x_1120_, 1);
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_v_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
else
{
lean_object* v___x_1126_; 
lean_dec_ref(v_x_1117_);
v___x_1126_ = lean_box(0);
return v___x_1126_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_KVMap_instValueSyntax___lam__1(lean_object* v_x_1132_){
_start:
{
if (lean_obj_tag(v_x_1132_) == 5)
{
lean_object* v_v_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
v_v_1133_ = lean_ctor_get(v_x_1132_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v_x_1132_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v_x_1132_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_v_1133_);
lean_dec(v_x_1132_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
lean_ctor_set_tag(v___x_1135_, 1);
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_v_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
else
{
lean_object* v___x_1141_; 
lean_dec_ref(v_x_1132_);
v___x_1141_ = lean_box(0);
return v___x_1141_;
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

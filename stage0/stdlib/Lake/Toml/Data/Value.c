// Lean compiler output
// Module: Lake.Toml.Data.Value
// Imports: public import Init.Data.Float.Float public import Lake.Toml.Data.Dict public import Lake.Toml.Data.DateTime import Lake.Util.String import Init.Data.String.TakeDrop import Init.Data.String.Search public import Init.Data.String.Defs import Init.Data.ToString.Macro
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
uint8_t lean_float_beq(double, double);
uint8_t l_Lake_Toml_instDecidableEqDateTime_decEq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Nat_toDigits(lean_object*, lean_object*);
lean_object* lean_string_mk(lean_object*);
lean_object* l_Lake_lpadAscii(lean_object*, uint32_t, lean_object*);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Int_repr(lean_object*);
lean_object* lean_float_to_string(double);
lean_object* l_Lake_Toml_DateTime_toString(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lake_Toml_RBDict_mkEmpty___redArg(lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lake_Toml_RBDict_empty___redArg();
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_string_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_string_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_integer_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_integer_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_float_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_float_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_boolean_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_boolean_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_dateTime_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_dateTime_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_array_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_array_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_table_x27_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_table_x27_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Toml_instInhabitedValue_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_Toml_instInhabitedValue_default___closed__0 = (const lean_object*)&l_Lake_Toml_instInhabitedValue_default___closed__0_value;
static const lean_ctor_object l_Lake_Toml_instInhabitedValue_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Toml_instInhabitedValue_default___closed__0_value)}};
static const lean_object* l_Lake_Toml_instInhabitedValue_default___closed__1 = (const lean_object*)&l_Lake_Toml_instInhabitedValue_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Toml_instInhabitedValue_default = (const lean_object*)&l_Lake_Toml_instInhabitedValue_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Toml_instInhabitedValue = (const lean_object*)&l_Lake_Toml_instInhabitedValue_default___closed__1_value;
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Toml_instBEqValue_beq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instBEqValue_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_Toml_instBEqValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_instBEqValue_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_instBEqValue___closed__0 = (const lean_object*)&l_Lake_Toml_instBEqValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Toml_instBEqValue = (const lean_object*)&l_Lake_Toml_instBEqValue___closed__0_value;
static lean_once_cell_t l_Lake_Toml_Table_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_Table_empty___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_Table_empty;
LEAN_EXPORT lean_object* l_Lake_Toml_Table_mkEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_mkEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_table(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_ref(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_ref___boxed(lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\\u"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\\\\"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\\\""};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\\r"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\\f"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__4_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\\n"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__5_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\\t"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__6_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\\b"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__7_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Toml_ppString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\""};
static const lean_object* l_Lake_Toml_ppString___closed__0 = (const lean_object*)&l_Lake_Toml_ppString___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Toml_ppString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_ppString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lake_Toml_ppSimpleKey_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lake_Toml_ppSimpleKey_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_ppSimpleKey(lean_object*);
static const lean_string_object l_Lake_Toml_ppKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_Toml_ppKey___closed__0 = (const lean_object*)&l_Lake_Toml_ppKey___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Toml_ppKey(lean_object*);
static const lean_string_object l_Lake_Toml_ppInlineArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lake_Toml_ppInlineArray___closed__0 = (const lean_object*)&l_Lake_Toml_ppInlineArray___closed__0_value;
static const lean_string_object l_Lake_Toml_ppInlineArray___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lake_Toml_ppInlineArray___closed__1 = (const lean_object*)&l_Lake_Toml_ppInlineArray___closed__1_value;
static const lean_string_object l_Lake_Toml_ppInlineArray___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lake_Toml_ppInlineArray___closed__2 = (const lean_object*)&l_Lake_Toml_ppInlineArray___closed__2_value;
static const lean_string_object l_Lake_Toml_Value_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lake_Toml_Value_toString___closed__0 = (const lean_object*)&l_Lake_Toml_Value_toString___closed__0_value;
static const lean_string_object l_Lake_Toml_Value_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lake_Toml_Value_toString___closed__1 = (const lean_object*)&l_Lake_Toml_Value_toString___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " = "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0(size_t, size_t, lean_object*);
static const lean_string_object l_Lake_Toml_ppInlineTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_Lake_Toml_ppInlineTable___closed__0 = (const lean_object*)&l_Lake_Toml_ppInlineTable___closed__0_value;
static const lean_string_object l_Lake_Toml_ppInlineTable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Lake_Toml_ppInlineTable___closed__1 = (const lean_object*)&l_Lake_Toml_ppInlineTable___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Toml_ppInlineTable(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_toString(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_ppInlineArray(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_Toml_instToStringValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_Value_toString, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_instToStringValue___closed__0 = (const lean_object*)&l_Lake_Toml_instToStringValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Toml_instToStringValue = (const lean_object*)&l_Lake_Toml_instToStringValue___closed__0_value;
static const lean_string_object l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval___closed__0 = (const lean_object*)&l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lake_Toml_ppTable_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[["};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "]]\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lake.Toml.Data.Value"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lake.Toml.ppTable"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Toml_ppTable_spec__4(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Toml_ppTable_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " = []\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "]\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lake_Toml_ppTable_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lake_Toml_ppTable_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lake_Toml_ppTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Toml_instInhabitedValue_default___closed__0_value),((lean_object*)&l_Lake_Toml_instInhabitedValue_default___closed__0_value)}};
static const lean_object* l_Lake_Toml_ppTable___closed__0 = (const lean_object*)&l_Lake_Toml_ppTable___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Toml_ppTable(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_ppTable___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lake_Toml_Value_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
switch(lean_obj_tag(v_t_5_))
{
case 1:
{
lean_object* v_ref_7_; lean_object* v_n_8_; lean_object* v___x_9_; 
v_ref_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_ref_7_);
v_n_8_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_n_8_);
lean_dec_ref_known(v_t_5_, 2);
v___x_9_ = lean_apply_2(v_k_6_, v_ref_7_, v_n_8_);
return v___x_9_;
}
case 2:
{
lean_object* v_ref_10_; double v_n_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v_ref_10_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_ref_10_);
v_n_11_ = lean_ctor_get_float(v_t_5_, sizeof(void*)*1);
lean_dec_ref_known(v_t_5_, 1);
v___x_12_ = lean_box_float(v_n_11_);
v___x_13_ = lean_apply_2(v_k_6_, v_ref_10_, v___x_12_);
return v___x_13_;
}
case 3:
{
lean_object* v_ref_14_; uint8_t v_b_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v_ref_14_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_ref_14_);
v_b_15_ = lean_ctor_get_uint8(v_t_5_, sizeof(void*)*1);
lean_dec_ref_known(v_t_5_, 1);
v___x_16_ = lean_box(v_b_15_);
v___x_17_ = lean_apply_2(v_k_6_, v_ref_14_, v___x_16_);
return v___x_17_;
}
default: 
{
lean_object* v_ref_18_; lean_object* v_s_19_; lean_object* v___x_20_; 
v_ref_18_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_ref_18_);
v_s_19_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_s_19_);
lean_dec_ref(v_t_5_);
v___x_20_ = lean_apply_2(v_k_6_, v_ref_18_, v_s_19_);
return v___x_20_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_ctorElim(lean_object* v_motive__1_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_23_, v_k_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_ctorElim___boxed(lean_object* v_motive__1_27_, lean_object* v_ctorIdx_28_, lean_object* v_t_29_, lean_object* v_h_30_, lean_object* v_k_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lake_Toml_Value_ctorElim(v_motive__1_27_, v_ctorIdx_28_, v_t_29_, v_h_30_, v_k_31_);
lean_dec(v_ctorIdx_28_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_string_elim___redArg(lean_object* v_t_33_, lean_object* v_string_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_33_, v_string_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_string_elim(lean_object* v_motive__1_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_string_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_37_, v_string_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_integer_elim___redArg(lean_object* v_t_41_, lean_object* v_integer_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_41_, v_integer_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_integer_elim(lean_object* v_motive__1_44_, lean_object* v_t_45_, lean_object* v_h_46_, lean_object* v_integer_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_45_, v_integer_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_float_elim___redArg(lean_object* v_t_49_, lean_object* v_float_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_49_, v_float_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_float_elim(lean_object* v_motive__1_52_, lean_object* v_t_53_, lean_object* v_h_54_, lean_object* v_float_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_53_, v_float_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_boolean_elim___redArg(lean_object* v_t_57_, lean_object* v_boolean_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_57_, v_boolean_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_boolean_elim(lean_object* v_motive__1_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_boolean_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_61_, v_boolean_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_dateTime_elim___redArg(lean_object* v_t_65_, lean_object* v_dateTime_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_65_, v_dateTime_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_dateTime_elim(lean_object* v_motive__1_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_dateTime_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_69_, v_dateTime_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_array_elim___redArg(lean_object* v_t_73_, lean_object* v_array_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_73_, v_array_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_array_elim(lean_object* v_motive__1_76_, lean_object* v_t_77_, lean_object* v_h_78_, lean_object* v_array_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_77_, v_array_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_table_x27_elim___redArg(lean_object* v_t_81_, lean_object* v_table_x27_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_81_, v_table_x27_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_table_x27_elim(lean_object* v_motive__1_84_, lean_object* v_t_85_, lean_object* v_h_86_, lean_object* v_table_x27_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_85_, v_table_x27_87_);
return v___x_88_;
}
}
uint8_t l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0___redArg(lean_object* v_xs_95_, lean_object* v_ys_96_, lean_object* v_x_97_){
_start:
{
lean_object* v_zero_98_; uint8_t v_isZero_99_; 
v_zero_98_ = lean_unsigned_to_nat(0u);
v_isZero_99_ = lean_nat_dec_eq(v_x_97_, v_zero_98_);
if (v_isZero_99_ == 1)
{
lean_dec(v_x_97_);
return v_isZero_99_;
}
else
{
lean_object* v_one_100_; lean_object* v_n_101_; lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v_one_100_ = lean_unsigned_to_nat(1u);
v_n_101_ = lean_nat_sub(v_x_97_, v_one_100_);
lean_dec(v_x_97_);
v___x_102_ = lean_array_fget_borrowed(v_xs_95_, v_n_101_);
v___x_103_ = lean_array_fget_borrowed(v_ys_96_, v_n_101_);
lean_inc(v___x_103_);
lean_inc(v___x_102_);
v___x_104_ = l_Lake_Toml_instBEqValue_beq(v___x_102_, v___x_103_);
if (v___x_104_ == 0)
{
lean_dec(v_n_101_);
return v___x_104_;
}
else
{
v_x_97_ = v_n_101_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_95_ = stack[0].m_obj;
lean_object* v_ys_96_ = stack[1].m_obj;
lean_object* v_x_97_ = stack[2].m_obj;
uint8_t v_res_106_;
v_res_106_ = l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0___redArg(v_xs_95_, v_ys_96_, v_x_97_);
stack->m_num = v_res_106_;
}
uint8_t l_Lake_Toml_instBEqValue_beq(lean_object* v_x_107_, lean_object* v_x_108_){
_start:
{
switch(lean_obj_tag(v_x_107_))
{
case 0:
{
if (lean_obj_tag(v_x_108_) == 0)
{
lean_object* v_ref_109_; lean_object* v_s_110_; lean_object* v_ref_111_; lean_object* v_s_112_; uint8_t v___x_113_; 
v_ref_109_ = lean_ctor_get(v_x_107_, 0);
lean_inc(v_ref_109_);
v_s_110_ = lean_ctor_get(v_x_107_, 1);
lean_inc_ref(v_s_110_);
lean_dec_ref_known(v_x_107_, 2);
v_ref_111_ = lean_ctor_get(v_x_108_, 0);
lean_inc(v_ref_111_);
v_s_112_ = lean_ctor_get(v_x_108_, 1);
lean_inc_ref(v_s_112_);
lean_dec_ref_known(v_x_108_, 2);
v___x_113_ = l_Lean_Syntax_structEq(v_ref_109_, v_ref_111_);
lean_dec(v_ref_111_);
lean_dec(v_ref_109_);
if (v___x_113_ == 0)
{
lean_dec_ref(v_s_112_);
lean_dec_ref(v_s_110_);
return v___x_113_;
}
else
{
uint8_t v___x_114_; 
v___x_114_ = lean_string_dec_eq(v_s_110_, v_s_112_);
lean_dec_ref(v_s_112_);
lean_dec_ref(v_s_110_);
return v___x_114_;
}
}
else
{
uint8_t v___x_115_; 
lean_dec_ref_known(v_x_107_, 2);
lean_dec_ref(v_x_108_);
v___x_115_ = 0;
return v___x_115_;
}
}
case 1:
{
if (lean_obj_tag(v_x_108_) == 1)
{
lean_object* v_ref_116_; lean_object* v_n_117_; lean_object* v_ref_118_; lean_object* v_n_119_; uint8_t v___x_120_; 
v_ref_116_ = lean_ctor_get(v_x_107_, 0);
lean_inc(v_ref_116_);
v_n_117_ = lean_ctor_get(v_x_107_, 1);
lean_inc(v_n_117_);
lean_dec_ref_known(v_x_107_, 2);
v_ref_118_ = lean_ctor_get(v_x_108_, 0);
lean_inc(v_ref_118_);
v_n_119_ = lean_ctor_get(v_x_108_, 1);
lean_inc(v_n_119_);
lean_dec_ref_known(v_x_108_, 2);
v___x_120_ = l_Lean_Syntax_structEq(v_ref_116_, v_ref_118_);
lean_dec(v_ref_118_);
lean_dec(v_ref_116_);
if (v___x_120_ == 0)
{
lean_dec(v_n_119_);
lean_dec(v_n_117_);
return v___x_120_;
}
else
{
uint8_t v___x_121_; 
v___x_121_ = lean_int_dec_eq(v_n_117_, v_n_119_);
lean_dec(v_n_119_);
lean_dec(v_n_117_);
return v___x_121_;
}
}
else
{
uint8_t v___x_122_; 
lean_dec_ref_known(v_x_107_, 2);
lean_dec_ref(v_x_108_);
v___x_122_ = 0;
return v___x_122_;
}
}
case 2:
{
if (lean_obj_tag(v_x_108_) == 2)
{
lean_object* v_ref_123_; double v_n_124_; lean_object* v_ref_125_; double v_n_126_; uint8_t v___x_127_; 
v_ref_123_ = lean_ctor_get(v_x_107_, 0);
lean_inc(v_ref_123_);
v_n_124_ = lean_ctor_get_float(v_x_107_, sizeof(void*)*1);
lean_dec_ref_known(v_x_107_, 1);
v_ref_125_ = lean_ctor_get(v_x_108_, 0);
lean_inc(v_ref_125_);
v_n_126_ = lean_ctor_get_float(v_x_108_, sizeof(void*)*1);
lean_dec_ref_known(v_x_108_, 1);
v___x_127_ = l_Lean_Syntax_structEq(v_ref_123_, v_ref_125_);
lean_dec(v_ref_125_);
lean_dec(v_ref_123_);
if (v___x_127_ == 0)
{
return v___x_127_;
}
else
{
uint8_t v___x_128_; 
v___x_128_ = lean_float_beq(v_n_124_, v_n_126_);
return v___x_128_;
}
}
else
{
uint8_t v___x_129_; 
lean_dec_ref_known(v_x_107_, 1);
lean_dec_ref(v_x_108_);
v___x_129_ = 0;
return v___x_129_;
}
}
case 3:
{
if (lean_obj_tag(v_x_108_) == 3)
{
lean_object* v_ref_130_; uint8_t v_b_131_; lean_object* v_ref_132_; uint8_t v_b_133_; uint8_t v___x_134_; 
v_ref_130_ = lean_ctor_get(v_x_107_, 0);
lean_inc(v_ref_130_);
v_b_131_ = lean_ctor_get_uint8(v_x_107_, sizeof(void*)*1);
lean_dec_ref_known(v_x_107_, 1);
v_ref_132_ = lean_ctor_get(v_x_108_, 0);
lean_inc(v_ref_132_);
v_b_133_ = lean_ctor_get_uint8(v_x_108_, sizeof(void*)*1);
lean_dec_ref_known(v_x_108_, 1);
v___x_134_ = l_Lean_Syntax_structEq(v_ref_130_, v_ref_132_);
lean_dec(v_ref_132_);
lean_dec(v_ref_130_);
if (v___x_134_ == 0)
{
return v___x_134_;
}
else
{
if (v_b_133_ == 0)
{
if (v_b_131_ == 0)
{
return v___x_134_;
}
else
{
return v_b_133_;
}
}
else
{
return v_b_131_;
}
}
}
else
{
uint8_t v___x_135_; 
lean_dec_ref_known(v_x_107_, 1);
lean_dec_ref(v_x_108_);
v___x_135_ = 0;
return v___x_135_;
}
}
case 4:
{
if (lean_obj_tag(v_x_108_) == 4)
{
lean_object* v_ref_136_; lean_object* v_dt_137_; lean_object* v_ref_138_; lean_object* v_dt_139_; uint8_t v___x_140_; 
v_ref_136_ = lean_ctor_get(v_x_107_, 0);
lean_inc(v_ref_136_);
v_dt_137_ = lean_ctor_get(v_x_107_, 1);
lean_inc_ref(v_dt_137_);
lean_dec_ref_known(v_x_107_, 2);
v_ref_138_ = lean_ctor_get(v_x_108_, 0);
lean_inc(v_ref_138_);
v_dt_139_ = lean_ctor_get(v_x_108_, 1);
lean_inc_ref(v_dt_139_);
lean_dec_ref_known(v_x_108_, 2);
v___x_140_ = l_Lean_Syntax_structEq(v_ref_136_, v_ref_138_);
lean_dec(v_ref_138_);
lean_dec(v_ref_136_);
if (v___x_140_ == 0)
{
lean_dec_ref(v_dt_139_);
lean_dec_ref(v_dt_137_);
return v___x_140_;
}
else
{
uint8_t v___x_141_; 
v___x_141_ = l_Lake_Toml_instDecidableEqDateTime_decEq(v_dt_137_, v_dt_139_);
return v___x_141_;
}
}
else
{
uint8_t v___x_142_; 
lean_dec_ref_known(v_x_107_, 2);
lean_dec_ref(v_x_108_);
v___x_142_ = 0;
return v___x_142_;
}
}
case 5:
{
if (lean_obj_tag(v_x_108_) == 5)
{
lean_object* v_ref_143_; lean_object* v_xs_144_; lean_object* v_ref_145_; lean_object* v_xs_146_; uint8_t v___x_147_; 
v_ref_143_ = lean_ctor_get(v_x_107_, 0);
lean_inc(v_ref_143_);
v_xs_144_ = lean_ctor_get(v_x_107_, 1);
lean_inc_ref(v_xs_144_);
lean_dec_ref_known(v_x_107_, 2);
v_ref_145_ = lean_ctor_get(v_x_108_, 0);
lean_inc(v_ref_145_);
v_xs_146_ = lean_ctor_get(v_x_108_, 1);
lean_inc_ref(v_xs_146_);
lean_dec_ref_known(v_x_108_, 2);
v___x_147_ = l_Lean_Syntax_structEq(v_ref_143_, v_ref_145_);
lean_dec(v_ref_145_);
lean_dec(v_ref_143_);
if (v___x_147_ == 0)
{
lean_dec_ref(v_xs_146_);
lean_dec_ref(v_xs_144_);
return v___x_147_;
}
else
{
lean_object* v___x_148_; lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_148_ = lean_array_get_size(v_xs_144_);
v___x_149_ = lean_array_get_size(v_xs_146_);
v___x_150_ = lean_nat_dec_eq(v___x_148_, v___x_149_);
if (v___x_150_ == 0)
{
lean_dec_ref(v_xs_146_);
lean_dec_ref(v_xs_144_);
return v___x_150_;
}
else
{
uint8_t v___x_151_; 
v___x_151_ = l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0___redArg(v_xs_144_, v_xs_146_, v___x_148_);
lean_dec_ref(v_xs_146_);
lean_dec_ref(v_xs_144_);
return v___x_151_;
}
}
}
else
{
uint8_t v___x_152_; 
lean_dec_ref_known(v_x_107_, 2);
lean_dec_ref(v_x_108_);
v___x_152_ = 0;
return v___x_152_;
}
}
default: 
{
if (lean_obj_tag(v_x_108_) == 6)
{
lean_object* v_ref_153_; lean_object* v_xs_154_; lean_object* v_ref_155_; lean_object* v_xs_156_; uint8_t v___x_157_; 
v_ref_153_ = lean_ctor_get(v_x_107_, 0);
lean_inc(v_ref_153_);
v_xs_154_ = lean_ctor_get(v_x_107_, 1);
lean_inc_ref(v_xs_154_);
lean_dec_ref_known(v_x_107_, 2);
v_ref_155_ = lean_ctor_get(v_x_108_, 0);
lean_inc(v_ref_155_);
v_xs_156_ = lean_ctor_get(v_x_108_, 1);
lean_inc_ref(v_xs_156_);
lean_dec_ref_known(v_x_108_, 2);
v___x_157_ = l_Lean_Syntax_structEq(v_ref_153_, v_ref_155_);
lean_dec(v_ref_155_);
lean_dec(v_ref_153_);
if (v___x_157_ == 0)
{
lean_dec_ref(v_xs_156_);
lean_dec_ref(v_xs_154_);
return v___x_157_;
}
else
{
uint8_t v___x_158_; 
v___x_158_ = l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1___redArg(v_xs_154_, v_xs_156_);
lean_dec_ref(v_xs_156_);
lean_dec_ref(v_xs_154_);
return v___x_158_;
}
}
else
{
uint8_t v___x_159_; 
lean_dec_ref_known(v_x_107_, 2);
lean_dec_ref(v_x_108_);
v___x_159_ = 0;
return v___x_159_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_Toml_instBEqValue_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_107_ = stack[0].m_obj;
lean_object* v_x_108_ = stack[1].m_obj;
uint8_t v_res_160_;
v_res_160_ = l_Lake_Toml_instBEqValue_beq(v_x_107_, v_x_108_);
stack->m_num = v_res_160_;
}
uint8_t l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___redArg(lean_object* v_xs_161_, lean_object* v_ys_162_, lean_object* v_x_163_){
_start:
{
lean_object* v_zero_164_; uint8_t v_isZero_165_; 
v_zero_164_ = lean_unsigned_to_nat(0u);
v_isZero_165_ = lean_nat_dec_eq(v_x_163_, v_zero_164_);
if (v_isZero_165_ == 1)
{
lean_dec(v_x_163_);
return v_isZero_165_;
}
else
{
lean_object* v_one_166_; lean_object* v_n_167_; uint8_t v___y_169_; lean_object* v___x_171_; lean_object* v_fst_172_; lean_object* v_snd_173_; lean_object* v___x_174_; lean_object* v_fst_175_; lean_object* v_snd_176_; uint8_t v___x_177_; 
v_one_166_ = lean_unsigned_to_nat(1u);
v_n_167_ = lean_nat_sub(v_x_163_, v_one_166_);
lean_dec(v_x_163_);
v___x_171_ = lean_array_fget_borrowed(v_xs_161_, v_n_167_);
v_fst_172_ = lean_ctor_get(v___x_171_, 0);
v_snd_173_ = lean_ctor_get(v___x_171_, 1);
v___x_174_ = lean_array_fget_borrowed(v_ys_162_, v_n_167_);
v_fst_175_ = lean_ctor_get(v___x_174_, 0);
v_snd_176_ = lean_ctor_get(v___x_174_, 1);
v___x_177_ = lean_name_eq(v_fst_172_, v_fst_175_);
if (v___x_177_ == 0)
{
v___y_169_ = v___x_177_;
goto v___jp_168_;
}
else
{
uint8_t v___x_178_; 
lean_inc(v_snd_176_);
lean_inc(v_snd_173_);
v___x_178_ = l_Lake_Toml_instBEqValue_beq(v_snd_173_, v_snd_176_);
v___y_169_ = v___x_178_;
goto v___jp_168_;
}
v___jp_168_:
{
if (v___y_169_ == 0)
{
lean_dec(v_n_167_);
return v___y_169_;
}
else
{
v_x_163_ = v_n_167_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_161_ = stack[0].m_obj;
lean_object* v_ys_162_ = stack[1].m_obj;
lean_object* v_x_163_ = stack[2].m_obj;
uint8_t v_res_179_;
v_res_179_ = l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___redArg(v_xs_161_, v_ys_162_, v_x_163_);
stack->m_num = v_res_179_;
}
uint8_t l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1___redArg(lean_object* v_self_180_, lean_object* v_other_181_){
_start:
{
lean_object* v_items_182_; lean_object* v_items_183_; lean_object* v___x_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v_items_182_ = lean_ctor_get(v_self_180_, 0);
v_items_183_ = lean_ctor_get(v_other_181_, 0);
v___x_184_ = lean_array_get_size(v_items_182_);
v___x_185_ = lean_array_get_size(v_items_183_);
v___x_186_ = lean_nat_dec_eq(v___x_184_, v___x_185_);
if (v___x_186_ == 0)
{
return v___x_186_;
}
else
{
uint8_t v___x_187_; 
v___x_187_ = l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___redArg(v_items_182_, v_items_183_, v___x_184_);
return v___x_187_;
}
}
}
LEAN_EXPORT void l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_180_ = stack[0].m_obj;
lean_object* v_other_181_ = stack[1].m_obj;
uint8_t v_res_188_;
v_res_188_ = l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1___redArg(v_self_180_, v_other_181_);
stack->m_num = v_res_188_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1___redArg___boxed(lean_object* v_self_189_, lean_object* v_other_190_){
_start:
{
uint8_t v_res_191_; lean_object* v_r_192_; 
v_res_191_ = l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1___redArg(v_self_189_, v_other_190_);
lean_dec_ref(v_other_190_);
lean_dec_ref(v_self_189_);
v_r_192_ = lean_box(v_res_191_);
return v_r_192_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0___redArg___boxed(lean_object* v_xs_193_, lean_object* v_ys_194_, lean_object* v_x_195_){
_start:
{
uint8_t v_res_196_; lean_object* v_r_197_; 
v_res_196_ = l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0___redArg(v_xs_193_, v_ys_194_, v_x_195_);
lean_dec_ref(v_ys_194_);
lean_dec_ref(v_xs_193_);
v_r_197_ = lean_box(v_res_196_);
return v_r_197_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___redArg___boxed(lean_object* v_xs_198_, lean_object* v_ys_199_, lean_object* v_x_200_){
_start:
{
uint8_t v_res_201_; lean_object* v_r_202_; 
v_res_201_ = l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___redArg(v_xs_198_, v_ys_199_, v_x_200_);
lean_dec_ref(v_ys_199_);
lean_dec_ref(v_xs_198_);
v_r_202_ = lean_box(v_res_201_);
return v_r_202_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instBEqValue_beq___boxed(lean_object* v_x_203_, lean_object* v_x_204_){
_start:
{
uint8_t v_res_205_; lean_object* v_r_206_; 
v_res_205_ = l_Lake_Toml_instBEqValue_beq(v_x_203_, v_x_204_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
uint8_t l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0(lean_object* v_xs_207_, lean_object* v_ys_208_, lean_object* v_hsz_209_, lean_object* v_x_210_, lean_object* v_x_211_){
_start:
{
uint8_t v___x_212_; 
v___x_212_ = l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0___redArg(v_xs_207_, v_ys_208_, v_x_210_);
return v___x_212_;
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_207_ = stack[0].m_obj;
lean_object* v_ys_208_ = stack[1].m_obj;
lean_object* v_x_210_ = stack[3].m_obj;
uint8_t v_res_213_;
v_res_213_ = l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0(v_xs_207_, v_ys_208_, lean_box(0), v_x_210_, lean_box(0));
stack->m_num = v_res_213_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0___boxed(lean_object* v_xs_214_, lean_object* v_ys_215_, lean_object* v_hsz_216_, lean_object* v_x_217_, lean_object* v_x_218_){
_start:
{
uint8_t v_res_219_; lean_object* v_r_220_; 
v_res_219_ = l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0(v_xs_214_, v_ys_215_, v_hsz_216_, v_x_217_, v_x_218_);
lean_dec_ref(v_ys_215_);
lean_dec_ref(v_xs_214_);
v_r_220_ = lean_box(v_res_219_);
return v_r_220_;
}
}
uint8_t l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1(lean_object* v_cmp_221_, lean_object* v_self_222_, lean_object* v_other_223_){
_start:
{
uint8_t v___x_224_; 
v___x_224_ = l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1___redArg(v_self_222_, v_other_223_);
return v___x_224_;
}
}
LEAN_EXPORT void l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_221_ = stack[0].m_obj;
lean_object* v_self_222_ = stack[1].m_obj;
lean_object* v_other_223_ = stack[2].m_obj;
uint8_t v_res_225_;
v_res_225_ = l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1(v_cmp_221_, v_self_222_, v_other_223_);
stack->m_num = v_res_225_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1___boxed(lean_object* v_cmp_226_, lean_object* v_self_227_, lean_object* v_other_228_){
_start:
{
uint8_t v_res_229_; lean_object* v_r_230_; 
v_res_229_ = l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1(v_cmp_226_, v_self_227_, v_other_228_);
lean_dec_ref(v_other_228_);
lean_dec_ref(v_self_227_);
lean_dec_ref(v_cmp_226_);
v_r_230_ = lean_box(v_res_229_);
return v_r_230_;
}
}
uint8_t l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1(lean_object* v_xs_231_, lean_object* v_ys_232_, lean_object* v_hsz_233_, lean_object* v_x_234_, lean_object* v_x_235_){
_start:
{
uint8_t v___x_236_; 
v___x_236_ = l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___redArg(v_xs_231_, v_ys_232_, v_x_234_);
return v___x_236_;
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_231_ = stack[0].m_obj;
lean_object* v_ys_232_ = stack[1].m_obj;
lean_object* v_x_234_ = stack[3].m_obj;
uint8_t v_res_237_;
v_res_237_ = l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1(v_xs_231_, v_ys_232_, lean_box(0), v_x_234_, lean_box(0));
stack->m_num = v_res_237_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___boxed(lean_object* v_xs_238_, lean_object* v_ys_239_, lean_object* v_hsz_240_, lean_object* v_x_241_, lean_object* v_x_242_){
_start:
{
uint8_t v_res_243_; lean_object* v_r_244_; 
v_res_243_ = l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1(v_xs_238_, v_ys_239_, v_hsz_240_, v_x_241_, v_x_242_);
lean_dec_ref(v_ys_239_);
lean_dec_ref(v_xs_238_);
v_r_244_ = lean_box(v_res_243_);
return v_r_244_;
}
}
static lean_object* _init_l_Lake_Toml_Table_empty___closed__0(void){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Lake_Toml_RBDict_empty___redArg();
return v___x_247_;
}
}
static lean_object* _init_l_Lake_Toml_Table_empty(void){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = lean_obj_once(&l_Lake_Toml_Table_empty___closed__0, &l_Lake_Toml_Table_empty___closed__0_once, _init_l_Lake_Toml_Table_empty___closed__0);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_mkEmpty(lean_object* v_capacity_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Lake_Toml_RBDict_mkEmpty___redArg(v_capacity_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_mkEmpty___boxed(lean_object* v_capacity_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lake_Toml_Table_mkEmpty(v_capacity_251_);
lean_dec(v_capacity_251_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_table(lean_object* v_ref_253_, lean_object* v_t_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_255_, 0, v_ref_253_);
lean_ctor_set(v___x_255_, 1, v_t_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_ref(lean_object* v_x_256_){
_start:
{
lean_object* v_ref_257_; 
v_ref_257_ = lean_ctor_get(v_x_256_, 0);
lean_inc(v_ref_257_);
return v_ref_257_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_ref___boxed(lean_object* v_x_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lake_Toml_Value_ref(v_x_258_);
lean_dec_ref(v_x_258_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg(lean_object* v___x_268_, lean_object* v_s_269_, lean_object* v_a_270_, lean_object* v_b_271_){
_start:
{
uint8_t v_decide_272_; 
v_decide_272_ = lean_nat_dec_eq(v_a_270_, v___x_268_);
if (v_decide_272_ == 0)
{
uint32_t v___x_273_; lean_object* v___x_274_; uint32_t v___x_287_; uint8_t v___x_288_; 
v___x_273_ = lean_string_utf8_get_fast(v_s_269_, v_a_270_);
v___x_274_ = lean_string_utf8_next_fast(v_s_269_, v_a_270_);
lean_dec(v_a_270_);
v___x_287_ = 8;
v___x_288_ = lean_uint32_dec_eq(v___x_273_, v___x_287_);
if (v___x_288_ == 0)
{
uint32_t v___x_289_; uint8_t v___x_290_; 
v___x_289_ = 9;
v___x_290_ = lean_uint32_dec_eq(v___x_273_, v___x_289_);
if (v___x_290_ == 0)
{
uint32_t v___x_291_; uint8_t v___x_292_; 
v___x_291_ = 10;
v___x_292_ = lean_uint32_dec_eq(v___x_273_, v___x_291_);
if (v___x_292_ == 0)
{
uint32_t v___x_293_; uint8_t v___x_294_; 
v___x_293_ = 12;
v___x_294_ = lean_uint32_dec_eq(v___x_273_, v___x_293_);
if (v___x_294_ == 0)
{
uint32_t v___x_295_; uint8_t v___x_296_; 
v___x_295_ = 13;
v___x_296_ = lean_uint32_dec_eq(v___x_273_, v___x_295_);
if (v___x_296_ == 0)
{
uint32_t v___x_297_; uint8_t v___x_298_; 
v___x_297_ = 34;
v___x_298_ = lean_uint32_dec_eq(v___x_273_, v___x_297_);
if (v___x_298_ == 0)
{
uint32_t v___x_299_; uint8_t v___x_300_; 
v___x_299_ = 92;
v___x_300_ = lean_uint32_dec_eq(v___x_273_, v___x_299_);
if (v___x_300_ == 0)
{
uint32_t v___x_301_; uint8_t v___x_302_; 
v___x_301_ = 32;
v___x_302_ = lean_uint32_dec_lt(v___x_273_, v___x_301_);
if (v___x_302_ == 0)
{
uint32_t v___x_303_; uint8_t v___x_304_; 
v___x_303_ = 127;
v___x_304_ = lean_uint32_dec_eq(v___x_273_, v___x_303_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; 
v___x_305_ = lean_string_push(v_b_271_, v___x_273_);
v_a_270_ = v___x_274_;
v_b_271_ = v___x_305_;
goto _start;
}
else
{
goto v___jp_275_;
}
}
else
{
goto v___jp_275_;
}
}
else
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__1));
v___x_308_ = lean_string_append(v_b_271_, v___x_307_);
v_a_270_ = v___x_274_;
v_b_271_ = v___x_308_;
goto _start;
}
}
else
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__2));
v___x_311_ = lean_string_append(v_b_271_, v___x_310_);
v_a_270_ = v___x_274_;
v_b_271_ = v___x_311_;
goto _start;
}
}
else
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__3));
v___x_314_ = lean_string_append(v_b_271_, v___x_313_);
v_a_270_ = v___x_274_;
v_b_271_ = v___x_314_;
goto _start;
}
}
else
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__4));
v___x_317_ = lean_string_append(v_b_271_, v___x_316_);
v_a_270_ = v___x_274_;
v_b_271_ = v___x_317_;
goto _start;
}
}
else
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__5));
v___x_320_ = lean_string_append(v_b_271_, v___x_319_);
v_a_270_ = v___x_274_;
v_b_271_ = v___x_320_;
goto _start;
}
}
else
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__6));
v___x_323_ = lean_string_append(v_b_271_, v___x_322_);
v_a_270_ = v___x_274_;
v_b_271_ = v___x_323_;
goto _start;
}
}
else
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__7));
v___x_326_ = lean_string_append(v_b_271_, v___x_325_);
v_a_270_ = v___x_274_;
v_b_271_ = v___x_326_;
goto _start;
}
v___jp_275_:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; uint32_t v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_276_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__0));
v___x_277_ = lean_string_append(v_b_271_, v___x_276_);
v___x_278_ = lean_unsigned_to_nat(16u);
v___x_279_ = lean_uint32_to_nat(v___x_273_);
v___x_280_ = l_Nat_toDigits(v___x_278_, v___x_279_);
v___x_281_ = lean_string_mk(v___x_280_);
v___x_282_ = 48;
v___x_283_ = lean_unsigned_to_nat(4u);
v___x_284_ = l_Lake_lpadAscii(v___x_281_, v___x_282_, v___x_283_);
lean_dec_ref(v___x_281_);
v___x_285_ = lean_string_append(v___x_277_, v___x_284_);
lean_dec_ref(v___x_284_);
v_a_270_ = v___x_274_;
v_b_271_ = v___x_285_;
goto _start;
}
}
else
{
lean_dec(v_a_270_);
return v_b_271_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___boxed(lean_object* v___x_328_, lean_object* v_s_329_, lean_object* v_a_330_, lean_object* v_b_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg(v___x_328_, v_s_329_, v_a_330_, v_b_331_);
lean_dec_ref(v_s_329_);
lean_dec(v___x_328_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppString(lean_object* v_s_334_){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v_s_338_; uint32_t v___x_339_; lean_object* v___x_340_; 
v___x_335_ = ((lean_object*)(l_Lake_Toml_ppString___closed__0));
v___x_336_ = lean_string_utf8_byte_size(v_s_334_);
v___x_337_ = lean_unsigned_to_nat(0u);
v_s_338_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg(v___x_336_, v_s_334_, v___x_337_, v___x_335_);
v___x_339_ = 34;
v___x_340_ = lean_string_push(v_s_338_, v___x_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppString___boxed(lean_object* v_s_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lake_Toml_ppString(v_s_341_);
lean_dec_ref(v_s_341_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0(lean_object* v___x_343_, lean_object* v___x_344_, lean_object* v_s_345_, lean_object* v_inst_346_, lean_object* v_R_347_, lean_object* v_a_348_, lean_object* v_b_349_, lean_object* v_c_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg(v___x_344_, v_s_345_, v_a_348_, v_b_349_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___boxed(lean_object* v___x_352_, lean_object* v___x_353_, lean_object* v_s_354_, lean_object* v_inst_355_, lean_object* v_R_356_, lean_object* v_a_357_, lean_object* v_b_358_, lean_object* v_c_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0(v___x_352_, v___x_353_, v_s_354_, v_inst_355_, v_R_356_, v_a_357_, v_b_358_, v_c_359_);
lean_dec_ref(v_s_354_);
lean_dec(v___x_353_);
lean_dec_ref(v___x_352_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lake_Toml_ppSimpleKey_spec__0(lean_object* v_s_361_, lean_object* v_pos_362_){
_start:
{
lean_object* v_str_363_; lean_object* v_startInclusive_364_; lean_object* v_endExclusive_365_; lean_object* v___x_366_; lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v_decide_377_; 
v_str_363_ = lean_ctor_get(v_s_361_, 0);
v_startInclusive_364_ = lean_ctor_get(v_s_361_, 1);
v_endExclusive_365_ = lean_ctor_get(v_s_361_, 2);
v___x_366_ = lean_nat_add(v_startInclusive_364_, v_pos_362_);
v___x_375_ = lean_unsigned_to_nat(0u);
v___x_376_ = lean_nat_sub(v_endExclusive_365_, v___x_366_);
v_decide_377_ = lean_nat_dec_eq(v___x_375_, v___x_376_);
lean_dec(v___x_376_);
if (v_decide_377_ == 0)
{
uint32_t v___x_378_; uint32_t v___x_394_; uint8_t v___x_395_; 
v___x_378_ = lean_string_utf8_get_fast(v_str_363_, v___x_366_);
v___x_394_ = 65;
v___x_395_ = lean_uint32_dec_le(v___x_394_, v___x_378_);
if (v___x_395_ == 0)
{
goto v___jp_389_;
}
else
{
uint32_t v___x_396_; uint8_t v___x_397_; 
v___x_396_ = 90;
v___x_397_ = lean_uint32_dec_le(v___x_378_, v___x_396_);
if (v___x_397_ == 0)
{
goto v___jp_389_;
}
else
{
goto v___jp_367_;
}
}
v___jp_379_:
{
uint32_t v___x_380_; uint8_t v___x_381_; 
v___x_380_ = 95;
v___x_381_ = lean_uint32_dec_eq(v___x_378_, v___x_380_);
if (v___x_381_ == 0)
{
uint32_t v___x_382_; uint8_t v___x_383_; 
v___x_382_ = 45;
v___x_383_ = lean_uint32_dec_eq(v___x_378_, v___x_382_);
if (v___x_383_ == 0)
{
lean_dec(v___x_366_);
return v_pos_362_;
}
else
{
goto v___jp_367_;
}
}
else
{
goto v___jp_367_;
}
}
v___jp_384_:
{
uint32_t v___x_385_; uint8_t v___x_386_; 
v___x_385_ = 48;
v___x_386_ = lean_uint32_dec_le(v___x_385_, v___x_378_);
if (v___x_386_ == 0)
{
goto v___jp_379_;
}
else
{
uint32_t v___x_387_; uint8_t v___x_388_; 
v___x_387_ = 57;
v___x_388_ = lean_uint32_dec_le(v___x_378_, v___x_387_);
if (v___x_388_ == 0)
{
goto v___jp_379_;
}
else
{
goto v___jp_367_;
}
}
}
v___jp_389_:
{
uint32_t v___x_390_; uint8_t v___x_391_; 
v___x_390_ = 97;
v___x_391_ = lean_uint32_dec_le(v___x_390_, v___x_378_);
if (v___x_391_ == 0)
{
goto v___jp_384_;
}
else
{
uint32_t v___x_392_; uint8_t v___x_393_; 
v___x_392_ = 122;
v___x_393_ = lean_uint32_dec_le(v___x_378_, v___x_392_);
if (v___x_393_ == 0)
{
goto v___jp_384_;
}
else
{
goto v___jp_367_;
}
}
}
}
else
{
lean_dec(v___x_366_);
return v_pos_362_;
}
v___jp_367_:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_368_ = lean_string_utf8_next_fast(v_str_363_, v___x_366_);
v___x_369_ = lean_nat_sub(v___x_368_, v___x_366_);
lean_dec(v___x_366_);
v___x_370_ = lean_nat_add(v_pos_362_, v___x_369_);
lean_dec(v___x_369_);
v___x_371_ = lean_unsigned_to_nat(1u);
v___x_372_ = lean_nat_add(v_pos_362_, v___x_371_);
v___x_373_ = lean_nat_dec_le(v___x_372_, v___x_370_);
lean_dec(v___x_372_);
if (v___x_373_ == 0)
{
lean_dec(v___x_370_);
return v_pos_362_;
}
else
{
lean_dec(v_pos_362_);
v_pos_362_ = v___x_370_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lake_Toml_ppSimpleKey_spec__0___boxed(lean_object* v_s_398_, lean_object* v_pos_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_String_Slice_Pos_skipWhile___at___00Lake_Toml_ppSimpleKey_spec__0(v_s_398_, v_pos_399_);
lean_dec_ref(v_s_398_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppSimpleKey(lean_object* v_k_401_){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v_decide_406_; 
v___x_402_ = lean_unsigned_to_nat(0u);
v___x_403_ = lean_string_utf8_byte_size(v_k_401_);
lean_inc_ref(v_k_401_);
v___x_404_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_404_, 0, v_k_401_);
lean_ctor_set(v___x_404_, 1, v___x_402_);
lean_ctor_set(v___x_404_, 2, v___x_403_);
v___x_405_ = l_String_Slice_Pos_skipWhile___at___00Lake_Toml_ppSimpleKey_spec__0(v___x_404_, v___x_402_);
lean_dec_ref_known(v___x_404_, 3);
v_decide_406_ = lean_nat_dec_eq(v___x_405_, v___x_403_);
lean_dec(v___x_405_);
if (v_decide_406_ == 0)
{
lean_object* v___x_407_; 
v___x_407_ = l_Lake_Toml_ppString(v_k_401_);
lean_dec_ref(v_k_401_);
return v___x_407_;
}
else
{
return v_k_401_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppKey(lean_object* v_k_409_){
_start:
{
if (lean_obj_tag(v_k_409_) == 1)
{
lean_object* v_pre_410_; lean_object* v_str_411_; uint8_t v___x_412_; 
v_pre_410_ = lean_ctor_get(v_k_409_, 0);
lean_inc(v_pre_410_);
v_str_411_ = lean_ctor_get(v_k_409_, 1);
lean_inc_ref(v_str_411_);
lean_dec_ref_known(v_k_409_, 2);
v___x_412_ = l_Lean_Name_isAnonymous(v_pre_410_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_413_ = l_Lake_Toml_ppKey(v_pre_410_);
v___x_414_ = ((lean_object*)(l_Lake_Toml_ppKey___closed__0));
v___x_415_ = lean_string_append(v___x_413_, v___x_414_);
v___x_416_ = l_Lake_Toml_ppSimpleKey(v_str_411_);
v___x_417_ = lean_string_append(v___x_415_, v___x_416_);
lean_dec_ref(v___x_416_);
return v___x_417_;
}
else
{
lean_object* v___x_418_; 
lean_dec(v_pre_410_);
v___x_418_ = l_Lake_Toml_ppSimpleKey(v_str_411_);
return v___x_418_;
}
}
else
{
lean_object* v___x_419_; 
lean_dec(v_k_409_);
v___x_419_ = ((lean_object*)(l_Lake_Toml_instInhabitedValue_default___closed__0));
return v___x_419_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0(size_t v_sz_426_, size_t v_i_427_, lean_object* v_bs_428_){
_start:
{
uint8_t v___x_429_; 
v___x_429_ = lean_usize_dec_lt(v_i_427_, v_sz_426_);
if (v___x_429_ == 0)
{
return v_bs_428_;
}
else
{
lean_object* v_v_430_; lean_object* v_fst_431_; lean_object* v_snd_432_; lean_object* v___x_433_; lean_object* v_bs_x27_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; size_t v___x_440_; size_t v___x_441_; lean_object* v___x_442_; 
v_v_430_ = lean_array_uget_borrowed(v_bs_428_, v_i_427_);
v_fst_431_ = lean_ctor_get(v_v_430_, 0);
lean_inc(v_fst_431_);
v_snd_432_ = lean_ctor_get(v_v_430_, 1);
lean_inc(v_snd_432_);
v___x_433_ = lean_unsigned_to_nat(0u);
v_bs_x27_434_ = lean_array_uset(v_bs_428_, v_i_427_, v___x_433_);
v___x_435_ = l_Lake_Toml_ppKey(v_fst_431_);
v___x_436_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___closed__0));
v___x_437_ = lean_string_append(v___x_435_, v___x_436_);
v___x_438_ = l_Lake_Toml_Value_toString(v_snd_432_);
v___x_439_ = lean_string_append(v___x_437_, v___x_438_);
lean_dec_ref(v___x_438_);
v___x_440_ = ((size_t)1ULL);
v___x_441_ = lean_usize_add(v_i_427_, v___x_440_);
v___x_442_ = lean_array_uset(v_bs_x27_434_, v_i_427_, v___x_439_);
v_i_427_ = v___x_441_;
v_bs_428_ = v___x_442_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_426_ = stack[0].m_num;
size_t v_i_427_ = stack[1].m_num;
lean_object* v_bs_428_ = stack[2].m_obj;
lean_object* v_res_444_;
v_res_444_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0(v_sz_426_, v_i_427_, v_bs_428_);
stack->m_obj
 = v_res_444_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppInlineTable(lean_object* v_t_447_){
_start:
{
lean_object* v_items_448_; size_t v_sz_449_; size_t v___x_450_; lean_object* v_xs_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v_items_448_ = lean_ctor_get(v_t_447_, 0);
lean_inc_ref(v_items_448_);
lean_dec_ref(v_t_447_);
v_sz_449_ = lean_array_size(v_items_448_);
v___x_450_ = ((size_t)0ULL);
v_xs_451_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0(v_sz_449_, v___x_450_, v_items_448_);
v___x_452_ = ((lean_object*)(l_Lake_Toml_ppInlineTable___closed__0));
v___x_453_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__1));
v___x_454_ = lean_array_to_list(v_xs_451_);
v___x_455_ = l_String_intercalate(v___x_453_, v___x_454_);
v___x_456_ = lean_string_append(v___x_452_, v___x_455_);
lean_dec_ref(v___x_455_);
v___x_457_ = ((lean_object*)(l_Lake_Toml_ppInlineTable___closed__1));
v___x_458_ = lean_string_append(v___x_456_, v___x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_toString(lean_object* v_v_459_){
_start:
{
switch(lean_obj_tag(v_v_459_))
{
case 0:
{
lean_object* v_s_460_; lean_object* v___x_461_; 
v_s_460_ = lean_ctor_get(v_v_459_, 1);
lean_inc_ref(v_s_460_);
lean_dec_ref_known(v_v_459_, 2);
v___x_461_ = l_Lake_Toml_ppString(v_s_460_);
lean_dec_ref(v_s_460_);
return v___x_461_;
}
case 1:
{
lean_object* v_n_462_; lean_object* v___x_463_; 
v_n_462_ = lean_ctor_get(v_v_459_, 1);
lean_inc(v_n_462_);
lean_dec_ref_known(v_v_459_, 2);
v___x_463_ = l_Int_repr(v_n_462_);
lean_dec(v_n_462_);
return v___x_463_;
}
case 2:
{
double v_n_464_; lean_object* v___x_465_; 
v_n_464_ = lean_ctor_get_float(v_v_459_, sizeof(void*)*1);
lean_dec_ref_known(v_v_459_, 1);
v___x_465_ = lean_float_to_string(v_n_464_);
return v___x_465_;
}
case 3:
{
uint8_t v_b_466_; 
v_b_466_ = lean_ctor_get_uint8(v_v_459_, sizeof(void*)*1);
lean_dec_ref_known(v_v_459_, 1);
if (v_b_466_ == 0)
{
lean_object* v___x_467_; 
v___x_467_ = ((lean_object*)(l_Lake_Toml_Value_toString___closed__0));
return v___x_467_;
}
else
{
lean_object* v___x_468_; 
v___x_468_ = ((lean_object*)(l_Lake_Toml_Value_toString___closed__1));
return v___x_468_;
}
}
case 4:
{
lean_object* v_dt_469_; lean_object* v___x_470_; 
v_dt_469_ = lean_ctor_get(v_v_459_, 1);
lean_inc_ref(v_dt_469_);
lean_dec_ref_known(v_v_459_, 2);
v___x_470_ = l_Lake_Toml_DateTime_toString(v_dt_469_);
return v___x_470_;
}
case 5:
{
lean_object* v_xs_471_; lean_object* v___x_472_; 
v_xs_471_ = lean_ctor_get(v_v_459_, 1);
lean_inc_ref(v_xs_471_);
lean_dec_ref_known(v_v_459_, 2);
v___x_472_ = l_Lake_Toml_ppInlineArray(v_xs_471_);
return v___x_472_;
}
default: 
{
lean_object* v_xs_473_; lean_object* v___x_474_; 
v_xs_473_ = lean_ctor_get(v_v_459_, 1);
lean_inc_ref(v_xs_473_);
lean_dec_ref_known(v_v_459_, 2);
v___x_474_ = l_Lake_Toml_ppInlineTable(v_xs_473_);
return v___x_474_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3(size_t v_sz_475_, size_t v_i_476_, lean_object* v_bs_477_){
_start:
{
uint8_t v___x_478_; 
v___x_478_ = lean_usize_dec_lt(v_i_476_, v_sz_475_);
if (v___x_478_ == 0)
{
return v_bs_477_;
}
else
{
lean_object* v_v_479_; lean_object* v___x_480_; lean_object* v_bs_x27_481_; lean_object* v___x_482_; size_t v___x_483_; size_t v___x_484_; lean_object* v___x_485_; 
v_v_479_ = lean_array_uget(v_bs_477_, v_i_476_);
v___x_480_ = lean_unsigned_to_nat(0u);
v_bs_x27_481_ = lean_array_uset(v_bs_477_, v_i_476_, v___x_480_);
v___x_482_ = l_Lake_Toml_Value_toString(v_v_479_);
v___x_483_ = ((size_t)1ULL);
v___x_484_ = lean_usize_add(v_i_476_, v___x_483_);
v___x_485_ = lean_array_uset(v_bs_x27_481_, v_i_476_, v___x_482_);
v_i_476_ = v___x_484_;
v_bs_477_ = v___x_485_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_sz_475_ = stack[0].m_num;
size_t v_i_476_ = stack[1].m_num;
lean_object* v_bs_477_ = stack[2].m_obj;
lean_object* v_res_487_;
v_res_487_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3(v_sz_475_, v_i_476_, v_bs_477_);
stack->m_obj
 = v_res_487_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppInlineArray(lean_object* v_vs_488_){
_start:
{
size_t v_sz_489_; size_t v___x_490_; lean_object* v_xs_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v_sz_489_ = lean_array_size(v_vs_488_);
v___x_490_ = ((size_t)0ULL);
v_xs_491_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3(v_sz_489_, v___x_490_, v_vs_488_);
v___x_492_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__0));
v___x_493_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__1));
v___x_494_ = lean_array_to_list(v_xs_491_);
v___x_495_ = l_String_intercalate(v___x_493_, v___x_494_);
v___x_496_ = lean_string_append(v___x_492_, v___x_495_);
lean_dec_ref(v___x_495_);
v___x_497_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__2));
v___x_498_ = lean_string_append(v___x_496_, v___x_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3___boxed(lean_object* v_sz_499_, lean_object* v_i_500_, lean_object* v_bs_501_){
_start:
{
size_t v_sz_boxed_502_; size_t v_i_boxed_503_; lean_object* v_res_504_; 
v_sz_boxed_502_ = lean_unbox_usize(v_sz_499_);
lean_dec(v_sz_499_);
v_i_boxed_503_ = lean_unbox_usize(v_i_500_);
lean_dec(v_i_500_);
v_res_504_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3(v_sz_boxed_502_, v_i_boxed_503_, v_bs_501_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___boxed(lean_object* v_sz_505_, lean_object* v_i_506_, lean_object* v_bs_507_){
_start:
{
size_t v_sz_boxed_508_; size_t v_i_boxed_509_; lean_object* v_res_510_; 
v_sz_boxed_508_ = lean_unbox_usize(v_sz_505_);
lean_dec(v_sz_505_);
v_i_boxed_509_ = lean_unbox_usize(v_i_506_);
lean_dec(v_i_506_);
v_res_510_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0(v_sz_boxed_508_, v_i_boxed_509_, v_bs_507_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval(lean_object* v_s_514_, lean_object* v_k_515_, lean_object* v_v_516_){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_517_ = l_Lake_Toml_ppKey(v_k_515_);
v___x_518_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___closed__0));
v___x_519_ = lean_string_append(v___x_517_, v___x_518_);
v___x_520_ = l_Lake_Toml_Value_toString(v_v_516_);
v___x_521_ = lean_string_append(v___x_519_, v___x_520_);
lean_dec_ref(v___x_520_);
v___x_522_ = ((lean_object*)(l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval___closed__0));
v___x_523_ = lean_string_append(v___x_521_, v___x_522_);
v___x_524_ = lean_string_append(v_s_514_, v___x_523_);
lean_dec_ref(v___x_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lake_Toml_ppTable_spec__2(lean_object* v_msg_525_){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = ((lean_object*)(l_Lake_Toml_instInhabitedValue_default___closed__0));
v___x_527_ = lean_panic_fn_borrowed(v___x_526_, v_msg_525_);
return v___x_527_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(lean_object* v_as_528_, size_t v_i_529_, size_t v_stop_530_, lean_object* v_b_531_){
_start:
{
uint8_t v___x_532_; 
v___x_532_ = lean_usize_dec_eq(v_i_529_, v_stop_530_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; lean_object* v_fst_534_; lean_object* v_snd_535_; lean_object* v___x_536_; size_t v___x_537_; size_t v___x_538_; 
v___x_533_ = lean_array_uget_borrowed(v_as_528_, v_i_529_);
v_fst_534_ = lean_ctor_get(v___x_533_, 0);
v_snd_535_ = lean_ctor_get(v___x_533_, 1);
lean_inc(v_snd_535_);
lean_inc(v_fst_534_);
v___x_536_ = l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval(v_b_531_, v_fst_534_, v_snd_535_);
v___x_537_ = ((size_t)1ULL);
v___x_538_ = lean_usize_add(v_i_529_, v___x_537_);
v_i_529_ = v___x_538_;
v_b_531_ = v___x_536_;
goto _start;
}
else
{
return v_b_531_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_528_ = stack[0].m_obj;
size_t v_i_529_ = stack[1].m_num;
size_t v_stop_530_ = stack[2].m_num;
lean_object* v_b_531_ = stack[3].m_obj;
lean_object* v_res_540_;
v_res_540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_as_528_, v_i_529_, v_stop_530_, v_b_531_);
stack->m_obj
 = v_res_540_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1___boxed(lean_object* v_as_541_, lean_object* v_i_542_, lean_object* v_stop_543_, lean_object* v_b_544_){
_start:
{
size_t v_i_boxed_545_; size_t v_stop_boxed_546_; lean_object* v_res_547_; 
v_i_boxed_545_ = lean_unbox_usize(v_i_542_);
lean_dec(v_i_542_);
v_stop_boxed_546_ = lean_unbox_usize(v_stop_543_);
lean_dec(v_stop_543_);
v_res_547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_as_541_, v_i_boxed_545_, v_stop_boxed_546_, v_b_544_);
lean_dec_ref(v_as_541_);
return v_res_547_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5(void){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_553_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__4));
v___x_554_ = lean_unsigned_to_nat(17u);
v___x_555_ = lean_unsigned_to_nat(128u);
v___x_556_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__3));
v___x_557_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__2));
v___x_558_ = l_mkPanicMessageWithDecl(v___x_557_, v___x_556_, v___x_555_, v___x_554_, v___x_553_);
return v___x_558_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3(lean_object* v_fst_559_, lean_object* v_as_560_, size_t v_i_561_, size_t v_stop_562_, lean_object* v_b_563_){
_start:
{
lean_object* v___y_565_; lean_object* v___y_570_; uint8_t v___x_573_; 
v___x_573_ = lean_usize_dec_eq(v_i_561_, v_stop_562_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; 
v___x_574_ = lean_array_uget_borrowed(v_as_560_, v_i_561_);
if (lean_obj_tag(v___x_574_) == 6)
{
lean_object* v_xs_575_; lean_object* v_items_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v_s_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
v_xs_575_ = lean_ctor_get(v___x_574_, 1);
v_items_576_ = lean_ctor_get(v_xs_575_, 0);
v___x_577_ = lean_unsigned_to_nat(0u);
v___x_578_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__0));
lean_inc(v_fst_559_);
v___x_579_ = l_Lake_Toml_ppKey(v_fst_559_);
v___x_580_ = lean_string_append(v___x_578_, v___x_579_);
lean_dec_ref(v___x_579_);
v___x_581_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__1));
v___x_582_ = lean_string_append(v___x_580_, v___x_581_);
v_s_583_ = lean_string_append(v_b_563_, v___x_582_);
lean_dec_ref(v___x_582_);
v___x_584_ = lean_array_get_size(v_items_576_);
v___x_585_ = lean_nat_dec_lt(v___x_577_, v___x_584_);
if (v___x_585_ == 0)
{
v___y_570_ = v_s_583_;
goto v___jp_569_;
}
else
{
uint8_t v___x_586_; 
v___x_586_ = lean_nat_dec_le(v___x_584_, v___x_584_);
if (v___x_586_ == 0)
{
if (v___x_585_ == 0)
{
v___y_570_ = v_s_583_;
goto v___jp_569_;
}
else
{
size_t v___x_587_; size_t v___x_588_; lean_object* v___x_589_; 
v___x_587_ = ((size_t)0ULL);
v___x_588_ = lean_usize_of_nat(v___x_584_);
v___x_589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_items_576_, v___x_587_, v___x_588_, v_s_583_);
v___y_570_ = v___x_589_;
goto v___jp_569_;
}
}
else
{
size_t v___x_590_; size_t v___x_591_; lean_object* v___x_592_; 
v___x_590_ = ((size_t)0ULL);
v___x_591_ = lean_usize_of_nat(v___x_584_);
v___x_592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_items_576_, v___x_590_, v___x_591_, v_s_583_);
v___y_570_ = v___x_592_;
goto v___jp_569_;
}
}
}
else
{
lean_object* v___x_593_; lean_object* v___x_594_; 
lean_dec_ref(v_b_563_);
v___x_593_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5);
v___x_594_ = l_panic___at___00Lake_Toml_ppTable_spec__2(v___x_593_);
v___y_565_ = v___x_594_;
goto v___jp_564_;
}
}
else
{
lean_dec(v_fst_559_);
return v_b_563_;
}
v___jp_564_:
{
size_t v___x_566_; size_t v___x_567_; 
v___x_566_ = ((size_t)1ULL);
v___x_567_ = lean_usize_add(v_i_561_, v___x_566_);
v_i_561_ = v___x_567_;
v_b_563_ = v___y_565_;
goto _start;
}
v___jp_569_:
{
uint32_t v___x_571_; lean_object* v___x_572_; 
v___x_571_ = 10;
v___x_572_ = lean_string_push(v___y_570_, v___x_571_);
v___y_565_ = v___x_572_;
goto v___jp_564_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_559_ = stack[0].m_obj;
lean_object* v_as_560_ = stack[1].m_obj;
size_t v_i_561_ = stack[2].m_num;
size_t v_stop_562_ = stack[3].m_num;
lean_object* v_b_563_ = stack[4].m_obj;
lean_object* v_res_595_;
v_res_595_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3(v_fst_559_, v_as_560_, v_i_561_, v_stop_562_, v_b_563_);
stack->m_obj
 = v_res_595_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___boxed(lean_object* v_fst_596_, lean_object* v_as_597_, lean_object* v_i_598_, lean_object* v_stop_599_, lean_object* v_b_600_){
_start:
{
size_t v_i_boxed_601_; size_t v_stop_boxed_602_; lean_object* v_res_603_; 
v_i_boxed_601_ = lean_unbox_usize(v_i_598_);
lean_dec(v_i_598_);
v_stop_boxed_602_ = lean_unbox_usize(v_stop_599_);
lean_dec(v_stop_599_);
v_res_603_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3(v_fst_596_, v_as_597_, v_i_boxed_601_, v_stop_boxed_602_, v_b_600_);
lean_dec_ref(v_as_597_);
return v_res_603_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Toml_ppTable_spec__4(lean_object* v___x_604_, lean_object* v_as_605_, size_t v_i_606_, size_t v_stop_607_){
_start:
{
uint8_t v___x_608_; 
v___x_608_ = lean_usize_dec_eq(v_i_606_, v_stop_607_);
if (v___x_608_ == 0)
{
uint8_t v___x_609_; lean_object* v___x_610_; 
v___x_609_ = 1;
v___x_610_ = lean_array_uget_borrowed(v_as_605_, v_i_606_);
if (lean_obj_tag(v___x_610_) == 6)
{
lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_611_ = lean_unsigned_to_nat(0u);
v___x_612_ = lean_nat_dec_eq(v___x_604_, v___x_611_);
if (v___x_612_ == 0)
{
size_t v___x_613_; size_t v___x_614_; 
v___x_613_ = ((size_t)1ULL);
v___x_614_ = lean_usize_add(v_i_606_, v___x_613_);
v_i_606_ = v___x_614_;
goto _start;
}
else
{
return v___x_609_;
}
}
else
{
return v___x_609_;
}
}
else
{
uint8_t v___x_616_; 
v___x_616_ = 0;
return v___x_616_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Toml_ppTable_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_604_ = stack[0].m_obj;
lean_object* v_as_605_ = stack[1].m_obj;
size_t v_i_606_ = stack[2].m_num;
size_t v_stop_607_ = stack[3].m_num;
uint8_t v_res_617_;
v_res_617_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Toml_ppTable_spec__4(v___x_604_, v_as_605_, v_i_606_, v_stop_607_);
stack->m_num = v_res_617_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Toml_ppTable_spec__4___boxed(lean_object* v___x_618_, lean_object* v_as_619_, lean_object* v_i_620_, lean_object* v_stop_621_){
_start:
{
size_t v_i_boxed_622_; size_t v_stop_boxed_623_; uint8_t v_res_624_; lean_object* v_r_625_; 
v_i_boxed_622_ = lean_unbox_usize(v_i_620_);
lean_dec(v_i_620_);
v_stop_boxed_623_ = lean_unbox_usize(v_stop_621_);
lean_dec(v_stop_621_);
v_res_624_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Toml_ppTable_spec__4(v___x_618_, v_as_619_, v_i_boxed_622_, v_stop_boxed_623_);
lean_dec_ref(v_as_619_);
lean_dec(v___x_618_);
v_r_625_ = lean_box(v_res_624_);
return v_r_625_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5(lean_object* v_as_628_, size_t v_i_629_, size_t v_stop_630_, lean_object* v_b_631_){
_start:
{
lean_object* v___y_633_; uint8_t v___x_637_; 
v___x_637_ = lean_usize_dec_eq(v_i_629_, v_stop_630_);
if (v___x_637_ == 0)
{
lean_object* v_fst_638_; lean_object* v_snd_639_; lean_object* v___y_641_; lean_object* v___x_645_; lean_object* v_snd_646_; 
v_fst_638_ = lean_ctor_get(v_b_631_, 0);
v_snd_639_ = lean_ctor_get(v_b_631_, 1);
v___x_645_ = lean_array_uget(v_as_628_, v_i_629_);
v_snd_646_ = lean_ctor_get(v___x_645_, 1);
switch(lean_obj_tag(v_snd_646_))
{
case 5:
{
lean_object* v_fst_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_704_; 
lean_inc_ref(v_snd_646_);
v_fst_647_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_704_ == 0)
{
lean_object* v_unused_705_; 
v_unused_705_ = lean_ctor_get(v___x_645_, 1);
lean_dec(v_unused_705_);
v___x_649_ = v___x_645_;
v_isShared_650_ = v_isSharedCheck_704_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_fst_647_);
lean_dec(v___x_645_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_704_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v_xs_651_; lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_669_; 
v_xs_651_ = lean_ctor_get(v_snd_646_, 1);
lean_inc_ref(v_xs_651_);
lean_dec_ref_known(v_snd_646_, 2);
v___x_652_ = lean_array_get_size(v_xs_651_);
v___x_653_ = lean_unsigned_to_nat(0u);
v___x_669_ = lean_nat_dec_eq(v___x_652_, v___x_653_);
if (v___x_669_ == 0)
{
uint8_t v___x_670_; 
v___x_670_ = lean_nat_dec_lt(v___x_653_, v___x_652_);
if (v___x_670_ == 0)
{
goto v___jp_654_;
}
else
{
if (v___x_670_ == 0)
{
goto v___jp_654_;
}
else
{
size_t v___x_671_; size_t v___x_672_; uint8_t v___x_673_; 
v___x_671_ = ((size_t)0ULL);
v___x_672_ = lean_usize_of_nat(v___x_652_);
v___x_673_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Toml_ppTable_spec__4(v___x_652_, v_xs_651_, v___x_671_, v___x_672_);
if (v___x_673_ == 0)
{
goto v___jp_654_;
}
else
{
lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_688_; 
lean_inc(v_snd_639_);
lean_inc(v_fst_638_);
lean_del_object(v___x_649_);
v_isSharedCheck_688_ = !lean_is_exclusive(v_b_631_);
if (v_isSharedCheck_688_ == 0)
{
lean_object* v_unused_689_; lean_object* v_unused_690_; 
v_unused_689_ = lean_ctor_get(v_b_631_, 1);
lean_dec(v_unused_689_);
v_unused_690_ = lean_ctor_get(v_b_631_, 0);
lean_dec(v_unused_690_);
v___x_675_ = v_b_631_;
v_isShared_676_ = v_isSharedCheck_688_;
goto v_resetjp_674_;
}
else
{
lean_dec(v_b_631_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_688_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_686_; 
v___x_677_ = l_Lake_Toml_ppKey(v_fst_647_);
v___x_678_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___closed__0));
v___x_679_ = lean_string_append(v___x_677_, v___x_678_);
v___x_680_ = l_Lake_Toml_ppInlineArray(v_xs_651_);
v___x_681_ = lean_string_append(v___x_679_, v___x_680_);
lean_dec_ref(v___x_680_);
v___x_682_ = ((lean_object*)(l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval___closed__0));
v___x_683_ = lean_string_append(v___x_681_, v___x_682_);
v___x_684_ = lean_string_append(v_fst_638_, v___x_683_);
lean_dec_ref(v___x_683_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 0, v___x_684_);
v___x_686_ = v___x_675_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_684_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_snd_639_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
v___y_633_ = v___x_686_;
goto v___jp_632_;
}
}
}
}
}
}
else
{
lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_701_; 
lean_inc(v_snd_639_);
lean_inc(v_fst_638_);
lean_dec_ref(v_xs_651_);
lean_del_object(v___x_649_);
v_isSharedCheck_701_ = !lean_is_exclusive(v_b_631_);
if (v_isSharedCheck_701_ == 0)
{
lean_object* v_unused_702_; lean_object* v_unused_703_; 
v_unused_702_ = lean_ctor_get(v_b_631_, 1);
lean_dec(v_unused_702_);
v_unused_703_ = lean_ctor_get(v_b_631_, 0);
lean_dec(v_unused_703_);
v___x_692_ = v_b_631_;
v_isShared_693_ = v_isSharedCheck_701_;
goto v_resetjp_691_;
}
else
{
lean_dec(v_b_631_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_701_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_694_ = l_Lake_Toml_ppKey(v_fst_647_);
v___x_695_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___closed__0));
v___x_696_ = lean_string_append(v___x_694_, v___x_695_);
v___x_697_ = lean_string_append(v_fst_638_, v___x_696_);
lean_dec_ref(v___x_696_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v___x_697_);
v___x_699_ = v___x_692_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_snd_639_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
v___y_633_ = v___x_699_;
goto v___jp_632_;
}
}
}
v___jp_654_:
{
uint8_t v___x_655_; 
v___x_655_ = lean_nat_dec_lt(v___x_653_, v___x_652_);
if (v___x_655_ == 0)
{
lean_dec_ref(v_xs_651_);
lean_del_object(v___x_649_);
lean_dec(v_fst_647_);
v___y_633_ = v_b_631_;
goto v___jp_632_;
}
else
{
uint8_t v___x_656_; 
v___x_656_ = lean_nat_dec_le(v___x_652_, v___x_652_);
if (v___x_656_ == 0)
{
if (v___x_655_ == 0)
{
lean_dec_ref(v_xs_651_);
lean_del_object(v___x_649_);
lean_dec(v_fst_647_);
v___y_633_ = v_b_631_;
goto v___jp_632_;
}
else
{
size_t v___x_657_; size_t v___x_658_; lean_object* v___x_659_; lean_object* v___x_661_; 
lean_inc(v_snd_639_);
lean_inc(v_fst_638_);
lean_dec_ref(v_b_631_);
v___x_657_ = ((size_t)0ULL);
v___x_658_ = lean_usize_of_nat(v___x_652_);
v___x_659_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3(v_fst_647_, v_xs_651_, v___x_657_, v___x_658_, v_snd_639_);
lean_dec_ref(v_xs_651_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 1, v___x_659_);
lean_ctor_set(v___x_649_, 0, v_fst_638_);
v___x_661_ = v___x_649_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_fst_638_);
lean_ctor_set(v_reuseFailAlloc_662_, 1, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
v___y_633_ = v___x_661_;
goto v___jp_632_;
}
}
}
else
{
size_t v___x_663_; size_t v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
lean_inc(v_snd_639_);
lean_inc(v_fst_638_);
lean_dec_ref(v_b_631_);
v___x_663_ = ((size_t)0ULL);
v___x_664_ = lean_usize_of_nat(v___x_652_);
v___x_665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3(v_fst_647_, v_xs_651_, v___x_663_, v___x_664_, v_snd_639_);
lean_dec_ref(v_xs_651_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 1, v___x_665_);
lean_ctor_set(v___x_649_, 0, v_fst_638_);
v___x_667_ = v___x_649_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_fst_638_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
v___y_633_ = v___x_667_;
goto v___jp_632_;
}
}
}
}
}
}
case 6:
{
lean_object* v_xs_706_; lean_object* v_fst_707_; lean_object* v_items_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v_fs_714_; lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
lean_inc(v_snd_639_);
lean_inc(v_fst_638_);
lean_dec_ref(v_b_631_);
v_xs_706_ = lean_ctor_get(v_snd_646_, 1);
lean_inc_ref(v_xs_706_);
v_fst_707_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_fst_707_);
lean_dec(v___x_645_);
v_items_708_ = lean_ctor_get(v_xs_706_, 0);
lean_inc_ref(v_items_708_);
lean_dec_ref(v_xs_706_);
v___x_709_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__0));
v___x_710_ = l_Lake_Toml_ppKey(v_fst_707_);
v___x_711_ = lean_string_append(v___x_709_, v___x_710_);
lean_dec_ref(v___x_710_);
v___x_712_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___closed__1));
v___x_713_ = lean_string_append(v___x_711_, v___x_712_);
v_fs_714_ = lean_string_append(v_snd_639_, v___x_713_);
lean_dec_ref(v___x_713_);
v___x_715_ = lean_unsigned_to_nat(0u);
v___x_716_ = lean_array_get_size(v_items_708_);
v___x_717_ = lean_nat_dec_lt(v___x_715_, v___x_716_);
if (v___x_717_ == 0)
{
lean_dec_ref(v_items_708_);
v___y_641_ = v_fs_714_;
goto v___jp_640_;
}
else
{
uint8_t v___x_718_; 
v___x_718_ = lean_nat_dec_le(v___x_716_, v___x_716_);
if (v___x_718_ == 0)
{
if (v___x_717_ == 0)
{
lean_dec_ref(v_items_708_);
v___y_641_ = v_fs_714_;
goto v___jp_640_;
}
else
{
size_t v___x_719_; size_t v___x_720_; lean_object* v___x_721_; 
v___x_719_ = ((size_t)0ULL);
v___x_720_ = lean_usize_of_nat(v___x_716_);
v___x_721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_items_708_, v___x_719_, v___x_720_, v_fs_714_);
lean_dec_ref(v_items_708_);
v___y_641_ = v___x_721_;
goto v___jp_640_;
}
}
else
{
size_t v___x_722_; size_t v___x_723_; lean_object* v___x_724_; 
v___x_722_ = ((size_t)0ULL);
v___x_723_ = lean_usize_of_nat(v___x_716_);
v___x_724_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_items_708_, v___x_722_, v___x_723_, v_fs_714_);
lean_dec_ref(v_items_708_);
v___y_641_ = v___x_724_;
goto v___jp_640_;
}
}
}
default: 
{
lean_object* v_fst_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_733_; 
lean_inc(v_snd_646_);
lean_inc(v_snd_639_);
lean_inc(v_fst_638_);
lean_dec_ref(v_b_631_);
v_fst_725_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_733_ == 0)
{
lean_object* v_unused_734_; 
v_unused_734_ = lean_ctor_get(v___x_645_, 1);
lean_dec(v_unused_734_);
v___x_727_ = v___x_645_;
v_isShared_728_ = v_isSharedCheck_733_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_fst_725_);
lean_dec(v___x_645_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_733_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; lean_object* v___x_731_; 
v___x_729_ = l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval(v_fst_638_, v_fst_725_, v_snd_646_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 1, v_snd_639_);
lean_ctor_set(v___x_727_, 0, v___x_729_);
v___x_731_ = v___x_727_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_729_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_snd_639_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
v___y_633_ = v___x_731_;
goto v___jp_632_;
}
}
}
}
v___jp_640_:
{
uint32_t v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_642_ = 10;
v___x_643_ = lean_string_push(v___y_641_, v___x_642_);
v___x_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_644_, 0, v_fst_638_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
v___y_633_ = v___x_644_;
goto v___jp_632_;
}
}
else
{
return v_b_631_;
}
v___jp_632_:
{
size_t v___x_634_; size_t v___x_635_; 
v___x_634_ = ((size_t)1ULL);
v___x_635_ = lean_usize_add(v_i_629_, v___x_634_);
v_i_629_ = v___x_635_;
v_b_631_ = v___y_633_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_628_ = stack[0].m_obj;
size_t v_i_629_ = stack[1].m_num;
size_t v_stop_630_ = stack[2].m_num;
lean_object* v_b_631_ = stack[3].m_obj;
lean_object* v_res_735_;
v_res_735_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5(v_as_628_, v_i_629_, v_stop_630_, v_b_631_);
stack->m_obj
 = v_res_735_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___boxed(lean_object* v_as_736_, lean_object* v_i_737_, lean_object* v_stop_738_, lean_object* v_b_739_){
_start:
{
size_t v_i_boxed_740_; size_t v_stop_boxed_741_; lean_object* v_res_742_; 
v_i_boxed_740_ = lean_unbox_usize(v_i_737_);
lean_dec(v_i_737_);
v_stop_boxed_741_ = lean_unbox_usize(v_stop_738_);
lean_dec(v_stop_738_);
v_res_742_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5(v_as_736_, v_i_boxed_740_, v_stop_boxed_741_, v_b_739_);
lean_dec_ref(v_as_736_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lake_Toml_ppTable_spec__0(lean_object* v_s_743_, lean_object* v_pos_744_){
_start:
{
lean_object* v_str_745_; lean_object* v_startInclusive_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v_decide_750_; 
v_str_745_ = lean_ctor_get(v_s_743_, 0);
v_startInclusive_746_ = lean_ctor_get(v_s_743_, 1);
v___x_747_ = lean_nat_add(v_startInclusive_746_, v_pos_744_);
v___x_748_ = lean_nat_sub(v___x_747_, v_startInclusive_746_);
v___x_749_ = lean_unsigned_to_nat(0u);
v_decide_750_ = lean_nat_dec_eq(v___x_748_, v___x_749_);
if (v_decide_750_ == 0)
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_759_; uint32_t v___x_760_; uint32_t v___x_761_; uint8_t v___x_762_; 
lean_inc(v_startInclusive_746_);
lean_inc_ref(v_str_745_);
v___x_751_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_751_, 0, v_str_745_);
lean_ctor_set(v___x_751_, 1, v_startInclusive_746_);
lean_ctor_set(v___x_751_, 2, v___x_747_);
v___x_752_ = lean_unsigned_to_nat(1u);
v___x_753_ = lean_nat_sub(v___x_748_, v___x_752_);
lean_dec(v___x_748_);
v___x_754_ = l_String_Slice_posLE(v___x_751_, v___x_753_);
lean_dec_ref_known(v___x_751_, 3);
v___x_759_ = lean_nat_add(v_startInclusive_746_, v___x_754_);
v___x_760_ = lean_string_utf8_get_fast(v_str_745_, v___x_759_);
lean_dec(v___x_759_);
v___x_761_ = 32;
v___x_762_ = lean_uint32_dec_eq(v___x_760_, v___x_761_);
if (v___x_762_ == 0)
{
uint32_t v___x_763_; uint8_t v___x_764_; 
v___x_763_ = 9;
v___x_764_ = lean_uint32_dec_eq(v___x_760_, v___x_763_);
if (v___x_764_ == 0)
{
uint32_t v___x_765_; uint8_t v___x_766_; 
v___x_765_ = 13;
v___x_766_ = lean_uint32_dec_eq(v___x_760_, v___x_765_);
if (v___x_766_ == 0)
{
uint32_t v___x_767_; uint8_t v___x_768_; 
v___x_767_ = 10;
v___x_768_ = lean_uint32_dec_eq(v___x_760_, v___x_767_);
if (v___x_768_ == 0)
{
lean_dec(v___x_754_);
return v_pos_744_;
}
else
{
goto v___jp_755_;
}
}
else
{
goto v___jp_755_;
}
}
else
{
goto v___jp_755_;
}
}
else
{
goto v___jp_755_;
}
v___jp_755_:
{
lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_756_ = lean_nat_add(v___x_754_, v___x_752_);
v___x_757_ = lean_nat_dec_le(v___x_756_, v_pos_744_);
lean_dec(v___x_756_);
if (v___x_757_ == 0)
{
lean_dec(v___x_754_);
return v_pos_744_;
}
else
{
lean_dec(v_pos_744_);
v_pos_744_ = v___x_754_;
goto _start;
}
}
}
else
{
lean_dec(v___x_748_);
lean_dec(v___x_747_);
return v_pos_744_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lake_Toml_ppTable_spec__0___boxed(lean_object* v_s_769_, lean_object* v_pos_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_String_Slice_Pos_revSkipWhile___at___00Lake_Toml_ppTable_spec__0(v_s_769_, v_pos_770_);
lean_dec_ref(v_s_769_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppTable(lean_object* v_t_774_){
_start:
{
lean_object* v_fst_776_; lean_object* v_snd_777_; lean_object* v___y_788_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v_items_793_; lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
v___x_791_ = ((lean_object*)(l_Lake_Toml_instInhabitedValue_default___closed__0));
v___x_792_ = ((lean_object*)(l_Lake_Toml_ppTable___closed__0));
v_items_793_ = lean_ctor_get(v_t_774_, 0);
v___x_794_ = lean_unsigned_to_nat(0u);
v___x_795_ = lean_array_get_size(v_items_793_);
v___x_796_ = lean_nat_dec_lt(v___x_794_, v___x_795_);
if (v___x_796_ == 0)
{
v_fst_776_ = v___x_791_;
v_snd_777_ = v___x_791_;
goto v___jp_775_;
}
else
{
uint8_t v___x_797_; 
v___x_797_ = lean_nat_dec_le(v___x_795_, v___x_795_);
if (v___x_797_ == 0)
{
if (v___x_796_ == 0)
{
v_fst_776_ = v___x_791_;
v_snd_777_ = v___x_791_;
goto v___jp_775_;
}
else
{
size_t v___x_798_; size_t v___x_799_; lean_object* v___x_800_; 
v___x_798_ = ((size_t)0ULL);
v___x_799_ = lean_usize_of_nat(v___x_795_);
v___x_800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5(v_items_793_, v___x_798_, v___x_799_, v___x_792_);
v___y_788_ = v___x_800_;
goto v___jp_787_;
}
}
else
{
size_t v___x_801_; size_t v___x_802_; lean_object* v___x_803_; 
v___x_801_ = ((size_t)0ULL);
v___x_802_ = lean_usize_of_nat(v___x_795_);
v___x_803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5(v_items_793_, v___x_801_, v___x_802_, v___x_792_);
v___y_788_ = v___x_803_;
goto v___jp_787_;
}
}
v___jp_775_:
{
uint32_t v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_778_ = 10;
v___x_779_ = lean_string_push(v_fst_776_, v___x_778_);
v___x_780_ = lean_string_append(v___x_779_, v_snd_777_);
lean_dec_ref(v_snd_777_);
v___x_781_ = lean_unsigned_to_nat(0u);
v___x_782_ = lean_string_utf8_byte_size(v___x_780_);
lean_inc_ref(v___x_780_);
v___x_783_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_783_, 0, v___x_780_);
lean_ctor_set(v___x_783_, 1, v___x_781_);
lean_ctor_set(v___x_783_, 2, v___x_782_);
v___x_784_ = l_String_Slice_Pos_revSkipWhile___at___00Lake_Toml_ppTable_spec__0(v___x_783_, v___x_782_);
lean_dec_ref_known(v___x_783_, 3);
v___x_785_ = lean_string_utf8_extract_fast(v___x_780_, v___x_781_, v___x_784_);
lean_dec(v___x_784_);
lean_dec_ref(v___x_780_);
v___x_786_ = lean_string_push(v___x_785_, v___x_778_);
return v___x_786_;
}
v___jp_787_:
{
lean_object* v_fst_789_; lean_object* v_snd_790_; 
v_fst_789_ = lean_ctor_get(v___y_788_, 0);
lean_inc(v_fst_789_);
v_snd_790_ = lean_ctor_get(v___y_788_, 1);
lean_inc(v_snd_790_);
lean_dec_ref(v___y_788_);
v_fst_776_ = v_fst_789_;
v_snd_777_ = v_snd_790_;
goto v___jp_775_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppTable___boxed(lean_object* v_t_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lake_Toml_ppTable(v_t_804_);
lean_dec_ref(v_t_804_);
return v_res_805_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Float(uint8_t builtin);
lean_object* runtime_initialize_Lake_Toml_Data_Dict(uint8_t builtin);
lean_object* runtime_initialize_Lake_Toml_Data_DateTime(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_String(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Toml_Data_Value(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Init_Data_Float_Float(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Toml_Data_Dict(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Toml_Data_DateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_Toml_Table_empty = _init_l_Lake_Toml_Table_empty();
lean_mark_persistent(l_Lake_Toml_Table_empty);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Toml_Data_Value(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Float_Float(uint8_t builtin);
lean_object* initialize_Lake_Toml_Data_Dict(uint8_t builtin);
lean_object* initialize_Lake_Toml_Data_DateTime(uint8_t builtin);
lean_object* initialize_Lake_Util_String(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Toml_Data_Value(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Float_Float(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Toml_Data_Dict(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Toml_Data_DateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Toml_Data_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Toml_Data_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Toml_Data_Value(builtin);
}
#ifdef __cplusplus
}
#endif

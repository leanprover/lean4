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
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0___redArg(lean_object* v_xs_95_, lean_object* v_ys_96_, lean_object* v_x_97_){
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
LEAN_EXPORT uint8_t l_Lake_Toml_instBEqValue_beq(lean_object* v_x_106_, lean_object* v_x_107_){
_start:
{
switch(lean_obj_tag(v_x_106_))
{
case 0:
{
if (lean_obj_tag(v_x_107_) == 0)
{
lean_object* v_ref_108_; lean_object* v_s_109_; lean_object* v_ref_110_; lean_object* v_s_111_; uint8_t v___x_112_; 
v_ref_108_ = lean_ctor_get(v_x_106_, 0);
lean_inc(v_ref_108_);
v_s_109_ = lean_ctor_get(v_x_106_, 1);
lean_inc_ref(v_s_109_);
lean_dec_ref_known(v_x_106_, 2);
v_ref_110_ = lean_ctor_get(v_x_107_, 0);
lean_inc(v_ref_110_);
v_s_111_ = lean_ctor_get(v_x_107_, 1);
lean_inc_ref(v_s_111_);
lean_dec_ref_known(v_x_107_, 2);
v___x_112_ = l_Lean_Syntax_structEq(v_ref_108_, v_ref_110_);
lean_dec(v_ref_110_);
lean_dec(v_ref_108_);
if (v___x_112_ == 0)
{
lean_dec_ref(v_s_111_);
lean_dec_ref(v_s_109_);
return v___x_112_;
}
else
{
uint8_t v___x_113_; 
v___x_113_ = lean_string_dec_eq(v_s_109_, v_s_111_);
lean_dec_ref(v_s_111_);
lean_dec_ref(v_s_109_);
return v___x_113_;
}
}
else
{
uint8_t v___x_114_; 
lean_dec_ref_known(v_x_106_, 2);
lean_dec_ref(v_x_107_);
v___x_114_ = 0;
return v___x_114_;
}
}
case 1:
{
if (lean_obj_tag(v_x_107_) == 1)
{
lean_object* v_ref_115_; lean_object* v_n_116_; lean_object* v_ref_117_; lean_object* v_n_118_; uint8_t v___x_119_; 
v_ref_115_ = lean_ctor_get(v_x_106_, 0);
lean_inc(v_ref_115_);
v_n_116_ = lean_ctor_get(v_x_106_, 1);
lean_inc(v_n_116_);
lean_dec_ref_known(v_x_106_, 2);
v_ref_117_ = lean_ctor_get(v_x_107_, 0);
lean_inc(v_ref_117_);
v_n_118_ = lean_ctor_get(v_x_107_, 1);
lean_inc(v_n_118_);
lean_dec_ref_known(v_x_107_, 2);
v___x_119_ = l_Lean_Syntax_structEq(v_ref_115_, v_ref_117_);
lean_dec(v_ref_117_);
lean_dec(v_ref_115_);
if (v___x_119_ == 0)
{
lean_dec(v_n_118_);
lean_dec(v_n_116_);
return v___x_119_;
}
else
{
uint8_t v___x_120_; 
v___x_120_ = lean_int_dec_eq(v_n_116_, v_n_118_);
lean_dec(v_n_118_);
lean_dec(v_n_116_);
return v___x_120_;
}
}
else
{
uint8_t v___x_121_; 
lean_dec_ref_known(v_x_106_, 2);
lean_dec_ref(v_x_107_);
v___x_121_ = 0;
return v___x_121_;
}
}
case 2:
{
if (lean_obj_tag(v_x_107_) == 2)
{
lean_object* v_ref_122_; double v_n_123_; lean_object* v_ref_124_; double v_n_125_; uint8_t v___x_126_; 
v_ref_122_ = lean_ctor_get(v_x_106_, 0);
lean_inc(v_ref_122_);
v_n_123_ = lean_ctor_get_float(v_x_106_, sizeof(void*)*1);
lean_dec_ref_known(v_x_106_, 1);
v_ref_124_ = lean_ctor_get(v_x_107_, 0);
lean_inc(v_ref_124_);
v_n_125_ = lean_ctor_get_float(v_x_107_, sizeof(void*)*1);
lean_dec_ref_known(v_x_107_, 1);
v___x_126_ = l_Lean_Syntax_structEq(v_ref_122_, v_ref_124_);
lean_dec(v_ref_124_);
lean_dec(v_ref_122_);
if (v___x_126_ == 0)
{
return v___x_126_;
}
else
{
uint8_t v___x_127_; 
v___x_127_ = lean_float_beq(v_n_123_, v_n_125_);
return v___x_127_;
}
}
else
{
uint8_t v___x_128_; 
lean_dec_ref_known(v_x_106_, 1);
lean_dec_ref(v_x_107_);
v___x_128_ = 0;
return v___x_128_;
}
}
case 3:
{
if (lean_obj_tag(v_x_107_) == 3)
{
lean_object* v_ref_129_; uint8_t v_b_130_; lean_object* v_ref_131_; uint8_t v_b_132_; uint8_t v___x_133_; 
v_ref_129_ = lean_ctor_get(v_x_106_, 0);
lean_inc(v_ref_129_);
v_b_130_ = lean_ctor_get_uint8(v_x_106_, sizeof(void*)*1);
lean_dec_ref_known(v_x_106_, 1);
v_ref_131_ = lean_ctor_get(v_x_107_, 0);
lean_inc(v_ref_131_);
v_b_132_ = lean_ctor_get_uint8(v_x_107_, sizeof(void*)*1);
lean_dec_ref_known(v_x_107_, 1);
v___x_133_ = l_Lean_Syntax_structEq(v_ref_129_, v_ref_131_);
lean_dec(v_ref_131_);
lean_dec(v_ref_129_);
if (v___x_133_ == 0)
{
return v___x_133_;
}
else
{
if (v_b_132_ == 0)
{
if (v_b_130_ == 0)
{
return v___x_133_;
}
else
{
return v_b_132_;
}
}
else
{
return v_b_130_;
}
}
}
else
{
uint8_t v___x_134_; 
lean_dec_ref_known(v_x_106_, 1);
lean_dec_ref(v_x_107_);
v___x_134_ = 0;
return v___x_134_;
}
}
case 4:
{
if (lean_obj_tag(v_x_107_) == 4)
{
lean_object* v_ref_135_; lean_object* v_dt_136_; lean_object* v_ref_137_; lean_object* v_dt_138_; uint8_t v___x_139_; 
v_ref_135_ = lean_ctor_get(v_x_106_, 0);
lean_inc(v_ref_135_);
v_dt_136_ = lean_ctor_get(v_x_106_, 1);
lean_inc_ref(v_dt_136_);
lean_dec_ref_known(v_x_106_, 2);
v_ref_137_ = lean_ctor_get(v_x_107_, 0);
lean_inc(v_ref_137_);
v_dt_138_ = lean_ctor_get(v_x_107_, 1);
lean_inc_ref(v_dt_138_);
lean_dec_ref_known(v_x_107_, 2);
v___x_139_ = l_Lean_Syntax_structEq(v_ref_135_, v_ref_137_);
lean_dec(v_ref_137_);
lean_dec(v_ref_135_);
if (v___x_139_ == 0)
{
lean_dec_ref(v_dt_138_);
lean_dec_ref(v_dt_136_);
return v___x_139_;
}
else
{
uint8_t v___x_140_; 
v___x_140_ = l_Lake_Toml_instDecidableEqDateTime_decEq(v_dt_136_, v_dt_138_);
return v___x_140_;
}
}
else
{
uint8_t v___x_141_; 
lean_dec_ref_known(v_x_106_, 2);
lean_dec_ref(v_x_107_);
v___x_141_ = 0;
return v___x_141_;
}
}
case 5:
{
if (lean_obj_tag(v_x_107_) == 5)
{
lean_object* v_ref_142_; lean_object* v_xs_143_; lean_object* v_ref_144_; lean_object* v_xs_145_; uint8_t v___x_146_; 
v_ref_142_ = lean_ctor_get(v_x_106_, 0);
lean_inc(v_ref_142_);
v_xs_143_ = lean_ctor_get(v_x_106_, 1);
lean_inc_ref(v_xs_143_);
lean_dec_ref_known(v_x_106_, 2);
v_ref_144_ = lean_ctor_get(v_x_107_, 0);
lean_inc(v_ref_144_);
v_xs_145_ = lean_ctor_get(v_x_107_, 1);
lean_inc_ref(v_xs_145_);
lean_dec_ref_known(v_x_107_, 2);
v___x_146_ = l_Lean_Syntax_structEq(v_ref_142_, v_ref_144_);
lean_dec(v_ref_144_);
lean_dec(v_ref_142_);
if (v___x_146_ == 0)
{
lean_dec_ref(v_xs_145_);
lean_dec_ref(v_xs_143_);
return v___x_146_;
}
else
{
lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_147_ = lean_array_get_size(v_xs_143_);
v___x_148_ = lean_array_get_size(v_xs_145_);
v___x_149_ = lean_nat_dec_eq(v___x_147_, v___x_148_);
if (v___x_149_ == 0)
{
lean_dec_ref(v_xs_145_);
lean_dec_ref(v_xs_143_);
return v___x_149_;
}
else
{
uint8_t v___x_150_; 
v___x_150_ = l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0___redArg(v_xs_143_, v_xs_145_, v___x_147_);
lean_dec_ref(v_xs_145_);
lean_dec_ref(v_xs_143_);
return v___x_150_;
}
}
}
else
{
uint8_t v___x_151_; 
lean_dec_ref_known(v_x_106_, 2);
lean_dec_ref(v_x_107_);
v___x_151_ = 0;
return v___x_151_;
}
}
default: 
{
if (lean_obj_tag(v_x_107_) == 6)
{
lean_object* v_ref_152_; lean_object* v_xs_153_; lean_object* v_ref_154_; lean_object* v_xs_155_; uint8_t v___x_156_; 
v_ref_152_ = lean_ctor_get(v_x_106_, 0);
lean_inc(v_ref_152_);
v_xs_153_ = lean_ctor_get(v_x_106_, 1);
lean_inc_ref(v_xs_153_);
lean_dec_ref_known(v_x_106_, 2);
v_ref_154_ = lean_ctor_get(v_x_107_, 0);
lean_inc(v_ref_154_);
v_xs_155_ = lean_ctor_get(v_x_107_, 1);
lean_inc_ref(v_xs_155_);
lean_dec_ref_known(v_x_107_, 2);
v___x_156_ = l_Lean_Syntax_structEq(v_ref_152_, v_ref_154_);
lean_dec(v_ref_154_);
lean_dec(v_ref_152_);
if (v___x_156_ == 0)
{
lean_dec_ref(v_xs_155_);
lean_dec_ref(v_xs_153_);
return v___x_156_;
}
else
{
uint8_t v___x_157_; 
v___x_157_ = l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1___redArg(v_xs_153_, v_xs_155_);
lean_dec_ref(v_xs_155_);
lean_dec_ref(v_xs_153_);
return v___x_157_;
}
}
else
{
uint8_t v___x_158_; 
lean_dec_ref_known(v_x_106_, 2);
lean_dec_ref(v_x_107_);
v___x_158_ = 0;
return v___x_158_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___redArg(lean_object* v_xs_159_, lean_object* v_ys_160_, lean_object* v_x_161_){
_start:
{
lean_object* v_zero_162_; uint8_t v_isZero_163_; 
v_zero_162_ = lean_unsigned_to_nat(0u);
v_isZero_163_ = lean_nat_dec_eq(v_x_161_, v_zero_162_);
if (v_isZero_163_ == 1)
{
lean_dec(v_x_161_);
return v_isZero_163_;
}
else
{
lean_object* v_one_164_; lean_object* v_n_165_; uint8_t v___y_167_; lean_object* v___x_169_; lean_object* v_fst_170_; lean_object* v_snd_171_; lean_object* v___x_172_; lean_object* v_fst_173_; lean_object* v_snd_174_; uint8_t v___x_175_; 
v_one_164_ = lean_unsigned_to_nat(1u);
v_n_165_ = lean_nat_sub(v_x_161_, v_one_164_);
lean_dec(v_x_161_);
v___x_169_ = lean_array_fget_borrowed(v_xs_159_, v_n_165_);
v_fst_170_ = lean_ctor_get(v___x_169_, 0);
v_snd_171_ = lean_ctor_get(v___x_169_, 1);
v___x_172_ = lean_array_fget_borrowed(v_ys_160_, v_n_165_);
v_fst_173_ = lean_ctor_get(v___x_172_, 0);
v_snd_174_ = lean_ctor_get(v___x_172_, 1);
v___x_175_ = lean_name_eq(v_fst_170_, v_fst_173_);
if (v___x_175_ == 0)
{
v___y_167_ = v___x_175_;
goto v___jp_166_;
}
else
{
uint8_t v___x_176_; 
lean_inc(v_snd_174_);
lean_inc(v_snd_171_);
v___x_176_ = l_Lake_Toml_instBEqValue_beq(v_snd_171_, v_snd_174_);
v___y_167_ = v___x_176_;
goto v___jp_166_;
}
v___jp_166_:
{
if (v___y_167_ == 0)
{
lean_dec(v_n_165_);
return v___y_167_;
}
else
{
v_x_161_ = v_n_165_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1___redArg(lean_object* v_self_177_, lean_object* v_other_178_){
_start:
{
lean_object* v_items_179_; lean_object* v_items_180_; lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v_items_179_ = lean_ctor_get(v_self_177_, 0);
v_items_180_ = lean_ctor_get(v_other_178_, 0);
v___x_181_ = lean_array_get_size(v_items_179_);
v___x_182_ = lean_array_get_size(v_items_180_);
v___x_183_ = lean_nat_dec_eq(v___x_181_, v___x_182_);
if (v___x_183_ == 0)
{
return v___x_183_;
}
else
{
uint8_t v___x_184_; 
v___x_184_ = l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___redArg(v_items_179_, v_items_180_, v___x_181_);
return v___x_184_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1___redArg___boxed(lean_object* v_self_185_, lean_object* v_other_186_){
_start:
{
uint8_t v_res_187_; lean_object* v_r_188_; 
v_res_187_ = l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1___redArg(v_self_185_, v_other_186_);
lean_dec_ref(v_other_186_);
lean_dec_ref(v_self_185_);
v_r_188_ = lean_box(v_res_187_);
return v_r_188_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0___redArg___boxed(lean_object* v_xs_189_, lean_object* v_ys_190_, lean_object* v_x_191_){
_start:
{
uint8_t v_res_192_; lean_object* v_r_193_; 
v_res_192_ = l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0___redArg(v_xs_189_, v_ys_190_, v_x_191_);
lean_dec_ref(v_ys_190_);
lean_dec_ref(v_xs_189_);
v_r_193_ = lean_box(v_res_192_);
return v_r_193_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___redArg___boxed(lean_object* v_xs_194_, lean_object* v_ys_195_, lean_object* v_x_196_){
_start:
{
uint8_t v_res_197_; lean_object* v_r_198_; 
v_res_197_ = l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___redArg(v_xs_194_, v_ys_195_, v_x_196_);
lean_dec_ref(v_ys_195_);
lean_dec_ref(v_xs_194_);
v_r_198_ = lean_box(v_res_197_);
return v_r_198_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instBEqValue_beq___boxed(lean_object* v_x_199_, lean_object* v_x_200_){
_start:
{
uint8_t v_res_201_; lean_object* v_r_202_; 
v_res_201_ = l_Lake_Toml_instBEqValue_beq(v_x_199_, v_x_200_);
v_r_202_ = lean_box(v_res_201_);
return v_r_202_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0(lean_object* v_xs_203_, lean_object* v_ys_204_, lean_object* v_hsz_205_, lean_object* v_x_206_, lean_object* v_x_207_){
_start:
{
uint8_t v___x_208_; 
v___x_208_ = l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0___redArg(v_xs_203_, v_ys_204_, v_x_206_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0___boxed(lean_object* v_xs_209_, lean_object* v_ys_210_, lean_object* v_hsz_211_, lean_object* v_x_212_, lean_object* v_x_213_){
_start:
{
uint8_t v_res_214_; lean_object* v_r_215_; 
v_res_214_ = l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0(v_xs_209_, v_ys_210_, v_hsz_211_, v_x_212_, v_x_213_);
lean_dec_ref(v_ys_210_);
lean_dec_ref(v_xs_209_);
v_r_215_ = lean_box(v_res_214_);
return v_r_215_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1(lean_object* v_cmp_216_, lean_object* v_self_217_, lean_object* v_other_218_){
_start:
{
uint8_t v___x_219_; 
v___x_219_ = l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1___redArg(v_self_217_, v_other_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1___boxed(lean_object* v_cmp_220_, lean_object* v_self_221_, lean_object* v_other_222_){
_start:
{
uint8_t v_res_223_; lean_object* v_r_224_; 
v_res_223_ = l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1(v_cmp_220_, v_self_221_, v_other_222_);
lean_dec_ref(v_other_222_);
lean_dec_ref(v_self_221_);
lean_dec_ref(v_cmp_220_);
v_r_224_ = lean_box(v_res_223_);
return v_r_224_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1(lean_object* v_xs_225_, lean_object* v_ys_226_, lean_object* v_hsz_227_, lean_object* v_x_228_, lean_object* v_x_229_){
_start:
{
uint8_t v___x_230_; 
v___x_230_ = l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___redArg(v_xs_225_, v_ys_226_, v_x_228_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___boxed(lean_object* v_xs_231_, lean_object* v_ys_232_, lean_object* v_hsz_233_, lean_object* v_x_234_, lean_object* v_x_235_){
_start:
{
uint8_t v_res_236_; lean_object* v_r_237_; 
v_res_236_ = l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1(v_xs_231_, v_ys_232_, v_hsz_233_, v_x_234_, v_x_235_);
lean_dec_ref(v_ys_232_);
lean_dec_ref(v_xs_231_);
v_r_237_ = lean_box(v_res_236_);
return v_r_237_;
}
}
static lean_object* _init_l_Lake_Toml_Table_empty___closed__0(void){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l_Lake_Toml_RBDict_empty___redArg();
return v___x_240_;
}
}
static lean_object* _init_l_Lake_Toml_Table_empty(void){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = lean_obj_once(&l_Lake_Toml_Table_empty___closed__0, &l_Lake_Toml_Table_empty___closed__0_once, _init_l_Lake_Toml_Table_empty___closed__0);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_mkEmpty(lean_object* v_capacity_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Lake_Toml_RBDict_mkEmpty___redArg(v_capacity_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_mkEmpty___boxed(lean_object* v_capacity_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lake_Toml_Table_mkEmpty(v_capacity_244_);
lean_dec(v_capacity_244_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_table(lean_object* v_ref_246_, lean_object* v_t_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_248_, 0, v_ref_246_);
lean_ctor_set(v___x_248_, 1, v_t_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_ref(lean_object* v_x_249_){
_start:
{
lean_object* v_ref_250_; 
v_ref_250_ = lean_ctor_get(v_x_249_, 0);
lean_inc(v_ref_250_);
return v_ref_250_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_ref___boxed(lean_object* v_x_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lake_Toml_Value_ref(v_x_251_);
lean_dec_ref(v_x_251_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg(lean_object* v___x_261_, lean_object* v_s_262_, lean_object* v_a_263_, lean_object* v_b_264_){
_start:
{
uint8_t v_decide_265_; 
v_decide_265_ = lean_nat_dec_eq(v_a_263_, v___x_261_);
if (v_decide_265_ == 0)
{
uint32_t v___x_266_; lean_object* v___x_267_; uint32_t v___x_280_; uint8_t v___x_281_; 
v___x_266_ = lean_string_utf8_get_fast(v_s_262_, v_a_263_);
v___x_267_ = lean_string_utf8_next_fast(v_s_262_, v_a_263_);
lean_dec(v_a_263_);
v___x_280_ = 8;
v___x_281_ = lean_uint32_dec_eq(v___x_266_, v___x_280_);
if (v___x_281_ == 0)
{
uint32_t v___x_282_; uint8_t v___x_283_; 
v___x_282_ = 9;
v___x_283_ = lean_uint32_dec_eq(v___x_266_, v___x_282_);
if (v___x_283_ == 0)
{
uint32_t v___x_284_; uint8_t v___x_285_; 
v___x_284_ = 10;
v___x_285_ = lean_uint32_dec_eq(v___x_266_, v___x_284_);
if (v___x_285_ == 0)
{
uint32_t v___x_286_; uint8_t v___x_287_; 
v___x_286_ = 12;
v___x_287_ = lean_uint32_dec_eq(v___x_266_, v___x_286_);
if (v___x_287_ == 0)
{
uint32_t v___x_288_; uint8_t v___x_289_; 
v___x_288_ = 13;
v___x_289_ = lean_uint32_dec_eq(v___x_266_, v___x_288_);
if (v___x_289_ == 0)
{
uint32_t v___x_290_; uint8_t v___x_291_; 
v___x_290_ = 34;
v___x_291_ = lean_uint32_dec_eq(v___x_266_, v___x_290_);
if (v___x_291_ == 0)
{
uint32_t v___x_292_; uint8_t v___x_293_; 
v___x_292_ = 92;
v___x_293_ = lean_uint32_dec_eq(v___x_266_, v___x_292_);
if (v___x_293_ == 0)
{
uint32_t v___x_294_; uint8_t v___x_295_; 
v___x_294_ = 32;
v___x_295_ = lean_uint32_dec_lt(v___x_266_, v___x_294_);
if (v___x_295_ == 0)
{
uint32_t v___x_296_; uint8_t v___x_297_; 
v___x_296_ = 127;
v___x_297_ = lean_uint32_dec_eq(v___x_266_, v___x_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; 
v___x_298_ = lean_string_push(v_b_264_, v___x_266_);
v_a_263_ = v___x_267_;
v_b_264_ = v___x_298_;
goto _start;
}
else
{
goto v___jp_268_;
}
}
else
{
goto v___jp_268_;
}
}
else
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__1));
v___x_301_ = lean_string_append(v_b_264_, v___x_300_);
v_a_263_ = v___x_267_;
v_b_264_ = v___x_301_;
goto _start;
}
}
else
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__2));
v___x_304_ = lean_string_append(v_b_264_, v___x_303_);
v_a_263_ = v___x_267_;
v_b_264_ = v___x_304_;
goto _start;
}
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__3));
v___x_307_ = lean_string_append(v_b_264_, v___x_306_);
v_a_263_ = v___x_267_;
v_b_264_ = v___x_307_;
goto _start;
}
}
else
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__4));
v___x_310_ = lean_string_append(v_b_264_, v___x_309_);
v_a_263_ = v___x_267_;
v_b_264_ = v___x_310_;
goto _start;
}
}
else
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__5));
v___x_313_ = lean_string_append(v_b_264_, v___x_312_);
v_a_263_ = v___x_267_;
v_b_264_ = v___x_313_;
goto _start;
}
}
else
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__6));
v___x_316_ = lean_string_append(v_b_264_, v___x_315_);
v_a_263_ = v___x_267_;
v_b_264_ = v___x_316_;
goto _start;
}
}
else
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__7));
v___x_319_ = lean_string_append(v_b_264_, v___x_318_);
v_a_263_ = v___x_267_;
v_b_264_ = v___x_319_;
goto _start;
}
v___jp_268_:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; uint32_t v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_269_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__0));
v___x_270_ = lean_string_append(v_b_264_, v___x_269_);
v___x_271_ = lean_unsigned_to_nat(16u);
v___x_272_ = lean_uint32_to_nat(v___x_266_);
v___x_273_ = l_Nat_toDigits(v___x_271_, v___x_272_);
v___x_274_ = lean_string_mk(v___x_273_);
v___x_275_ = 48;
v___x_276_ = lean_unsigned_to_nat(4u);
v___x_277_ = l_Lake_lpadAscii(v___x_274_, v___x_275_, v___x_276_);
lean_dec_ref(v___x_274_);
v___x_278_ = lean_string_append(v___x_270_, v___x_277_);
lean_dec_ref(v___x_277_);
v_a_263_ = v___x_267_;
v_b_264_ = v___x_278_;
goto _start;
}
}
else
{
lean_dec(v_a_263_);
return v_b_264_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___boxed(lean_object* v___x_321_, lean_object* v_s_322_, lean_object* v_a_323_, lean_object* v_b_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg(v___x_321_, v_s_322_, v_a_323_, v_b_324_);
lean_dec_ref(v_s_322_);
lean_dec(v___x_321_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppString(lean_object* v_s_327_){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v_s_331_; uint32_t v___x_332_; lean_object* v___x_333_; 
v___x_328_ = ((lean_object*)(l_Lake_Toml_ppString___closed__0));
v___x_329_ = lean_string_utf8_byte_size(v_s_327_);
v___x_330_ = lean_unsigned_to_nat(0u);
v_s_331_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg(v___x_329_, v_s_327_, v___x_330_, v___x_328_);
v___x_332_ = 34;
v___x_333_ = lean_string_push(v_s_331_, v___x_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppString___boxed(lean_object* v_s_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lake_Toml_ppString(v_s_334_);
lean_dec_ref(v_s_334_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0(lean_object* v___x_336_, lean_object* v___x_337_, lean_object* v_s_338_, lean_object* v_inst_339_, lean_object* v_R_340_, lean_object* v_a_341_, lean_object* v_b_342_, lean_object* v_c_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg(v___x_337_, v_s_338_, v_a_341_, v_b_342_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___boxed(lean_object* v___x_345_, lean_object* v___x_346_, lean_object* v_s_347_, lean_object* v_inst_348_, lean_object* v_R_349_, lean_object* v_a_350_, lean_object* v_b_351_, lean_object* v_c_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0(v___x_345_, v___x_346_, v_s_347_, v_inst_348_, v_R_349_, v_a_350_, v_b_351_, v_c_352_);
lean_dec_ref(v_s_347_);
lean_dec(v___x_346_);
lean_dec_ref(v___x_345_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lake_Toml_ppSimpleKey_spec__0(lean_object* v_s_354_, lean_object* v_pos_355_){
_start:
{
lean_object* v_str_356_; lean_object* v_startInclusive_357_; lean_object* v_endExclusive_358_; lean_object* v___x_359_; lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v_decide_370_; 
v_str_356_ = lean_ctor_get(v_s_354_, 0);
v_startInclusive_357_ = lean_ctor_get(v_s_354_, 1);
v_endExclusive_358_ = lean_ctor_get(v_s_354_, 2);
v___x_359_ = lean_nat_add(v_startInclusive_357_, v_pos_355_);
v___x_368_ = lean_unsigned_to_nat(0u);
v___x_369_ = lean_nat_sub(v_endExclusive_358_, v___x_359_);
v_decide_370_ = lean_nat_dec_eq(v___x_368_, v___x_369_);
lean_dec(v___x_369_);
if (v_decide_370_ == 0)
{
uint32_t v___x_371_; uint32_t v___x_387_; uint8_t v___x_388_; 
v___x_371_ = lean_string_utf8_get_fast(v_str_356_, v___x_359_);
v___x_387_ = 65;
v___x_388_ = lean_uint32_dec_le(v___x_387_, v___x_371_);
if (v___x_388_ == 0)
{
goto v___jp_382_;
}
else
{
uint32_t v___x_389_; uint8_t v___x_390_; 
v___x_389_ = 90;
v___x_390_ = lean_uint32_dec_le(v___x_371_, v___x_389_);
if (v___x_390_ == 0)
{
goto v___jp_382_;
}
else
{
goto v___jp_360_;
}
}
v___jp_372_:
{
uint32_t v___x_373_; uint8_t v___x_374_; 
v___x_373_ = 95;
v___x_374_ = lean_uint32_dec_eq(v___x_371_, v___x_373_);
if (v___x_374_ == 0)
{
uint32_t v___x_375_; uint8_t v___x_376_; 
v___x_375_ = 45;
v___x_376_ = lean_uint32_dec_eq(v___x_371_, v___x_375_);
if (v___x_376_ == 0)
{
lean_dec(v___x_359_);
return v_pos_355_;
}
else
{
goto v___jp_360_;
}
}
else
{
goto v___jp_360_;
}
}
v___jp_377_:
{
uint32_t v___x_378_; uint8_t v___x_379_; 
v___x_378_ = 48;
v___x_379_ = lean_uint32_dec_le(v___x_378_, v___x_371_);
if (v___x_379_ == 0)
{
goto v___jp_372_;
}
else
{
uint32_t v___x_380_; uint8_t v___x_381_; 
v___x_380_ = 57;
v___x_381_ = lean_uint32_dec_le(v___x_371_, v___x_380_);
if (v___x_381_ == 0)
{
goto v___jp_372_;
}
else
{
goto v___jp_360_;
}
}
}
v___jp_382_:
{
uint32_t v___x_383_; uint8_t v___x_384_; 
v___x_383_ = 97;
v___x_384_ = lean_uint32_dec_le(v___x_383_, v___x_371_);
if (v___x_384_ == 0)
{
goto v___jp_377_;
}
else
{
uint32_t v___x_385_; uint8_t v___x_386_; 
v___x_385_ = 122;
v___x_386_ = lean_uint32_dec_le(v___x_371_, v___x_385_);
if (v___x_386_ == 0)
{
goto v___jp_377_;
}
else
{
goto v___jp_360_;
}
}
}
}
else
{
lean_dec(v___x_359_);
return v_pos_355_;
}
v___jp_360_:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_361_ = lean_string_utf8_next_fast(v_str_356_, v___x_359_);
v___x_362_ = lean_nat_sub(v___x_361_, v___x_359_);
lean_dec(v___x_359_);
v___x_363_ = lean_nat_add(v_pos_355_, v___x_362_);
lean_dec(v___x_362_);
v___x_364_ = lean_unsigned_to_nat(1u);
v___x_365_ = lean_nat_add(v_pos_355_, v___x_364_);
v___x_366_ = lean_nat_dec_le(v___x_365_, v___x_363_);
lean_dec(v___x_365_);
if (v___x_366_ == 0)
{
lean_dec(v___x_363_);
return v_pos_355_;
}
else
{
lean_dec(v_pos_355_);
v_pos_355_ = v___x_363_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lake_Toml_ppSimpleKey_spec__0___boxed(lean_object* v_s_391_, lean_object* v_pos_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_String_Slice_Pos_skipWhile___at___00Lake_Toml_ppSimpleKey_spec__0(v_s_391_, v_pos_392_);
lean_dec_ref(v_s_391_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppSimpleKey(lean_object* v_k_394_){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v_decide_399_; 
v___x_395_ = lean_unsigned_to_nat(0u);
v___x_396_ = lean_string_utf8_byte_size(v_k_394_);
lean_inc_ref(v_k_394_);
v___x_397_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_397_, 0, v_k_394_);
lean_ctor_set(v___x_397_, 1, v___x_395_);
lean_ctor_set(v___x_397_, 2, v___x_396_);
v___x_398_ = l_String_Slice_Pos_skipWhile___at___00Lake_Toml_ppSimpleKey_spec__0(v___x_397_, v___x_395_);
lean_dec_ref_known(v___x_397_, 3);
v_decide_399_ = lean_nat_dec_eq(v___x_398_, v___x_396_);
lean_dec(v___x_398_);
if (v_decide_399_ == 0)
{
lean_object* v___x_400_; 
v___x_400_ = l_Lake_Toml_ppString(v_k_394_);
lean_dec_ref(v_k_394_);
return v___x_400_;
}
else
{
return v_k_394_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppKey(lean_object* v_k_402_){
_start:
{
if (lean_obj_tag(v_k_402_) == 1)
{
lean_object* v_pre_403_; lean_object* v_str_404_; uint8_t v___x_405_; 
v_pre_403_ = lean_ctor_get(v_k_402_, 0);
lean_inc(v_pre_403_);
v_str_404_ = lean_ctor_get(v_k_402_, 1);
lean_inc_ref(v_str_404_);
lean_dec_ref_known(v_k_402_, 2);
v___x_405_ = l_Lean_Name_isAnonymous(v_pre_403_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_406_ = l_Lake_Toml_ppKey(v_pre_403_);
v___x_407_ = ((lean_object*)(l_Lake_Toml_ppKey___closed__0));
v___x_408_ = lean_string_append(v___x_406_, v___x_407_);
v___x_409_ = l_Lake_Toml_ppSimpleKey(v_str_404_);
v___x_410_ = lean_string_append(v___x_408_, v___x_409_);
lean_dec_ref(v___x_409_);
return v___x_410_;
}
else
{
lean_object* v___x_411_; 
lean_dec(v_pre_403_);
v___x_411_ = l_Lake_Toml_ppSimpleKey(v_str_404_);
return v___x_411_;
}
}
else
{
lean_object* v___x_412_; 
lean_dec(v_k_402_);
v___x_412_ = ((lean_object*)(l_Lake_Toml_instInhabitedValue_default___closed__0));
return v___x_412_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0(size_t v_sz_419_, size_t v_i_420_, lean_object* v_bs_421_){
_start:
{
uint8_t v___x_422_; 
v___x_422_ = lean_usize_dec_lt(v_i_420_, v_sz_419_);
if (v___x_422_ == 0)
{
return v_bs_421_;
}
else
{
lean_object* v_v_423_; lean_object* v_fst_424_; lean_object* v_snd_425_; lean_object* v___x_426_; lean_object* v_bs_x27_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; size_t v___x_433_; size_t v___x_434_; lean_object* v___x_435_; 
v_v_423_ = lean_array_uget_borrowed(v_bs_421_, v_i_420_);
v_fst_424_ = lean_ctor_get(v_v_423_, 0);
lean_inc(v_fst_424_);
v_snd_425_ = lean_ctor_get(v_v_423_, 1);
lean_inc(v_snd_425_);
v___x_426_ = lean_unsigned_to_nat(0u);
v_bs_x27_427_ = lean_array_uset(v_bs_421_, v_i_420_, v___x_426_);
v___x_428_ = l_Lake_Toml_ppKey(v_fst_424_);
v___x_429_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___closed__0));
v___x_430_ = lean_string_append(v___x_428_, v___x_429_);
v___x_431_ = l_Lake_Toml_Value_toString(v_snd_425_);
v___x_432_ = lean_string_append(v___x_430_, v___x_431_);
lean_dec_ref(v___x_431_);
v___x_433_ = ((size_t)1ULL);
v___x_434_ = lean_usize_add(v_i_420_, v___x_433_);
v___x_435_ = lean_array_uset(v_bs_x27_427_, v_i_420_, v___x_432_);
v_i_420_ = v___x_434_;
v_bs_421_ = v___x_435_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppInlineTable(lean_object* v_t_439_){
_start:
{
lean_object* v_items_440_; size_t v_sz_441_; size_t v___x_442_; lean_object* v_xs_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v_items_440_ = lean_ctor_get(v_t_439_, 0);
lean_inc_ref(v_items_440_);
lean_dec_ref(v_t_439_);
v_sz_441_ = lean_array_size(v_items_440_);
v___x_442_ = ((size_t)0ULL);
v_xs_443_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0(v_sz_441_, v___x_442_, v_items_440_);
v___x_444_ = ((lean_object*)(l_Lake_Toml_ppInlineTable___closed__0));
v___x_445_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__1));
v___x_446_ = lean_array_to_list(v_xs_443_);
v___x_447_ = l_String_intercalate(v___x_445_, v___x_446_);
v___x_448_ = lean_string_append(v___x_444_, v___x_447_);
lean_dec_ref(v___x_447_);
v___x_449_ = ((lean_object*)(l_Lake_Toml_ppInlineTable___closed__1));
v___x_450_ = lean_string_append(v___x_448_, v___x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_toString(lean_object* v_v_451_){
_start:
{
switch(lean_obj_tag(v_v_451_))
{
case 0:
{
lean_object* v_s_452_; lean_object* v___x_453_; 
v_s_452_ = lean_ctor_get(v_v_451_, 1);
lean_inc_ref(v_s_452_);
lean_dec_ref_known(v_v_451_, 2);
v___x_453_ = l_Lake_Toml_ppString(v_s_452_);
lean_dec_ref(v_s_452_);
return v___x_453_;
}
case 1:
{
lean_object* v_n_454_; lean_object* v___x_455_; 
v_n_454_ = lean_ctor_get(v_v_451_, 1);
lean_inc(v_n_454_);
lean_dec_ref_known(v_v_451_, 2);
v___x_455_ = l_Int_repr(v_n_454_);
lean_dec(v_n_454_);
return v___x_455_;
}
case 2:
{
double v_n_456_; lean_object* v___x_457_; 
v_n_456_ = lean_ctor_get_float(v_v_451_, sizeof(void*)*1);
lean_dec_ref_known(v_v_451_, 1);
v___x_457_ = lean_float_to_string(v_n_456_);
return v___x_457_;
}
case 3:
{
uint8_t v_b_458_; 
v_b_458_ = lean_ctor_get_uint8(v_v_451_, sizeof(void*)*1);
lean_dec_ref_known(v_v_451_, 1);
if (v_b_458_ == 0)
{
lean_object* v___x_459_; 
v___x_459_ = ((lean_object*)(l_Lake_Toml_Value_toString___closed__0));
return v___x_459_;
}
else
{
lean_object* v___x_460_; 
v___x_460_ = ((lean_object*)(l_Lake_Toml_Value_toString___closed__1));
return v___x_460_;
}
}
case 4:
{
lean_object* v_dt_461_; lean_object* v___x_462_; 
v_dt_461_ = lean_ctor_get(v_v_451_, 1);
lean_inc_ref(v_dt_461_);
lean_dec_ref_known(v_v_451_, 2);
v___x_462_ = l_Lake_Toml_DateTime_toString(v_dt_461_);
return v___x_462_;
}
case 5:
{
lean_object* v_xs_463_; lean_object* v___x_464_; 
v_xs_463_ = lean_ctor_get(v_v_451_, 1);
lean_inc_ref(v_xs_463_);
lean_dec_ref_known(v_v_451_, 2);
v___x_464_ = l_Lake_Toml_ppInlineArray(v_xs_463_);
return v___x_464_;
}
default: 
{
lean_object* v_xs_465_; lean_object* v___x_466_; 
v_xs_465_ = lean_ctor_get(v_v_451_, 1);
lean_inc_ref(v_xs_465_);
lean_dec_ref_known(v_v_451_, 2);
v___x_466_ = l_Lake_Toml_ppInlineTable(v_xs_465_);
return v___x_466_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3(size_t v_sz_467_, size_t v_i_468_, lean_object* v_bs_469_){
_start:
{
uint8_t v___x_470_; 
v___x_470_ = lean_usize_dec_lt(v_i_468_, v_sz_467_);
if (v___x_470_ == 0)
{
return v_bs_469_;
}
else
{
lean_object* v_v_471_; lean_object* v___x_472_; lean_object* v_bs_x27_473_; lean_object* v___x_474_; size_t v___x_475_; size_t v___x_476_; lean_object* v___x_477_; 
v_v_471_ = lean_array_uget(v_bs_469_, v_i_468_);
v___x_472_ = lean_unsigned_to_nat(0u);
v_bs_x27_473_ = lean_array_uset(v_bs_469_, v_i_468_, v___x_472_);
v___x_474_ = l_Lake_Toml_Value_toString(v_v_471_);
v___x_475_ = ((size_t)1ULL);
v___x_476_ = lean_usize_add(v_i_468_, v___x_475_);
v___x_477_ = lean_array_uset(v_bs_x27_473_, v_i_468_, v___x_474_);
v_i_468_ = v___x_476_;
v_bs_469_ = v___x_477_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppInlineArray(lean_object* v_vs_479_){
_start:
{
size_t v_sz_480_; size_t v___x_481_; lean_object* v_xs_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v_sz_480_ = lean_array_size(v_vs_479_);
v___x_481_ = ((size_t)0ULL);
v_xs_482_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3(v_sz_480_, v___x_481_, v_vs_479_);
v___x_483_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__0));
v___x_484_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__1));
v___x_485_ = lean_array_to_list(v_xs_482_);
v___x_486_ = l_String_intercalate(v___x_484_, v___x_485_);
v___x_487_ = lean_string_append(v___x_483_, v___x_486_);
lean_dec_ref(v___x_486_);
v___x_488_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__2));
v___x_489_ = lean_string_append(v___x_487_, v___x_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3___boxed(lean_object* v_sz_490_, lean_object* v_i_491_, lean_object* v_bs_492_){
_start:
{
size_t v_sz_boxed_493_; size_t v_i_boxed_494_; lean_object* v_res_495_; 
v_sz_boxed_493_ = lean_unbox_usize(v_sz_490_);
lean_dec(v_sz_490_);
v_i_boxed_494_ = lean_unbox_usize(v_i_491_);
lean_dec(v_i_491_);
v_res_495_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3(v_sz_boxed_493_, v_i_boxed_494_, v_bs_492_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___boxed(lean_object* v_sz_496_, lean_object* v_i_497_, lean_object* v_bs_498_){
_start:
{
size_t v_sz_boxed_499_; size_t v_i_boxed_500_; lean_object* v_res_501_; 
v_sz_boxed_499_ = lean_unbox_usize(v_sz_496_);
lean_dec(v_sz_496_);
v_i_boxed_500_ = lean_unbox_usize(v_i_497_);
lean_dec(v_i_497_);
v_res_501_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0(v_sz_boxed_499_, v_i_boxed_500_, v_bs_498_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval(lean_object* v_s_505_, lean_object* v_k_506_, lean_object* v_v_507_){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_508_ = l_Lake_Toml_ppKey(v_k_506_);
v___x_509_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___closed__0));
v___x_510_ = lean_string_append(v___x_508_, v___x_509_);
v___x_511_ = l_Lake_Toml_Value_toString(v_v_507_);
v___x_512_ = lean_string_append(v___x_510_, v___x_511_);
lean_dec_ref(v___x_511_);
v___x_513_ = ((lean_object*)(l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval___closed__0));
v___x_514_ = lean_string_append(v___x_512_, v___x_513_);
v___x_515_ = lean_string_append(v_s_505_, v___x_514_);
lean_dec_ref(v___x_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lake_Toml_ppTable_spec__2(lean_object* v_msg_516_){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = ((lean_object*)(l_Lake_Toml_instInhabitedValue_default___closed__0));
v___x_518_ = lean_panic_fn_borrowed(v___x_517_, v_msg_516_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(lean_object* v_as_519_, size_t v_i_520_, size_t v_stop_521_, lean_object* v_b_522_){
_start:
{
uint8_t v___x_523_; 
v___x_523_ = lean_usize_dec_eq(v_i_520_, v_stop_521_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; lean_object* v_fst_525_; lean_object* v_snd_526_; lean_object* v___x_527_; size_t v___x_528_; size_t v___x_529_; 
v___x_524_ = lean_array_uget_borrowed(v_as_519_, v_i_520_);
v_fst_525_ = lean_ctor_get(v___x_524_, 0);
v_snd_526_ = lean_ctor_get(v___x_524_, 1);
lean_inc(v_snd_526_);
lean_inc(v_fst_525_);
v___x_527_ = l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval(v_b_522_, v_fst_525_, v_snd_526_);
v___x_528_ = ((size_t)1ULL);
v___x_529_ = lean_usize_add(v_i_520_, v___x_528_);
v_i_520_ = v___x_529_;
v_b_522_ = v___x_527_;
goto _start;
}
else
{
return v_b_522_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1___boxed(lean_object* v_as_531_, lean_object* v_i_532_, lean_object* v_stop_533_, lean_object* v_b_534_){
_start:
{
size_t v_i_boxed_535_; size_t v_stop_boxed_536_; lean_object* v_res_537_; 
v_i_boxed_535_ = lean_unbox_usize(v_i_532_);
lean_dec(v_i_532_);
v_stop_boxed_536_ = lean_unbox_usize(v_stop_533_);
lean_dec(v_stop_533_);
v_res_537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_as_531_, v_i_boxed_535_, v_stop_boxed_536_, v_b_534_);
lean_dec_ref(v_as_531_);
return v_res_537_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_543_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__4));
v___x_544_ = lean_unsigned_to_nat(17u);
v___x_545_ = lean_unsigned_to_nat(128u);
v___x_546_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__3));
v___x_547_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__2));
v___x_548_ = l_mkPanicMessageWithDecl(v___x_547_, v___x_546_, v___x_545_, v___x_544_, v___x_543_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3(lean_object* v_fst_549_, lean_object* v_as_550_, size_t v_i_551_, size_t v_stop_552_, lean_object* v_b_553_){
_start:
{
lean_object* v___y_555_; lean_object* v___y_560_; uint8_t v___x_563_; 
v___x_563_ = lean_usize_dec_eq(v_i_551_, v_stop_552_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; 
v___x_564_ = lean_array_uget_borrowed(v_as_550_, v_i_551_);
if (lean_obj_tag(v___x_564_) == 6)
{
lean_object* v_xs_565_; lean_object* v_items_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v_s_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v_xs_565_ = lean_ctor_get(v___x_564_, 1);
v_items_566_ = lean_ctor_get(v_xs_565_, 0);
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__0));
lean_inc(v_fst_549_);
v___x_569_ = l_Lake_Toml_ppKey(v_fst_549_);
v___x_570_ = lean_string_append(v___x_568_, v___x_569_);
lean_dec_ref(v___x_569_);
v___x_571_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__1));
v___x_572_ = lean_string_append(v___x_570_, v___x_571_);
v_s_573_ = lean_string_append(v_b_553_, v___x_572_);
lean_dec_ref(v___x_572_);
v___x_574_ = lean_array_get_size(v_items_566_);
v___x_575_ = lean_nat_dec_lt(v___x_567_, v___x_574_);
if (v___x_575_ == 0)
{
v___y_560_ = v_s_573_;
goto v___jp_559_;
}
else
{
uint8_t v___x_576_; 
v___x_576_ = lean_nat_dec_le(v___x_574_, v___x_574_);
if (v___x_576_ == 0)
{
if (v___x_575_ == 0)
{
v___y_560_ = v_s_573_;
goto v___jp_559_;
}
else
{
size_t v___x_577_; size_t v___x_578_; lean_object* v___x_579_; 
v___x_577_ = ((size_t)0ULL);
v___x_578_ = lean_usize_of_nat(v___x_574_);
v___x_579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_items_566_, v___x_577_, v___x_578_, v_s_573_);
v___y_560_ = v___x_579_;
goto v___jp_559_;
}
}
else
{
size_t v___x_580_; size_t v___x_581_; lean_object* v___x_582_; 
v___x_580_ = ((size_t)0ULL);
v___x_581_ = lean_usize_of_nat(v___x_574_);
v___x_582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_items_566_, v___x_580_, v___x_581_, v_s_573_);
v___y_560_ = v___x_582_;
goto v___jp_559_;
}
}
}
else
{
lean_object* v___x_583_; lean_object* v___x_584_; 
lean_dec_ref(v_b_553_);
v___x_583_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5);
v___x_584_ = l_panic___at___00Lake_Toml_ppTable_spec__2(v___x_583_);
v___y_555_ = v___x_584_;
goto v___jp_554_;
}
}
else
{
lean_dec(v_fst_549_);
return v_b_553_;
}
v___jp_554_:
{
size_t v___x_556_; size_t v___x_557_; 
v___x_556_ = ((size_t)1ULL);
v___x_557_ = lean_usize_add(v_i_551_, v___x_556_);
v_i_551_ = v___x_557_;
v_b_553_ = v___y_555_;
goto _start;
}
v___jp_559_:
{
uint32_t v___x_561_; lean_object* v___x_562_; 
v___x_561_ = 10;
v___x_562_ = lean_string_push(v___y_560_, v___x_561_);
v___y_555_ = v___x_562_;
goto v___jp_554_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___boxed(lean_object* v_fst_585_, lean_object* v_as_586_, lean_object* v_i_587_, lean_object* v_stop_588_, lean_object* v_b_589_){
_start:
{
size_t v_i_boxed_590_; size_t v_stop_boxed_591_; lean_object* v_res_592_; 
v_i_boxed_590_ = lean_unbox_usize(v_i_587_);
lean_dec(v_i_587_);
v_stop_boxed_591_ = lean_unbox_usize(v_stop_588_);
lean_dec(v_stop_588_);
v_res_592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3(v_fst_585_, v_as_586_, v_i_boxed_590_, v_stop_boxed_591_, v_b_589_);
lean_dec_ref(v_as_586_);
return v_res_592_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Toml_ppTable_spec__4(lean_object* v___x_593_, lean_object* v_as_594_, size_t v_i_595_, size_t v_stop_596_){
_start:
{
uint8_t v___x_597_; 
v___x_597_ = lean_usize_dec_eq(v_i_595_, v_stop_596_);
if (v___x_597_ == 0)
{
uint8_t v___x_598_; lean_object* v___x_599_; 
v___x_598_ = 1;
v___x_599_ = lean_array_uget_borrowed(v_as_594_, v_i_595_);
if (lean_obj_tag(v___x_599_) == 6)
{
lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_600_ = lean_unsigned_to_nat(0u);
v___x_601_ = lean_nat_dec_eq(v___x_593_, v___x_600_);
if (v___x_601_ == 0)
{
size_t v___x_602_; size_t v___x_603_; 
v___x_602_ = ((size_t)1ULL);
v___x_603_ = lean_usize_add(v_i_595_, v___x_602_);
v_i_595_ = v___x_603_;
goto _start;
}
else
{
return v___x_598_;
}
}
else
{
return v___x_598_;
}
}
else
{
uint8_t v___x_605_; 
v___x_605_ = 0;
return v___x_605_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Toml_ppTable_spec__4___boxed(lean_object* v___x_606_, lean_object* v_as_607_, lean_object* v_i_608_, lean_object* v_stop_609_){
_start:
{
size_t v_i_boxed_610_; size_t v_stop_boxed_611_; uint8_t v_res_612_; lean_object* v_r_613_; 
v_i_boxed_610_ = lean_unbox_usize(v_i_608_);
lean_dec(v_i_608_);
v_stop_boxed_611_ = lean_unbox_usize(v_stop_609_);
lean_dec(v_stop_609_);
v_res_612_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Toml_ppTable_spec__4(v___x_606_, v_as_607_, v_i_boxed_610_, v_stop_boxed_611_);
lean_dec_ref(v_as_607_);
lean_dec(v___x_606_);
v_r_613_ = lean_box(v_res_612_);
return v_r_613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5(lean_object* v_as_616_, size_t v_i_617_, size_t v_stop_618_, lean_object* v_b_619_){
_start:
{
lean_object* v___y_621_; uint8_t v___x_625_; 
v___x_625_ = lean_usize_dec_eq(v_i_617_, v_stop_618_);
if (v___x_625_ == 0)
{
lean_object* v_fst_626_; lean_object* v_snd_627_; lean_object* v___y_629_; lean_object* v___x_633_; lean_object* v_snd_634_; 
v_fst_626_ = lean_ctor_get(v_b_619_, 0);
v_snd_627_ = lean_ctor_get(v_b_619_, 1);
v___x_633_ = lean_array_uget(v_as_616_, v_i_617_);
v_snd_634_ = lean_ctor_get(v___x_633_, 1);
switch(lean_obj_tag(v_snd_634_))
{
case 5:
{
lean_object* v_fst_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_692_; 
lean_inc_ref(v_snd_634_);
v_fst_635_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_692_ == 0)
{
lean_object* v_unused_693_; 
v_unused_693_ = lean_ctor_get(v___x_633_, 1);
lean_dec(v_unused_693_);
v___x_637_ = v___x_633_;
v_isShared_638_ = v_isSharedCheck_692_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_fst_635_);
lean_dec(v___x_633_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_692_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v_xs_639_; lean_object* v___x_640_; lean_object* v___x_641_; uint8_t v___x_657_; 
v_xs_639_ = lean_ctor_get(v_snd_634_, 1);
lean_inc_ref(v_xs_639_);
lean_dec_ref_known(v_snd_634_, 2);
v___x_640_ = lean_array_get_size(v_xs_639_);
v___x_641_ = lean_unsigned_to_nat(0u);
v___x_657_ = lean_nat_dec_eq(v___x_640_, v___x_641_);
if (v___x_657_ == 0)
{
uint8_t v___x_658_; 
v___x_658_ = lean_nat_dec_lt(v___x_641_, v___x_640_);
if (v___x_658_ == 0)
{
goto v___jp_642_;
}
else
{
if (v___x_658_ == 0)
{
goto v___jp_642_;
}
else
{
size_t v___x_659_; size_t v___x_660_; uint8_t v___x_661_; 
v___x_659_ = ((size_t)0ULL);
v___x_660_ = lean_usize_of_nat(v___x_640_);
v___x_661_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Toml_ppTable_spec__4(v___x_640_, v_xs_639_, v___x_659_, v___x_660_);
if (v___x_661_ == 0)
{
goto v___jp_642_;
}
else
{
lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_676_; 
lean_inc(v_snd_627_);
lean_inc(v_fst_626_);
lean_del_object(v___x_637_);
v_isSharedCheck_676_ = !lean_is_exclusive(v_b_619_);
if (v_isSharedCheck_676_ == 0)
{
lean_object* v_unused_677_; lean_object* v_unused_678_; 
v_unused_677_ = lean_ctor_get(v_b_619_, 1);
lean_dec(v_unused_677_);
v_unused_678_ = lean_ctor_get(v_b_619_, 0);
lean_dec(v_unused_678_);
v___x_663_ = v_b_619_;
v_isShared_664_ = v_isSharedCheck_676_;
goto v_resetjp_662_;
}
else
{
lean_dec(v_b_619_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_676_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_665_ = l_Lake_Toml_ppKey(v_fst_635_);
v___x_666_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___closed__0));
v___x_667_ = lean_string_append(v___x_665_, v___x_666_);
v___x_668_ = l_Lake_Toml_ppInlineArray(v_xs_639_);
v___x_669_ = lean_string_append(v___x_667_, v___x_668_);
lean_dec_ref(v___x_668_);
v___x_670_ = ((lean_object*)(l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval___closed__0));
v___x_671_ = lean_string_append(v___x_669_, v___x_670_);
v___x_672_ = lean_string_append(v_fst_626_, v___x_671_);
lean_dec_ref(v___x_671_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 0, v___x_672_);
v___x_674_ = v___x_663_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_snd_627_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
v___y_621_ = v___x_674_;
goto v___jp_620_;
}
}
}
}
}
}
else
{
lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_689_; 
lean_inc(v_snd_627_);
lean_inc(v_fst_626_);
lean_dec_ref(v_xs_639_);
lean_del_object(v___x_637_);
v_isSharedCheck_689_ = !lean_is_exclusive(v_b_619_);
if (v_isSharedCheck_689_ == 0)
{
lean_object* v_unused_690_; lean_object* v_unused_691_; 
v_unused_690_ = lean_ctor_get(v_b_619_, 1);
lean_dec(v_unused_690_);
v_unused_691_ = lean_ctor_get(v_b_619_, 0);
lean_dec(v_unused_691_);
v___x_680_ = v_b_619_;
v_isShared_681_ = v_isSharedCheck_689_;
goto v_resetjp_679_;
}
else
{
lean_dec(v_b_619_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_689_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_687_; 
v___x_682_ = l_Lake_Toml_ppKey(v_fst_635_);
v___x_683_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___closed__0));
v___x_684_ = lean_string_append(v___x_682_, v___x_683_);
v___x_685_ = lean_string_append(v_fst_626_, v___x_684_);
lean_dec_ref(v___x_684_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v___x_685_);
v___x_687_ = v___x_680_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_685_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v_snd_627_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
v___y_621_ = v___x_687_;
goto v___jp_620_;
}
}
}
v___jp_642_:
{
uint8_t v___x_643_; 
v___x_643_ = lean_nat_dec_lt(v___x_641_, v___x_640_);
if (v___x_643_ == 0)
{
lean_dec_ref(v_xs_639_);
lean_del_object(v___x_637_);
lean_dec(v_fst_635_);
v___y_621_ = v_b_619_;
goto v___jp_620_;
}
else
{
uint8_t v___x_644_; 
v___x_644_ = lean_nat_dec_le(v___x_640_, v___x_640_);
if (v___x_644_ == 0)
{
if (v___x_643_ == 0)
{
lean_dec_ref(v_xs_639_);
lean_del_object(v___x_637_);
lean_dec(v_fst_635_);
v___y_621_ = v_b_619_;
goto v___jp_620_;
}
else
{
size_t v___x_645_; size_t v___x_646_; lean_object* v___x_647_; lean_object* v___x_649_; 
lean_inc(v_snd_627_);
lean_inc(v_fst_626_);
lean_dec_ref(v_b_619_);
v___x_645_ = ((size_t)0ULL);
v___x_646_ = lean_usize_of_nat(v___x_640_);
v___x_647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3(v_fst_635_, v_xs_639_, v___x_645_, v___x_646_, v_snd_627_);
lean_dec_ref(v_xs_639_);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 1, v___x_647_);
lean_ctor_set(v___x_637_, 0, v_fst_626_);
v___x_649_ = v___x_637_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_fst_626_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v___x_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
v___y_621_ = v___x_649_;
goto v___jp_620_;
}
}
}
else
{
size_t v___x_651_; size_t v___x_652_; lean_object* v___x_653_; lean_object* v___x_655_; 
lean_inc(v_snd_627_);
lean_inc(v_fst_626_);
lean_dec_ref(v_b_619_);
v___x_651_ = ((size_t)0ULL);
v___x_652_ = lean_usize_of_nat(v___x_640_);
v___x_653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3(v_fst_635_, v_xs_639_, v___x_651_, v___x_652_, v_snd_627_);
lean_dec_ref(v_xs_639_);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 1, v___x_653_);
lean_ctor_set(v___x_637_, 0, v_fst_626_);
v___x_655_ = v___x_637_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_fst_626_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v___x_653_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
v___y_621_ = v___x_655_;
goto v___jp_620_;
}
}
}
}
}
}
case 6:
{
lean_object* v_xs_694_; lean_object* v_fst_695_; lean_object* v_items_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v_fs_702_; lean_object* v___x_703_; lean_object* v___x_704_; uint8_t v___x_705_; 
lean_inc(v_snd_627_);
lean_inc(v_fst_626_);
lean_dec_ref(v_b_619_);
v_xs_694_ = lean_ctor_get(v_snd_634_, 1);
lean_inc_ref(v_xs_694_);
v_fst_695_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_fst_695_);
lean_dec(v___x_633_);
v_items_696_ = lean_ctor_get(v_xs_694_, 0);
lean_inc_ref(v_items_696_);
lean_dec_ref(v_xs_694_);
v___x_697_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__0));
v___x_698_ = l_Lake_Toml_ppKey(v_fst_695_);
v___x_699_ = lean_string_append(v___x_697_, v___x_698_);
lean_dec_ref(v___x_698_);
v___x_700_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___closed__1));
v___x_701_ = lean_string_append(v___x_699_, v___x_700_);
v_fs_702_ = lean_string_append(v_snd_627_, v___x_701_);
lean_dec_ref(v___x_701_);
v___x_703_ = lean_unsigned_to_nat(0u);
v___x_704_ = lean_array_get_size(v_items_696_);
v___x_705_ = lean_nat_dec_lt(v___x_703_, v___x_704_);
if (v___x_705_ == 0)
{
lean_dec_ref(v_items_696_);
v___y_629_ = v_fs_702_;
goto v___jp_628_;
}
else
{
uint8_t v___x_706_; 
v___x_706_ = lean_nat_dec_le(v___x_704_, v___x_704_);
if (v___x_706_ == 0)
{
if (v___x_705_ == 0)
{
lean_dec_ref(v_items_696_);
v___y_629_ = v_fs_702_;
goto v___jp_628_;
}
else
{
size_t v___x_707_; size_t v___x_708_; lean_object* v___x_709_; 
v___x_707_ = ((size_t)0ULL);
v___x_708_ = lean_usize_of_nat(v___x_704_);
v___x_709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_items_696_, v___x_707_, v___x_708_, v_fs_702_);
lean_dec_ref(v_items_696_);
v___y_629_ = v___x_709_;
goto v___jp_628_;
}
}
else
{
size_t v___x_710_; size_t v___x_711_; lean_object* v___x_712_; 
v___x_710_ = ((size_t)0ULL);
v___x_711_ = lean_usize_of_nat(v___x_704_);
v___x_712_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_items_696_, v___x_710_, v___x_711_, v_fs_702_);
lean_dec_ref(v_items_696_);
v___y_629_ = v___x_712_;
goto v___jp_628_;
}
}
}
default: 
{
lean_object* v_fst_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_721_; 
lean_inc(v_snd_634_);
lean_inc(v_snd_627_);
lean_inc(v_fst_626_);
lean_dec_ref(v_b_619_);
v_fst_713_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_721_ == 0)
{
lean_object* v_unused_722_; 
v_unused_722_ = lean_ctor_get(v___x_633_, 1);
lean_dec(v_unused_722_);
v___x_715_ = v___x_633_;
v_isShared_716_ = v_isSharedCheck_721_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_fst_713_);
lean_dec(v___x_633_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_721_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_717_; lean_object* v___x_719_; 
v___x_717_ = l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval(v_fst_626_, v_fst_713_, v_snd_634_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 1, v_snd_627_);
lean_ctor_set(v___x_715_, 0, v___x_717_);
v___x_719_ = v___x_715_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_717_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v_snd_627_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
v___y_621_ = v___x_719_;
goto v___jp_620_;
}
}
}
}
v___jp_628_:
{
uint32_t v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_630_ = 10;
v___x_631_ = lean_string_push(v___y_629_, v___x_630_);
v___x_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_632_, 0, v_fst_626_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___y_621_ = v___x_632_;
goto v___jp_620_;
}
}
else
{
return v_b_619_;
}
v___jp_620_:
{
size_t v___x_622_; size_t v___x_623_; 
v___x_622_ = ((size_t)1ULL);
v___x_623_ = lean_usize_add(v_i_617_, v___x_622_);
v_i_617_ = v___x_623_;
v_b_619_ = v___y_621_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___boxed(lean_object* v_as_723_, lean_object* v_i_724_, lean_object* v_stop_725_, lean_object* v_b_726_){
_start:
{
size_t v_i_boxed_727_; size_t v_stop_boxed_728_; lean_object* v_res_729_; 
v_i_boxed_727_ = lean_unbox_usize(v_i_724_);
lean_dec(v_i_724_);
v_stop_boxed_728_ = lean_unbox_usize(v_stop_725_);
lean_dec(v_stop_725_);
v_res_729_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5(v_as_723_, v_i_boxed_727_, v_stop_boxed_728_, v_b_726_);
lean_dec_ref(v_as_723_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lake_Toml_ppTable_spec__0(lean_object* v_s_730_, lean_object* v_pos_731_){
_start:
{
lean_object* v_str_732_; lean_object* v_startInclusive_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; uint8_t v_decide_737_; 
v_str_732_ = lean_ctor_get(v_s_730_, 0);
v_startInclusive_733_ = lean_ctor_get(v_s_730_, 1);
v___x_734_ = lean_nat_add(v_startInclusive_733_, v_pos_731_);
v___x_735_ = lean_nat_sub(v___x_734_, v_startInclusive_733_);
v___x_736_ = lean_unsigned_to_nat(0u);
v_decide_737_ = lean_nat_dec_eq(v___x_735_, v___x_736_);
if (v_decide_737_ == 0)
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_746_; uint32_t v___x_747_; uint32_t v___x_748_; uint8_t v___x_749_; 
lean_inc(v_startInclusive_733_);
lean_inc_ref(v_str_732_);
v___x_738_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_738_, 0, v_str_732_);
lean_ctor_set(v___x_738_, 1, v_startInclusive_733_);
lean_ctor_set(v___x_738_, 2, v___x_734_);
v___x_739_ = lean_unsigned_to_nat(1u);
v___x_740_ = lean_nat_sub(v___x_735_, v___x_739_);
lean_dec(v___x_735_);
v___x_741_ = l_String_Slice_posLE(v___x_738_, v___x_740_);
lean_dec_ref_known(v___x_738_, 3);
v___x_746_ = lean_nat_add(v_startInclusive_733_, v___x_741_);
v___x_747_ = lean_string_utf8_get_fast(v_str_732_, v___x_746_);
lean_dec(v___x_746_);
v___x_748_ = 32;
v___x_749_ = lean_uint32_dec_eq(v___x_747_, v___x_748_);
if (v___x_749_ == 0)
{
uint32_t v___x_750_; uint8_t v___x_751_; 
v___x_750_ = 9;
v___x_751_ = lean_uint32_dec_eq(v___x_747_, v___x_750_);
if (v___x_751_ == 0)
{
uint32_t v___x_752_; uint8_t v___x_753_; 
v___x_752_ = 13;
v___x_753_ = lean_uint32_dec_eq(v___x_747_, v___x_752_);
if (v___x_753_ == 0)
{
uint32_t v___x_754_; uint8_t v___x_755_; 
v___x_754_ = 10;
v___x_755_ = lean_uint32_dec_eq(v___x_747_, v___x_754_);
if (v___x_755_ == 0)
{
lean_dec(v___x_741_);
return v_pos_731_;
}
else
{
goto v___jp_742_;
}
}
else
{
goto v___jp_742_;
}
}
else
{
goto v___jp_742_;
}
}
else
{
goto v___jp_742_;
}
v___jp_742_:
{
lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_743_ = lean_nat_add(v___x_741_, v___x_739_);
v___x_744_ = lean_nat_dec_le(v___x_743_, v_pos_731_);
lean_dec(v___x_743_);
if (v___x_744_ == 0)
{
lean_dec(v___x_741_);
return v_pos_731_;
}
else
{
lean_dec(v_pos_731_);
v_pos_731_ = v___x_741_;
goto _start;
}
}
}
else
{
lean_dec(v___x_735_);
lean_dec(v___x_734_);
return v_pos_731_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lake_Toml_ppTable_spec__0___boxed(lean_object* v_s_756_, lean_object* v_pos_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_String_Slice_Pos_revSkipWhile___at___00Lake_Toml_ppTable_spec__0(v_s_756_, v_pos_757_);
lean_dec_ref(v_s_756_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppTable(lean_object* v_t_761_){
_start:
{
lean_object* v_fst_763_; lean_object* v_snd_764_; lean_object* v___y_775_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v_items_780_; lean_object* v___x_781_; lean_object* v___x_782_; uint8_t v___x_783_; 
v___x_778_ = ((lean_object*)(l_Lake_Toml_instInhabitedValue_default___closed__0));
v___x_779_ = ((lean_object*)(l_Lake_Toml_ppTable___closed__0));
v_items_780_ = lean_ctor_get(v_t_761_, 0);
v___x_781_ = lean_unsigned_to_nat(0u);
v___x_782_ = lean_array_get_size(v_items_780_);
v___x_783_ = lean_nat_dec_lt(v___x_781_, v___x_782_);
if (v___x_783_ == 0)
{
v_fst_763_ = v___x_778_;
v_snd_764_ = v___x_778_;
goto v___jp_762_;
}
else
{
uint8_t v___x_784_; 
v___x_784_ = lean_nat_dec_le(v___x_782_, v___x_782_);
if (v___x_784_ == 0)
{
if (v___x_783_ == 0)
{
v_fst_763_ = v___x_778_;
v_snd_764_ = v___x_778_;
goto v___jp_762_;
}
else
{
size_t v___x_785_; size_t v___x_786_; lean_object* v___x_787_; 
v___x_785_ = ((size_t)0ULL);
v___x_786_ = lean_usize_of_nat(v___x_782_);
v___x_787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5(v_items_780_, v___x_785_, v___x_786_, v___x_779_);
v___y_775_ = v___x_787_;
goto v___jp_774_;
}
}
else
{
size_t v___x_788_; size_t v___x_789_; lean_object* v___x_790_; 
v___x_788_ = ((size_t)0ULL);
v___x_789_ = lean_usize_of_nat(v___x_782_);
v___x_790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5(v_items_780_, v___x_788_, v___x_789_, v___x_779_);
v___y_775_ = v___x_790_;
goto v___jp_774_;
}
}
v___jp_762_:
{
uint32_t v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_765_ = 10;
v___x_766_ = lean_string_push(v_fst_763_, v___x_765_);
v___x_767_ = lean_string_append(v___x_766_, v_snd_764_);
lean_dec_ref(v_snd_764_);
v___x_768_ = lean_unsigned_to_nat(0u);
v___x_769_ = lean_string_utf8_byte_size(v___x_767_);
lean_inc_ref(v___x_767_);
v___x_770_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_770_, 0, v___x_767_);
lean_ctor_set(v___x_770_, 1, v___x_768_);
lean_ctor_set(v___x_770_, 2, v___x_769_);
v___x_771_ = l_String_Slice_Pos_revSkipWhile___at___00Lake_Toml_ppTable_spec__0(v___x_770_, v___x_769_);
lean_dec_ref_known(v___x_770_, 3);
v___x_772_ = lean_string_utf8_extract_fast(v___x_767_, v___x_768_, v___x_771_);
lean_dec(v___x_771_);
lean_dec_ref(v___x_767_);
v___x_773_ = lean_string_push(v___x_772_, v___x_765_);
return v___x_773_;
}
v___jp_774_:
{
lean_object* v_fst_776_; lean_object* v_snd_777_; 
v_fst_776_ = lean_ctor_get(v___y_775_, 0);
lean_inc(v_fst_776_);
v_snd_777_ = lean_ctor_get(v___y_775_, 1);
lean_inc(v_snd_777_);
lean_dec_ref(v___y_775_);
v_fst_763_ = v_fst_776_;
v_snd_764_ = v_snd_777_;
goto v___jp_762_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppTable___boxed(lean_object* v_t_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Lake_Toml_ppTable(v_t_791_);
lean_dec_ref(v_t_791_);
return v_res_792_;
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

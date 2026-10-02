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
lean_object* l_Lake_Toml_RBDict_empty___redArg();
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_Toml_Value_ctorIdx(lean_object* v_x_1_){
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
case 5:
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(5u);
return v___x_7_;
}
default: 
{
lean_object* v___x_8_; 
v___x_8_ = lean_unsigned_to_nat(6u);
return v___x_8_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_ctorIdx___boxed(lean_object* v_x_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lake_Toml_Value_ctorIdx(v_x_9_);
lean_dec_ref(v_x_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_ctorElim___redArg(lean_object* v_t_11_, lean_object* v_k_12_){
_start:
{
switch(lean_obj_tag(v_t_11_))
{
case 1:
{
lean_object* v_ref_13_; lean_object* v_n_14_; lean_object* v___x_15_; 
v_ref_13_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_ref_13_);
v_n_14_ = lean_ctor_get(v_t_11_, 1);
lean_inc(v_n_14_);
lean_dec_ref_known(v_t_11_, 2);
v___x_15_ = lean_apply_2(v_k_12_, v_ref_13_, v_n_14_);
return v___x_15_;
}
case 2:
{
lean_object* v_ref_16_; double v_n_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v_ref_16_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_ref_16_);
v_n_17_ = lean_ctor_get_float(v_t_11_, sizeof(void*)*1);
lean_dec_ref_known(v_t_11_, 1);
v___x_18_ = lean_box_float(v_n_17_);
v___x_19_ = lean_apply_2(v_k_12_, v_ref_16_, v___x_18_);
return v___x_19_;
}
case 3:
{
lean_object* v_ref_20_; uint8_t v_b_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v_ref_20_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_ref_20_);
v_b_21_ = lean_ctor_get_uint8(v_t_11_, sizeof(void*)*1);
lean_dec_ref_known(v_t_11_, 1);
v___x_22_ = lean_box(v_b_21_);
v___x_23_ = lean_apply_2(v_k_12_, v_ref_20_, v___x_22_);
return v___x_23_;
}
default: 
{
lean_object* v_ref_24_; lean_object* v_s_25_; lean_object* v___x_26_; 
v_ref_24_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_ref_24_);
v_s_25_ = lean_ctor_get(v_t_11_, 1);
lean_inc_ref(v_s_25_);
lean_dec_ref(v_t_11_);
v___x_26_ = lean_apply_2(v_k_12_, v_ref_24_, v_s_25_);
return v___x_26_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_ctorElim(lean_object* v_motive__1_27_, lean_object* v_ctorIdx_28_, lean_object* v_t_29_, lean_object* v_h_30_, lean_object* v_k_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_29_, v_k_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_ctorElim___boxed(lean_object* v_motive__1_33_, lean_object* v_ctorIdx_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_k_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lake_Toml_Value_ctorElim(v_motive__1_33_, v_ctorIdx_34_, v_t_35_, v_h_36_, v_k_37_);
lean_dec(v_ctorIdx_34_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_string_elim___redArg(lean_object* v_t_39_, lean_object* v_string_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_39_, v_string_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_string_elim(lean_object* v_motive__1_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_string_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_43_, v_string_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_integer_elim___redArg(lean_object* v_t_47_, lean_object* v_integer_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_47_, v_integer_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_integer_elim(lean_object* v_motive__1_50_, lean_object* v_t_51_, lean_object* v_h_52_, lean_object* v_integer_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_51_, v_integer_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_float_elim___redArg(lean_object* v_t_55_, lean_object* v_float_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_55_, v_float_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_float_elim(lean_object* v_motive__1_58_, lean_object* v_t_59_, lean_object* v_h_60_, lean_object* v_float_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_59_, v_float_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_boolean_elim___redArg(lean_object* v_t_63_, lean_object* v_boolean_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_63_, v_boolean_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_boolean_elim(lean_object* v_motive__1_66_, lean_object* v_t_67_, lean_object* v_h_68_, lean_object* v_boolean_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_67_, v_boolean_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_dateTime_elim___redArg(lean_object* v_t_71_, lean_object* v_dateTime_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_71_, v_dateTime_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_dateTime_elim(lean_object* v_motive__1_74_, lean_object* v_t_75_, lean_object* v_h_76_, lean_object* v_dateTime_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_75_, v_dateTime_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_array_elim___redArg(lean_object* v_t_79_, lean_object* v_array_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_79_, v_array_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_array_elim(lean_object* v_motive__1_82_, lean_object* v_t_83_, lean_object* v_h_84_, lean_object* v_array_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_83_, v_array_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_table_x27_elim___redArg(lean_object* v_t_87_, lean_object* v_table_x27_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_87_, v_table_x27_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_table_x27_elim(lean_object* v_motive__1_90_, lean_object* v_t_91_, lean_object* v_h_92_, lean_object* v_table_x27_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_91_, v_table_x27_93_);
return v___x_94_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0___redArg(lean_object* v_xs_101_, lean_object* v_ys_102_, lean_object* v_x_103_){
_start:
{
lean_object* v_zero_104_; uint8_t v_isZero_105_; 
v_zero_104_ = lean_unsigned_to_nat(0u);
v_isZero_105_ = lean_nat_dec_eq(v_x_103_, v_zero_104_);
if (v_isZero_105_ == 1)
{
lean_dec(v_x_103_);
return v_isZero_105_;
}
else
{
lean_object* v_one_106_; lean_object* v_n_107_; lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; 
v_one_106_ = lean_unsigned_to_nat(1u);
v_n_107_ = lean_nat_sub(v_x_103_, v_one_106_);
lean_dec(v_x_103_);
v___x_108_ = lean_array_fget_borrowed(v_xs_101_, v_n_107_);
v___x_109_ = lean_array_fget_borrowed(v_ys_102_, v_n_107_);
lean_inc(v___x_109_);
lean_inc(v___x_108_);
v___x_110_ = l_Lake_Toml_instBEqValue_beq(v___x_108_, v___x_109_);
if (v___x_110_ == 0)
{
lean_dec(v_n_107_);
return v___x_110_;
}
else
{
v_x_103_ = v_n_107_;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_instBEqValue_beq(lean_object* v_x_112_, lean_object* v_x_113_){
_start:
{
switch(lean_obj_tag(v_x_112_))
{
case 0:
{
if (lean_obj_tag(v_x_113_) == 0)
{
lean_object* v_ref_114_; lean_object* v_s_115_; lean_object* v_ref_116_; lean_object* v_s_117_; uint8_t v___x_118_; 
v_ref_114_ = lean_ctor_get(v_x_112_, 0);
lean_inc(v_ref_114_);
v_s_115_ = lean_ctor_get(v_x_112_, 1);
lean_inc_ref(v_s_115_);
lean_dec_ref_known(v_x_112_, 2);
v_ref_116_ = lean_ctor_get(v_x_113_, 0);
lean_inc(v_ref_116_);
v_s_117_ = lean_ctor_get(v_x_113_, 1);
lean_inc_ref(v_s_117_);
lean_dec_ref_known(v_x_113_, 2);
v___x_118_ = l_Lean_Syntax_structEq(v_ref_114_, v_ref_116_);
lean_dec(v_ref_116_);
lean_dec(v_ref_114_);
if (v___x_118_ == 0)
{
lean_dec_ref(v_s_117_);
lean_dec_ref(v_s_115_);
return v___x_118_;
}
else
{
uint8_t v___x_119_; 
v___x_119_ = lean_string_dec_eq(v_s_115_, v_s_117_);
lean_dec_ref(v_s_117_);
lean_dec_ref(v_s_115_);
return v___x_119_;
}
}
else
{
uint8_t v___x_120_; 
lean_dec_ref_known(v_x_112_, 2);
lean_dec_ref(v_x_113_);
v___x_120_ = 0;
return v___x_120_;
}
}
case 1:
{
if (lean_obj_tag(v_x_113_) == 1)
{
lean_object* v_ref_121_; lean_object* v_n_122_; lean_object* v_ref_123_; lean_object* v_n_124_; uint8_t v___x_125_; 
v_ref_121_ = lean_ctor_get(v_x_112_, 0);
lean_inc(v_ref_121_);
v_n_122_ = lean_ctor_get(v_x_112_, 1);
lean_inc(v_n_122_);
lean_dec_ref_known(v_x_112_, 2);
v_ref_123_ = lean_ctor_get(v_x_113_, 0);
lean_inc(v_ref_123_);
v_n_124_ = lean_ctor_get(v_x_113_, 1);
lean_inc(v_n_124_);
lean_dec_ref_known(v_x_113_, 2);
v___x_125_ = l_Lean_Syntax_structEq(v_ref_121_, v_ref_123_);
lean_dec(v_ref_123_);
lean_dec(v_ref_121_);
if (v___x_125_ == 0)
{
lean_dec(v_n_124_);
lean_dec(v_n_122_);
return v___x_125_;
}
else
{
uint8_t v___x_126_; 
v___x_126_ = lean_int_dec_eq(v_n_122_, v_n_124_);
lean_dec(v_n_124_);
lean_dec(v_n_122_);
return v___x_126_;
}
}
else
{
uint8_t v___x_127_; 
lean_dec_ref_known(v_x_112_, 2);
lean_dec_ref(v_x_113_);
v___x_127_ = 0;
return v___x_127_;
}
}
case 2:
{
if (lean_obj_tag(v_x_113_) == 2)
{
lean_object* v_ref_128_; double v_n_129_; lean_object* v_ref_130_; double v_n_131_; uint8_t v___x_132_; 
v_ref_128_ = lean_ctor_get(v_x_112_, 0);
lean_inc(v_ref_128_);
v_n_129_ = lean_ctor_get_float(v_x_112_, sizeof(void*)*1);
lean_dec_ref_known(v_x_112_, 1);
v_ref_130_ = lean_ctor_get(v_x_113_, 0);
lean_inc(v_ref_130_);
v_n_131_ = lean_ctor_get_float(v_x_113_, sizeof(void*)*1);
lean_dec_ref_known(v_x_113_, 1);
v___x_132_ = l_Lean_Syntax_structEq(v_ref_128_, v_ref_130_);
lean_dec(v_ref_130_);
lean_dec(v_ref_128_);
if (v___x_132_ == 0)
{
return v___x_132_;
}
else
{
uint8_t v___x_133_; 
v___x_133_ = lean_float_beq(v_n_129_, v_n_131_);
return v___x_133_;
}
}
else
{
uint8_t v___x_134_; 
lean_dec_ref_known(v_x_112_, 1);
lean_dec_ref(v_x_113_);
v___x_134_ = 0;
return v___x_134_;
}
}
case 3:
{
if (lean_obj_tag(v_x_113_) == 3)
{
lean_object* v_ref_135_; uint8_t v_b_136_; lean_object* v_ref_137_; uint8_t v_b_138_; uint8_t v___x_139_; 
v_ref_135_ = lean_ctor_get(v_x_112_, 0);
lean_inc(v_ref_135_);
v_b_136_ = lean_ctor_get_uint8(v_x_112_, sizeof(void*)*1);
lean_dec_ref_known(v_x_112_, 1);
v_ref_137_ = lean_ctor_get(v_x_113_, 0);
lean_inc(v_ref_137_);
v_b_138_ = lean_ctor_get_uint8(v_x_113_, sizeof(void*)*1);
lean_dec_ref_known(v_x_113_, 1);
v___x_139_ = l_Lean_Syntax_structEq(v_ref_135_, v_ref_137_);
lean_dec(v_ref_137_);
lean_dec(v_ref_135_);
if (v___x_139_ == 0)
{
return v___x_139_;
}
else
{
if (v_b_138_ == 0)
{
if (v_b_136_ == 0)
{
return v___x_139_;
}
else
{
return v_b_138_;
}
}
else
{
return v_b_136_;
}
}
}
else
{
uint8_t v___x_140_; 
lean_dec_ref_known(v_x_112_, 1);
lean_dec_ref(v_x_113_);
v___x_140_ = 0;
return v___x_140_;
}
}
case 4:
{
if (lean_obj_tag(v_x_113_) == 4)
{
lean_object* v_ref_141_; lean_object* v_dt_142_; lean_object* v_ref_143_; lean_object* v_dt_144_; uint8_t v___x_145_; 
v_ref_141_ = lean_ctor_get(v_x_112_, 0);
lean_inc(v_ref_141_);
v_dt_142_ = lean_ctor_get(v_x_112_, 1);
lean_inc_ref(v_dt_142_);
lean_dec_ref_known(v_x_112_, 2);
v_ref_143_ = lean_ctor_get(v_x_113_, 0);
lean_inc(v_ref_143_);
v_dt_144_ = lean_ctor_get(v_x_113_, 1);
lean_inc_ref(v_dt_144_);
lean_dec_ref_known(v_x_113_, 2);
v___x_145_ = l_Lean_Syntax_structEq(v_ref_141_, v_ref_143_);
lean_dec(v_ref_143_);
lean_dec(v_ref_141_);
if (v___x_145_ == 0)
{
lean_dec_ref(v_dt_144_);
lean_dec_ref(v_dt_142_);
return v___x_145_;
}
else
{
uint8_t v___x_146_; 
v___x_146_ = l_Lake_Toml_instDecidableEqDateTime_decEq(v_dt_142_, v_dt_144_);
return v___x_146_;
}
}
else
{
uint8_t v___x_147_; 
lean_dec_ref_known(v_x_112_, 2);
lean_dec_ref(v_x_113_);
v___x_147_ = 0;
return v___x_147_;
}
}
case 5:
{
if (lean_obj_tag(v_x_113_) == 5)
{
lean_object* v_ref_148_; lean_object* v_xs_149_; lean_object* v_ref_150_; lean_object* v_xs_151_; uint8_t v___x_152_; 
v_ref_148_ = lean_ctor_get(v_x_112_, 0);
lean_inc(v_ref_148_);
v_xs_149_ = lean_ctor_get(v_x_112_, 1);
lean_inc_ref(v_xs_149_);
lean_dec_ref_known(v_x_112_, 2);
v_ref_150_ = lean_ctor_get(v_x_113_, 0);
lean_inc(v_ref_150_);
v_xs_151_ = lean_ctor_get(v_x_113_, 1);
lean_inc_ref(v_xs_151_);
lean_dec_ref_known(v_x_113_, 2);
v___x_152_ = l_Lean_Syntax_structEq(v_ref_148_, v_ref_150_);
lean_dec(v_ref_150_);
lean_dec(v_ref_148_);
if (v___x_152_ == 0)
{
lean_dec_ref(v_xs_151_);
lean_dec_ref(v_xs_149_);
return v___x_152_;
}
else
{
lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_153_ = lean_array_get_size(v_xs_149_);
v___x_154_ = lean_array_get_size(v_xs_151_);
v___x_155_ = lean_nat_dec_eq(v___x_153_, v___x_154_);
if (v___x_155_ == 0)
{
lean_dec_ref(v_xs_151_);
lean_dec_ref(v_xs_149_);
return v___x_155_;
}
else
{
uint8_t v___x_156_; 
v___x_156_ = l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0___redArg(v_xs_149_, v_xs_151_, v___x_153_);
lean_dec_ref(v_xs_151_);
lean_dec_ref(v_xs_149_);
return v___x_156_;
}
}
}
else
{
uint8_t v___x_157_; 
lean_dec_ref_known(v_x_112_, 2);
lean_dec_ref(v_x_113_);
v___x_157_ = 0;
return v___x_157_;
}
}
default: 
{
if (lean_obj_tag(v_x_113_) == 6)
{
lean_object* v_ref_158_; lean_object* v_xs_159_; lean_object* v_ref_160_; lean_object* v_xs_161_; uint8_t v___x_162_; 
v_ref_158_ = lean_ctor_get(v_x_112_, 0);
lean_inc(v_ref_158_);
v_xs_159_ = lean_ctor_get(v_x_112_, 1);
lean_inc_ref(v_xs_159_);
lean_dec_ref_known(v_x_112_, 2);
v_ref_160_ = lean_ctor_get(v_x_113_, 0);
lean_inc(v_ref_160_);
v_xs_161_ = lean_ctor_get(v_x_113_, 1);
lean_inc_ref(v_xs_161_);
lean_dec_ref_known(v_x_113_, 2);
v___x_162_ = l_Lean_Syntax_structEq(v_ref_158_, v_ref_160_);
lean_dec(v_ref_160_);
lean_dec(v_ref_158_);
if (v___x_162_ == 0)
{
lean_dec_ref(v_xs_161_);
lean_dec_ref(v_xs_159_);
return v___x_162_;
}
else
{
uint8_t v___x_163_; 
v___x_163_ = l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1___redArg(v_xs_159_, v_xs_161_);
lean_dec_ref(v_xs_161_);
lean_dec_ref(v_xs_159_);
return v___x_163_;
}
}
else
{
uint8_t v___x_164_; 
lean_dec_ref_known(v_x_112_, 2);
lean_dec_ref(v_x_113_);
v___x_164_ = 0;
return v___x_164_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___redArg(lean_object* v_xs_165_, lean_object* v_ys_166_, lean_object* v_x_167_){
_start:
{
lean_object* v_zero_168_; uint8_t v_isZero_169_; 
v_zero_168_ = lean_unsigned_to_nat(0u);
v_isZero_169_ = lean_nat_dec_eq(v_x_167_, v_zero_168_);
if (v_isZero_169_ == 1)
{
lean_dec(v_x_167_);
return v_isZero_169_;
}
else
{
lean_object* v_one_170_; lean_object* v_n_171_; uint8_t v___y_173_; lean_object* v___x_175_; lean_object* v_fst_176_; lean_object* v_snd_177_; lean_object* v___x_178_; lean_object* v_fst_179_; lean_object* v_snd_180_; uint8_t v___x_181_; 
v_one_170_ = lean_unsigned_to_nat(1u);
v_n_171_ = lean_nat_sub(v_x_167_, v_one_170_);
lean_dec(v_x_167_);
v___x_175_ = lean_array_fget_borrowed(v_xs_165_, v_n_171_);
v_fst_176_ = lean_ctor_get(v___x_175_, 0);
v_snd_177_ = lean_ctor_get(v___x_175_, 1);
v___x_178_ = lean_array_fget_borrowed(v_ys_166_, v_n_171_);
v_fst_179_ = lean_ctor_get(v___x_178_, 0);
v_snd_180_ = lean_ctor_get(v___x_178_, 1);
v___x_181_ = lean_name_eq(v_fst_176_, v_fst_179_);
if (v___x_181_ == 0)
{
v___y_173_ = v___x_181_;
goto v___jp_172_;
}
else
{
uint8_t v___x_182_; 
lean_inc(v_snd_180_);
lean_inc(v_snd_177_);
v___x_182_ = l_Lake_Toml_instBEqValue_beq(v_snd_177_, v_snd_180_);
v___y_173_ = v___x_182_;
goto v___jp_172_;
}
v___jp_172_:
{
if (v___y_173_ == 0)
{
lean_dec(v_n_171_);
return v___y_173_;
}
else
{
v_x_167_ = v_n_171_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1___redArg(lean_object* v_self_183_, lean_object* v_other_184_){
_start:
{
lean_object* v_items_185_; lean_object* v_items_186_; lean_object* v___x_187_; lean_object* v___x_188_; uint8_t v___x_189_; 
v_items_185_ = lean_ctor_get(v_self_183_, 0);
v_items_186_ = lean_ctor_get(v_other_184_, 0);
v___x_187_ = lean_array_get_size(v_items_185_);
v___x_188_ = lean_array_get_size(v_items_186_);
v___x_189_ = lean_nat_dec_eq(v___x_187_, v___x_188_);
if (v___x_189_ == 0)
{
return v___x_189_;
}
else
{
uint8_t v___x_190_; 
v___x_190_ = l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___redArg(v_items_185_, v_items_186_, v___x_187_);
return v___x_190_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1___redArg___boxed(lean_object* v_self_191_, lean_object* v_other_192_){
_start:
{
uint8_t v_res_193_; lean_object* v_r_194_; 
v_res_193_ = l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1___redArg(v_self_191_, v_other_192_);
lean_dec_ref(v_other_192_);
lean_dec_ref(v_self_191_);
v_r_194_ = lean_box(v_res_193_);
return v_r_194_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0___redArg___boxed(lean_object* v_xs_195_, lean_object* v_ys_196_, lean_object* v_x_197_){
_start:
{
uint8_t v_res_198_; lean_object* v_r_199_; 
v_res_198_ = l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0___redArg(v_xs_195_, v_ys_196_, v_x_197_);
lean_dec_ref(v_ys_196_);
lean_dec_ref(v_xs_195_);
v_r_199_ = lean_box(v_res_198_);
return v_r_199_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___redArg___boxed(lean_object* v_xs_200_, lean_object* v_ys_201_, lean_object* v_x_202_){
_start:
{
uint8_t v_res_203_; lean_object* v_r_204_; 
v_res_203_ = l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___redArg(v_xs_200_, v_ys_201_, v_x_202_);
lean_dec_ref(v_ys_201_);
lean_dec_ref(v_xs_200_);
v_r_204_ = lean_box(v_res_203_);
return v_r_204_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instBEqValue_beq___boxed(lean_object* v_x_205_, lean_object* v_x_206_){
_start:
{
uint8_t v_res_207_; lean_object* v_r_208_; 
v_res_207_ = l_Lake_Toml_instBEqValue_beq(v_x_205_, v_x_206_);
v_r_208_ = lean_box(v_res_207_);
return v_r_208_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0(lean_object* v_xs_209_, lean_object* v_ys_210_, lean_object* v_hsz_211_, lean_object* v_x_212_, lean_object* v_x_213_){
_start:
{
uint8_t v___x_214_; 
v___x_214_ = l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0___redArg(v_xs_209_, v_ys_210_, v_x_212_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0___boxed(lean_object* v_xs_215_, lean_object* v_ys_216_, lean_object* v_hsz_217_, lean_object* v_x_218_, lean_object* v_x_219_){
_start:
{
uint8_t v_res_220_; lean_object* v_r_221_; 
v_res_220_ = l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0(v_xs_215_, v_ys_216_, v_hsz_217_, v_x_218_, v_x_219_);
lean_dec_ref(v_ys_216_);
lean_dec_ref(v_xs_215_);
v_r_221_ = lean_box(v_res_220_);
return v_r_221_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1(lean_object* v_cmp_222_, lean_object* v_self_223_, lean_object* v_other_224_){
_start:
{
uint8_t v___x_225_; 
v___x_225_ = l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1___redArg(v_self_223_, v_other_224_);
return v___x_225_;
}
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
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1(lean_object* v_xs_231_, lean_object* v_ys_232_, lean_object* v_hsz_233_, lean_object* v_x_234_, lean_object* v_x_235_){
_start:
{
uint8_t v___x_236_; 
v___x_236_ = l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___redArg(v_xs_231_, v_ys_232_, v_x_234_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___boxed(lean_object* v_xs_237_, lean_object* v_ys_238_, lean_object* v_hsz_239_, lean_object* v_x_240_, lean_object* v_x_241_){
_start:
{
uint8_t v_res_242_; lean_object* v_r_243_; 
v_res_242_ = l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1(v_xs_237_, v_ys_238_, v_hsz_239_, v_x_240_, v_x_241_);
lean_dec_ref(v_ys_238_);
lean_dec_ref(v_xs_237_);
v_r_243_ = lean_box(v_res_242_);
return v_r_243_;
}
}
static lean_object* _init_l_Lake_Toml_Table_empty___closed__0(void){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l_Lake_Toml_RBDict_empty___redArg();
return v___x_246_;
}
}
static lean_object* _init_l_Lake_Toml_Table_empty(void){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = lean_obj_once(&l_Lake_Toml_Table_empty___closed__0, &l_Lake_Toml_Table_empty___closed__0_once, _init_l_Lake_Toml_Table_empty___closed__0);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_mkEmpty(lean_object* v_capacity_248_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l_Lake_Toml_RBDict_mkEmpty___redArg(v_capacity_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_mkEmpty___boxed(lean_object* v_capacity_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lake_Toml_Table_mkEmpty(v_capacity_250_);
lean_dec(v_capacity_250_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_table(lean_object* v_ref_252_, lean_object* v_t_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_254_, 0, v_ref_252_);
lean_ctor_set(v___x_254_, 1, v_t_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_ref(lean_object* v_x_255_){
_start:
{
lean_object* v_ref_256_; 
v_ref_256_ = lean_ctor_get(v_x_255_, 0);
lean_inc(v_ref_256_);
return v_ref_256_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_ref___boxed(lean_object* v_x_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lake_Toml_Value_ref(v_x_257_);
lean_dec_ref(v_x_257_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg(lean_object* v___x_267_, lean_object* v_s_268_, lean_object* v_a_269_, lean_object* v_b_270_){
_start:
{
uint8_t v_decide_271_; 
v_decide_271_ = lean_nat_dec_eq(v_a_269_, v___x_267_);
if (v_decide_271_ == 0)
{
uint32_t v___x_272_; lean_object* v___x_273_; uint32_t v___x_286_; uint8_t v___x_287_; 
v___x_272_ = lean_string_utf8_get_fast(v_s_268_, v_a_269_);
v___x_273_ = lean_string_utf8_next_fast(v_s_268_, v_a_269_);
lean_dec(v_a_269_);
v___x_286_ = 8;
v___x_287_ = lean_uint32_dec_eq(v___x_272_, v___x_286_);
if (v___x_287_ == 0)
{
uint32_t v___x_288_; uint8_t v___x_289_; 
v___x_288_ = 9;
v___x_289_ = lean_uint32_dec_eq(v___x_272_, v___x_288_);
if (v___x_289_ == 0)
{
uint32_t v___x_290_; uint8_t v___x_291_; 
v___x_290_ = 10;
v___x_291_ = lean_uint32_dec_eq(v___x_272_, v___x_290_);
if (v___x_291_ == 0)
{
uint32_t v___x_292_; uint8_t v___x_293_; 
v___x_292_ = 12;
v___x_293_ = lean_uint32_dec_eq(v___x_272_, v___x_292_);
if (v___x_293_ == 0)
{
uint32_t v___x_294_; uint8_t v___x_295_; 
v___x_294_ = 13;
v___x_295_ = lean_uint32_dec_eq(v___x_272_, v___x_294_);
if (v___x_295_ == 0)
{
uint32_t v___x_296_; uint8_t v___x_297_; 
v___x_296_ = 34;
v___x_297_ = lean_uint32_dec_eq(v___x_272_, v___x_296_);
if (v___x_297_ == 0)
{
uint32_t v___x_298_; uint8_t v___x_299_; 
v___x_298_ = 92;
v___x_299_ = lean_uint32_dec_eq(v___x_272_, v___x_298_);
if (v___x_299_ == 0)
{
uint32_t v___x_300_; uint8_t v___x_301_; 
v___x_300_ = 32;
v___x_301_ = lean_uint32_dec_lt(v___x_272_, v___x_300_);
if (v___x_301_ == 0)
{
uint32_t v___x_302_; uint8_t v___x_303_; 
v___x_302_ = 127;
v___x_303_ = lean_uint32_dec_eq(v___x_272_, v___x_302_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; 
v___x_304_ = lean_string_push(v_b_270_, v___x_272_);
v_a_269_ = v___x_273_;
v_b_270_ = v___x_304_;
goto _start;
}
else
{
goto v___jp_274_;
}
}
else
{
goto v___jp_274_;
}
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__1));
v___x_307_ = lean_string_append(v_b_270_, v___x_306_);
v_a_269_ = v___x_273_;
v_b_270_ = v___x_307_;
goto _start;
}
}
else
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__2));
v___x_310_ = lean_string_append(v_b_270_, v___x_309_);
v_a_269_ = v___x_273_;
v_b_270_ = v___x_310_;
goto _start;
}
}
else
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__3));
v___x_313_ = lean_string_append(v_b_270_, v___x_312_);
v_a_269_ = v___x_273_;
v_b_270_ = v___x_313_;
goto _start;
}
}
else
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__4));
v___x_316_ = lean_string_append(v_b_270_, v___x_315_);
v_a_269_ = v___x_273_;
v_b_270_ = v___x_316_;
goto _start;
}
}
else
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__5));
v___x_319_ = lean_string_append(v_b_270_, v___x_318_);
v_a_269_ = v___x_273_;
v_b_270_ = v___x_319_;
goto _start;
}
}
else
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__6));
v___x_322_ = lean_string_append(v_b_270_, v___x_321_);
v_a_269_ = v___x_273_;
v_b_270_ = v___x_322_;
goto _start;
}
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__7));
v___x_325_ = lean_string_append(v_b_270_, v___x_324_);
v_a_269_ = v___x_273_;
v_b_270_ = v___x_325_;
goto _start;
}
v___jp_274_:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; uint32_t v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_275_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__0));
v___x_276_ = lean_string_append(v_b_270_, v___x_275_);
v___x_277_ = lean_unsigned_to_nat(16u);
v___x_278_ = lean_uint32_to_nat(v___x_272_);
v___x_279_ = l_Nat_toDigits(v___x_277_, v___x_278_);
v___x_280_ = lean_string_mk(v___x_279_);
v___x_281_ = 48;
v___x_282_ = lean_unsigned_to_nat(4u);
v___x_283_ = l_Lake_lpadAscii(v___x_280_, v___x_281_, v___x_282_);
lean_dec_ref(v___x_280_);
v___x_284_ = lean_string_append(v___x_276_, v___x_283_);
lean_dec_ref(v___x_283_);
v_a_269_ = v___x_273_;
v_b_270_ = v___x_284_;
goto _start;
}
}
else
{
lean_dec(v_a_269_);
return v_b_270_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___boxed(lean_object* v___x_327_, lean_object* v_s_328_, lean_object* v_a_329_, lean_object* v_b_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg(v___x_327_, v_s_328_, v_a_329_, v_b_330_);
lean_dec_ref(v_s_328_);
lean_dec(v___x_327_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppString(lean_object* v_s_333_){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v_s_337_; uint32_t v___x_338_; lean_object* v___x_339_; 
v___x_334_ = ((lean_object*)(l_Lake_Toml_ppString___closed__0));
v___x_335_ = lean_string_utf8_byte_size(v_s_333_);
v___x_336_ = lean_unsigned_to_nat(0u);
v_s_337_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg(v___x_335_, v_s_333_, v___x_336_, v___x_334_);
v___x_338_ = 34;
v___x_339_ = lean_string_push(v_s_337_, v___x_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppString___boxed(lean_object* v_s_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lake_Toml_ppString(v_s_340_);
lean_dec_ref(v_s_340_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0(lean_object* v___x_342_, lean_object* v___x_343_, lean_object* v_s_344_, lean_object* v_inst_345_, lean_object* v_R_346_, lean_object* v_a_347_, lean_object* v_b_348_, lean_object* v_c_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg(v___x_343_, v_s_344_, v_a_347_, v_b_348_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___boxed(lean_object* v___x_351_, lean_object* v___x_352_, lean_object* v_s_353_, lean_object* v_inst_354_, lean_object* v_R_355_, lean_object* v_a_356_, lean_object* v_b_357_, lean_object* v_c_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0(v___x_351_, v___x_352_, v_s_353_, v_inst_354_, v_R_355_, v_a_356_, v_b_357_, v_c_358_);
lean_dec_ref(v_s_353_);
lean_dec(v___x_352_);
lean_dec_ref(v___x_351_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lake_Toml_ppSimpleKey_spec__0(lean_object* v_s_360_, lean_object* v_pos_361_){
_start:
{
lean_object* v_str_362_; lean_object* v_startInclusive_363_; lean_object* v_endExclusive_364_; lean_object* v___x_365_; lean_object* v___x_374_; lean_object* v___x_375_; uint8_t v_decide_376_; 
v_str_362_ = lean_ctor_get(v_s_360_, 0);
v_startInclusive_363_ = lean_ctor_get(v_s_360_, 1);
v_endExclusive_364_ = lean_ctor_get(v_s_360_, 2);
v___x_365_ = lean_nat_add(v_startInclusive_363_, v_pos_361_);
v___x_374_ = lean_unsigned_to_nat(0u);
v___x_375_ = lean_nat_sub(v_endExclusive_364_, v___x_365_);
v_decide_376_ = lean_nat_dec_eq(v___x_374_, v___x_375_);
lean_dec(v___x_375_);
if (v_decide_376_ == 0)
{
uint32_t v___x_377_; uint8_t v___y_389_; uint32_t v___x_394_; uint8_t v___x_395_; 
v___x_377_ = lean_string_utf8_get_fast(v_str_362_, v___x_365_);
v___x_394_ = 65;
v___x_395_ = lean_uint32_dec_le(v___x_394_, v___x_377_);
if (v___x_395_ == 0)
{
v___y_389_ = v___x_395_;
goto v___jp_388_;
}
else
{
uint32_t v___x_396_; uint8_t v___x_397_; 
v___x_396_ = 90;
v___x_397_ = lean_uint32_dec_le(v___x_377_, v___x_396_);
v___y_389_ = v___x_397_;
goto v___jp_388_;
}
v___jp_378_:
{
uint32_t v___x_379_; uint8_t v___x_380_; 
v___x_379_ = 95;
v___x_380_ = lean_uint32_dec_eq(v___x_377_, v___x_379_);
if (v___x_380_ == 0)
{
uint32_t v___x_381_; uint8_t v___x_382_; 
v___x_381_ = 45;
v___x_382_ = lean_uint32_dec_eq(v___x_377_, v___x_381_);
if (v___x_382_ == 0)
{
lean_dec(v___x_365_);
return v_pos_361_;
}
else
{
goto v___jp_366_;
}
}
else
{
goto v___jp_366_;
}
}
v___jp_383_:
{
uint32_t v___x_384_; uint8_t v___x_385_; 
v___x_384_ = 48;
v___x_385_ = lean_uint32_dec_le(v___x_384_, v___x_377_);
if (v___x_385_ == 0)
{
goto v___jp_378_;
}
else
{
uint32_t v___x_386_; uint8_t v___x_387_; 
v___x_386_ = 57;
v___x_387_ = lean_uint32_dec_le(v___x_377_, v___x_386_);
if (v___x_387_ == 0)
{
goto v___jp_378_;
}
else
{
goto v___jp_366_;
}
}
}
v___jp_388_:
{
if (v___y_389_ == 0)
{
uint32_t v___x_390_; uint8_t v___x_391_; 
v___x_390_ = 97;
v___x_391_ = lean_uint32_dec_le(v___x_390_, v___x_377_);
if (v___x_391_ == 0)
{
goto v___jp_383_;
}
else
{
uint32_t v___x_392_; uint8_t v___x_393_; 
v___x_392_ = 122;
v___x_393_ = lean_uint32_dec_le(v___x_377_, v___x_392_);
if (v___x_393_ == 0)
{
goto v___jp_383_;
}
else
{
goto v___jp_366_;
}
}
}
else
{
goto v___jp_366_;
}
}
}
else
{
lean_dec(v___x_365_);
return v_pos_361_;
}
v___jp_366_:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_367_ = lean_string_utf8_next_fast(v_str_362_, v___x_365_);
v___x_368_ = lean_nat_sub(v___x_367_, v___x_365_);
lean_dec(v___x_365_);
v___x_369_ = lean_nat_add(v_pos_361_, v___x_368_);
lean_dec(v___x_368_);
v___x_370_ = lean_unsigned_to_nat(1u);
v___x_371_ = lean_nat_add(v_pos_361_, v___x_370_);
v___x_372_ = lean_nat_dec_le(v___x_371_, v___x_369_);
lean_dec(v___x_371_);
if (v___x_372_ == 0)
{
lean_dec(v___x_369_);
return v_pos_361_;
}
else
{
lean_dec(v_pos_361_);
v_pos_361_ = v___x_369_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0(size_t v_sz_426_, size_t v_i_427_, lean_object* v_bs_428_){
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
LEAN_EXPORT lean_object* l_Lake_Toml_ppInlineTable(lean_object* v_t_446_){
_start:
{
lean_object* v_items_447_; size_t v_sz_448_; size_t v___x_449_; lean_object* v_xs_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v_items_447_ = lean_ctor_get(v_t_446_, 0);
lean_inc_ref(v_items_447_);
lean_dec_ref(v_t_446_);
v_sz_448_ = lean_array_size(v_items_447_);
v___x_449_ = ((size_t)0ULL);
v_xs_450_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0(v_sz_448_, v___x_449_, v_items_447_);
v___x_451_ = ((lean_object*)(l_Lake_Toml_ppInlineTable___closed__0));
v___x_452_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__1));
v___x_453_ = lean_array_to_list(v_xs_450_);
v___x_454_ = l_String_intercalate(v___x_452_, v___x_453_);
v___x_455_ = lean_string_append(v___x_451_, v___x_454_);
lean_dec_ref(v___x_454_);
v___x_456_ = ((lean_object*)(l_Lake_Toml_ppInlineTable___closed__1));
v___x_457_ = lean_string_append(v___x_455_, v___x_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_toString(lean_object* v_v_458_){
_start:
{
switch(lean_obj_tag(v_v_458_))
{
case 0:
{
lean_object* v_s_459_; lean_object* v___x_460_; 
v_s_459_ = lean_ctor_get(v_v_458_, 1);
lean_inc_ref(v_s_459_);
lean_dec_ref_known(v_v_458_, 2);
v___x_460_ = l_Lake_Toml_ppString(v_s_459_);
lean_dec_ref(v_s_459_);
return v___x_460_;
}
case 1:
{
lean_object* v_n_461_; lean_object* v___x_462_; 
v_n_461_ = lean_ctor_get(v_v_458_, 1);
lean_inc(v_n_461_);
lean_dec_ref_known(v_v_458_, 2);
v___x_462_ = l_Int_repr(v_n_461_);
lean_dec(v_n_461_);
return v___x_462_;
}
case 2:
{
double v_n_463_; lean_object* v___x_464_; 
v_n_463_ = lean_ctor_get_float(v_v_458_, sizeof(void*)*1);
lean_dec_ref_known(v_v_458_, 1);
v___x_464_ = lean_float_to_string(v_n_463_);
return v___x_464_;
}
case 3:
{
uint8_t v_b_465_; 
v_b_465_ = lean_ctor_get_uint8(v_v_458_, sizeof(void*)*1);
lean_dec_ref_known(v_v_458_, 1);
if (v_b_465_ == 0)
{
lean_object* v___x_466_; 
v___x_466_ = ((lean_object*)(l_Lake_Toml_Value_toString___closed__0));
return v___x_466_;
}
else
{
lean_object* v___x_467_; 
v___x_467_ = ((lean_object*)(l_Lake_Toml_Value_toString___closed__1));
return v___x_467_;
}
}
case 4:
{
lean_object* v_dt_468_; lean_object* v___x_469_; 
v_dt_468_ = lean_ctor_get(v_v_458_, 1);
lean_inc_ref(v_dt_468_);
lean_dec_ref_known(v_v_458_, 2);
v___x_469_ = l_Lake_Toml_DateTime_toString(v_dt_468_);
return v___x_469_;
}
case 5:
{
lean_object* v_xs_470_; lean_object* v___x_471_; 
v_xs_470_ = lean_ctor_get(v_v_458_, 1);
lean_inc_ref(v_xs_470_);
lean_dec_ref_known(v_v_458_, 2);
v___x_471_ = l_Lake_Toml_ppInlineArray(v_xs_470_);
return v___x_471_;
}
default: 
{
lean_object* v_xs_472_; lean_object* v___x_473_; 
v_xs_472_ = lean_ctor_get(v_v_458_, 1);
lean_inc_ref(v_xs_472_);
lean_dec_ref_known(v_v_458_, 2);
v___x_473_ = l_Lake_Toml_ppInlineTable(v_xs_472_);
return v___x_473_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3(size_t v_sz_474_, size_t v_i_475_, lean_object* v_bs_476_){
_start:
{
uint8_t v___x_477_; 
v___x_477_ = lean_usize_dec_lt(v_i_475_, v_sz_474_);
if (v___x_477_ == 0)
{
return v_bs_476_;
}
else
{
lean_object* v_v_478_; lean_object* v___x_479_; lean_object* v_bs_x27_480_; lean_object* v___x_481_; size_t v___x_482_; size_t v___x_483_; lean_object* v___x_484_; 
v_v_478_ = lean_array_uget(v_bs_476_, v_i_475_);
v___x_479_ = lean_unsigned_to_nat(0u);
v_bs_x27_480_ = lean_array_uset(v_bs_476_, v_i_475_, v___x_479_);
v___x_481_ = l_Lake_Toml_Value_toString(v_v_478_);
v___x_482_ = ((size_t)1ULL);
v___x_483_ = lean_usize_add(v_i_475_, v___x_482_);
v___x_484_ = lean_array_uset(v_bs_x27_480_, v_i_475_, v___x_481_);
v_i_475_ = v___x_483_;
v_bs_476_ = v___x_484_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppInlineArray(lean_object* v_vs_486_){
_start:
{
size_t v_sz_487_; size_t v___x_488_; lean_object* v_xs_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v_sz_487_ = lean_array_size(v_vs_486_);
v___x_488_ = ((size_t)0ULL);
v_xs_489_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3(v_sz_487_, v___x_488_, v_vs_486_);
v___x_490_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__0));
v___x_491_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__1));
v___x_492_ = lean_array_to_list(v_xs_489_);
v___x_493_ = l_String_intercalate(v___x_491_, v___x_492_);
v___x_494_ = lean_string_append(v___x_490_, v___x_493_);
lean_dec_ref(v___x_493_);
v___x_495_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__2));
v___x_496_ = lean_string_append(v___x_494_, v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3___boxed(lean_object* v_sz_497_, lean_object* v_i_498_, lean_object* v_bs_499_){
_start:
{
size_t v_sz_boxed_500_; size_t v_i_boxed_501_; lean_object* v_res_502_; 
v_sz_boxed_500_ = lean_unbox_usize(v_sz_497_);
lean_dec(v_sz_497_);
v_i_boxed_501_ = lean_unbox_usize(v_i_498_);
lean_dec(v_i_498_);
v_res_502_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3(v_sz_boxed_500_, v_i_boxed_501_, v_bs_499_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___boxed(lean_object* v_sz_503_, lean_object* v_i_504_, lean_object* v_bs_505_){
_start:
{
size_t v_sz_boxed_506_; size_t v_i_boxed_507_; lean_object* v_res_508_; 
v_sz_boxed_506_ = lean_unbox_usize(v_sz_503_);
lean_dec(v_sz_503_);
v_i_boxed_507_ = lean_unbox_usize(v_i_504_);
lean_dec(v_i_504_);
v_res_508_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0(v_sz_boxed_506_, v_i_boxed_507_, v_bs_505_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval(lean_object* v_s_512_, lean_object* v_k_513_, lean_object* v_v_514_){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_515_ = l_Lake_Toml_ppKey(v_k_513_);
v___x_516_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___closed__0));
v___x_517_ = lean_string_append(v___x_515_, v___x_516_);
v___x_518_ = l_Lake_Toml_Value_toString(v_v_514_);
v___x_519_ = lean_string_append(v___x_517_, v___x_518_);
lean_dec_ref(v___x_518_);
v___x_520_ = ((lean_object*)(l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval___closed__0));
v___x_521_ = lean_string_append(v___x_519_, v___x_520_);
v___x_522_ = lean_string_append(v_s_512_, v___x_521_);
lean_dec_ref(v___x_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lake_Toml_ppTable_spec__2(lean_object* v_msg_523_){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = ((lean_object*)(l_Lake_Toml_instInhabitedValue_default___closed__0));
v___x_525_ = lean_panic_fn_borrowed(v___x_524_, v_msg_523_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(lean_object* v_as_526_, size_t v_i_527_, size_t v_stop_528_, lean_object* v_b_529_){
_start:
{
uint8_t v___x_530_; 
v___x_530_ = lean_usize_dec_eq(v_i_527_, v_stop_528_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; lean_object* v_fst_532_; lean_object* v_snd_533_; lean_object* v___x_534_; size_t v___x_535_; size_t v___x_536_; 
v___x_531_ = lean_array_uget_borrowed(v_as_526_, v_i_527_);
v_fst_532_ = lean_ctor_get(v___x_531_, 0);
v_snd_533_ = lean_ctor_get(v___x_531_, 1);
lean_inc(v_snd_533_);
lean_inc(v_fst_532_);
v___x_534_ = l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval(v_b_529_, v_fst_532_, v_snd_533_);
v___x_535_ = ((size_t)1ULL);
v___x_536_ = lean_usize_add(v_i_527_, v___x_535_);
v_i_527_ = v___x_536_;
v_b_529_ = v___x_534_;
goto _start;
}
else
{
return v_b_529_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1___boxed(lean_object* v_as_538_, lean_object* v_i_539_, lean_object* v_stop_540_, lean_object* v_b_541_){
_start:
{
size_t v_i_boxed_542_; size_t v_stop_boxed_543_; lean_object* v_res_544_; 
v_i_boxed_542_ = lean_unbox_usize(v_i_539_);
lean_dec(v_i_539_);
v_stop_boxed_543_ = lean_unbox_usize(v_stop_540_);
lean_dec(v_stop_540_);
v_res_544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_as_538_, v_i_boxed_542_, v_stop_boxed_543_, v_b_541_);
lean_dec_ref(v_as_538_);
return v_res_544_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5(void){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_550_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__4));
v___x_551_ = lean_unsigned_to_nat(17u);
v___x_552_ = lean_unsigned_to_nat(128u);
v___x_553_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__3));
v___x_554_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__2));
v___x_555_ = l_mkPanicMessageWithDecl(v___x_554_, v___x_553_, v___x_552_, v___x_551_, v___x_550_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3(lean_object* v_fst_556_, lean_object* v_as_557_, size_t v_i_558_, size_t v_stop_559_, lean_object* v_b_560_){
_start:
{
lean_object* v___y_562_; lean_object* v___y_567_; uint8_t v___x_570_; 
v___x_570_ = lean_usize_dec_eq(v_i_558_, v_stop_559_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; 
v___x_571_ = lean_array_uget_borrowed(v_as_557_, v_i_558_);
if (lean_obj_tag(v___x_571_) == 6)
{
lean_object* v_xs_572_; lean_object* v_items_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v_s_580_; lean_object* v___x_581_; uint8_t v___x_582_; 
v_xs_572_ = lean_ctor_get(v___x_571_, 1);
v_items_573_ = lean_ctor_get(v_xs_572_, 0);
v___x_574_ = lean_unsigned_to_nat(0u);
v___x_575_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__0));
lean_inc(v_fst_556_);
v___x_576_ = l_Lake_Toml_ppKey(v_fst_556_);
v___x_577_ = lean_string_append(v___x_575_, v___x_576_);
lean_dec_ref(v___x_576_);
v___x_578_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__1));
v___x_579_ = lean_string_append(v___x_577_, v___x_578_);
v_s_580_ = lean_string_append(v_b_560_, v___x_579_);
lean_dec_ref(v___x_579_);
v___x_581_ = lean_array_get_size(v_items_573_);
v___x_582_ = lean_nat_dec_lt(v___x_574_, v___x_581_);
if (v___x_582_ == 0)
{
v___y_567_ = v_s_580_;
goto v___jp_566_;
}
else
{
uint8_t v___x_583_; 
v___x_583_ = lean_nat_dec_le(v___x_581_, v___x_581_);
if (v___x_583_ == 0)
{
if (v___x_582_ == 0)
{
v___y_567_ = v_s_580_;
goto v___jp_566_;
}
else
{
size_t v___x_584_; size_t v___x_585_; lean_object* v___x_586_; 
v___x_584_ = ((size_t)0ULL);
v___x_585_ = lean_usize_of_nat(v___x_581_);
v___x_586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_items_573_, v___x_584_, v___x_585_, v_s_580_);
v___y_567_ = v___x_586_;
goto v___jp_566_;
}
}
else
{
size_t v___x_587_; size_t v___x_588_; lean_object* v___x_589_; 
v___x_587_ = ((size_t)0ULL);
v___x_588_ = lean_usize_of_nat(v___x_581_);
v___x_589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_items_573_, v___x_587_, v___x_588_, v_s_580_);
v___y_567_ = v___x_589_;
goto v___jp_566_;
}
}
}
else
{
lean_object* v___x_590_; lean_object* v___x_591_; 
lean_dec_ref(v_b_560_);
v___x_590_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5);
v___x_591_ = l_panic___at___00Lake_Toml_ppTable_spec__2(v___x_590_);
v___y_562_ = v___x_591_;
goto v___jp_561_;
}
}
else
{
lean_dec(v_fst_556_);
return v_b_560_;
}
v___jp_561_:
{
size_t v___x_563_; size_t v___x_564_; 
v___x_563_ = ((size_t)1ULL);
v___x_564_ = lean_usize_add(v_i_558_, v___x_563_);
v_i_558_ = v___x_564_;
v_b_560_ = v___y_562_;
goto _start;
}
v___jp_566_:
{
uint32_t v___x_568_; lean_object* v___x_569_; 
v___x_568_ = 10;
v___x_569_ = lean_string_push(v___y_567_, v___x_568_);
v___y_562_ = v___x_569_;
goto v___jp_561_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___boxed(lean_object* v_fst_592_, lean_object* v_as_593_, lean_object* v_i_594_, lean_object* v_stop_595_, lean_object* v_b_596_){
_start:
{
size_t v_i_boxed_597_; size_t v_stop_boxed_598_; lean_object* v_res_599_; 
v_i_boxed_597_ = lean_unbox_usize(v_i_594_);
lean_dec(v_i_594_);
v_stop_boxed_598_ = lean_unbox_usize(v_stop_595_);
lean_dec(v_stop_595_);
v_res_599_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3(v_fst_592_, v_as_593_, v_i_boxed_597_, v_stop_boxed_598_, v_b_596_);
lean_dec_ref(v_as_593_);
return v_res_599_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Toml_ppTable_spec__4(lean_object* v___x_600_, lean_object* v_as_601_, size_t v_i_602_, size_t v_stop_603_){
_start:
{
uint8_t v___x_604_; 
v___x_604_ = lean_usize_dec_eq(v_i_602_, v_stop_603_);
if (v___x_604_ == 0)
{
uint8_t v___x_605_; lean_object* v___x_606_; 
v___x_605_ = 1;
v___x_606_ = lean_array_uget_borrowed(v_as_601_, v_i_602_);
if (lean_obj_tag(v___x_606_) == 6)
{
lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_607_ = lean_unsigned_to_nat(0u);
v___x_608_ = lean_nat_dec_eq(v___x_600_, v___x_607_);
if (v___x_608_ == 0)
{
size_t v___x_609_; size_t v___x_610_; 
v___x_609_ = ((size_t)1ULL);
v___x_610_ = lean_usize_add(v_i_602_, v___x_609_);
v_i_602_ = v___x_610_;
goto _start;
}
else
{
return v___x_605_;
}
}
else
{
return v___x_605_;
}
}
else
{
uint8_t v___x_612_; 
v___x_612_ = 0;
return v___x_612_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Toml_ppTable_spec__4___boxed(lean_object* v___x_613_, lean_object* v_as_614_, lean_object* v_i_615_, lean_object* v_stop_616_){
_start:
{
size_t v_i_boxed_617_; size_t v_stop_boxed_618_; uint8_t v_res_619_; lean_object* v_r_620_; 
v_i_boxed_617_ = lean_unbox_usize(v_i_615_);
lean_dec(v_i_615_);
v_stop_boxed_618_ = lean_unbox_usize(v_stop_616_);
lean_dec(v_stop_616_);
v_res_619_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Toml_ppTable_spec__4(v___x_613_, v_as_614_, v_i_boxed_617_, v_stop_boxed_618_);
lean_dec_ref(v_as_614_);
lean_dec(v___x_613_);
v_r_620_ = lean_box(v_res_619_);
return v_r_620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5(lean_object* v_as_623_, size_t v_i_624_, size_t v_stop_625_, lean_object* v_b_626_){
_start:
{
lean_object* v___y_628_; uint8_t v___x_632_; 
v___x_632_ = lean_usize_dec_eq(v_i_624_, v_stop_625_);
if (v___x_632_ == 0)
{
lean_object* v_fst_633_; lean_object* v_snd_634_; lean_object* v___y_636_; lean_object* v___x_640_; lean_object* v_snd_641_; 
v_fst_633_ = lean_ctor_get(v_b_626_, 0);
v_snd_634_ = lean_ctor_get(v_b_626_, 1);
v___x_640_ = lean_array_uget(v_as_623_, v_i_624_);
v_snd_641_ = lean_ctor_get(v___x_640_, 1);
switch(lean_obj_tag(v_snd_641_))
{
case 5:
{
lean_object* v_fst_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_699_; 
lean_inc_ref(v_snd_641_);
v_fst_642_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_699_ == 0)
{
lean_object* v_unused_700_; 
v_unused_700_ = lean_ctor_get(v___x_640_, 1);
lean_dec(v_unused_700_);
v___x_644_ = v___x_640_;
v_isShared_645_ = v_isSharedCheck_699_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_fst_642_);
lean_dec(v___x_640_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_699_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v_xs_646_; lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_664_; 
v_xs_646_ = lean_ctor_get(v_snd_641_, 1);
lean_inc_ref(v_xs_646_);
lean_dec_ref_known(v_snd_641_, 2);
v___x_647_ = lean_array_get_size(v_xs_646_);
v___x_648_ = lean_unsigned_to_nat(0u);
v___x_664_ = lean_nat_dec_eq(v___x_647_, v___x_648_);
if (v___x_664_ == 0)
{
uint8_t v___x_665_; 
v___x_665_ = lean_nat_dec_lt(v___x_648_, v___x_647_);
if (v___x_665_ == 0)
{
goto v___jp_649_;
}
else
{
if (v___x_665_ == 0)
{
goto v___jp_649_;
}
else
{
size_t v___x_666_; size_t v___x_667_; uint8_t v___x_668_; 
v___x_666_ = ((size_t)0ULL);
v___x_667_ = lean_usize_of_nat(v___x_647_);
v___x_668_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Toml_ppTable_spec__4(v___x_647_, v_xs_646_, v___x_666_, v___x_667_);
if (v___x_668_ == 0)
{
goto v___jp_649_;
}
else
{
lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_683_; 
lean_inc(v_snd_634_);
lean_inc(v_fst_633_);
lean_del_object(v___x_644_);
v_isSharedCheck_683_ = !lean_is_exclusive(v_b_626_);
if (v_isSharedCheck_683_ == 0)
{
lean_object* v_unused_684_; lean_object* v_unused_685_; 
v_unused_684_ = lean_ctor_get(v_b_626_, 1);
lean_dec(v_unused_684_);
v_unused_685_ = lean_ctor_get(v_b_626_, 0);
lean_dec(v_unused_685_);
v___x_670_ = v_b_626_;
v_isShared_671_ = v_isSharedCheck_683_;
goto v_resetjp_669_;
}
else
{
lean_dec(v_b_626_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_683_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_681_; 
v___x_672_ = l_Lake_Toml_ppKey(v_fst_642_);
v___x_673_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___closed__0));
v___x_674_ = lean_string_append(v___x_672_, v___x_673_);
v___x_675_ = l_Lake_Toml_ppInlineArray(v_xs_646_);
v___x_676_ = lean_string_append(v___x_674_, v___x_675_);
lean_dec_ref(v___x_675_);
v___x_677_ = ((lean_object*)(l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval___closed__0));
v___x_678_ = lean_string_append(v___x_676_, v___x_677_);
v___x_679_ = lean_string_append(v_fst_633_, v___x_678_);
lean_dec_ref(v___x_678_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_679_);
v___x_681_ = v___x_670_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_679_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_snd_634_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
v___y_628_ = v___x_681_;
goto v___jp_627_;
}
}
}
}
}
}
else
{
lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_696_; 
lean_inc(v_snd_634_);
lean_inc(v_fst_633_);
lean_dec_ref(v_xs_646_);
lean_del_object(v___x_644_);
v_isSharedCheck_696_ = !lean_is_exclusive(v_b_626_);
if (v_isSharedCheck_696_ == 0)
{
lean_object* v_unused_697_; lean_object* v_unused_698_; 
v_unused_697_ = lean_ctor_get(v_b_626_, 1);
lean_dec(v_unused_697_);
v_unused_698_ = lean_ctor_get(v_b_626_, 0);
lean_dec(v_unused_698_);
v___x_687_ = v_b_626_;
v_isShared_688_ = v_isSharedCheck_696_;
goto v_resetjp_686_;
}
else
{
lean_dec(v_b_626_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_696_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_694_; 
v___x_689_ = l_Lake_Toml_ppKey(v_fst_642_);
v___x_690_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___closed__0));
v___x_691_ = lean_string_append(v___x_689_, v___x_690_);
v___x_692_ = lean_string_append(v_fst_633_, v___x_691_);
lean_dec_ref(v___x_691_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v___x_692_);
v___x_694_ = v___x_687_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_692_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_snd_634_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
v___y_628_ = v___x_694_;
goto v___jp_627_;
}
}
}
v___jp_649_:
{
uint8_t v___x_650_; 
v___x_650_ = lean_nat_dec_lt(v___x_648_, v___x_647_);
if (v___x_650_ == 0)
{
lean_dec_ref(v_xs_646_);
lean_del_object(v___x_644_);
lean_dec(v_fst_642_);
v___y_628_ = v_b_626_;
goto v___jp_627_;
}
else
{
uint8_t v___x_651_; 
v___x_651_ = lean_nat_dec_le(v___x_647_, v___x_647_);
if (v___x_651_ == 0)
{
if (v___x_650_ == 0)
{
lean_dec_ref(v_xs_646_);
lean_del_object(v___x_644_);
lean_dec(v_fst_642_);
v___y_628_ = v_b_626_;
goto v___jp_627_;
}
else
{
size_t v___x_652_; size_t v___x_653_; lean_object* v___x_654_; lean_object* v___x_656_; 
lean_inc(v_snd_634_);
lean_inc(v_fst_633_);
lean_dec_ref(v_b_626_);
v___x_652_ = ((size_t)0ULL);
v___x_653_ = lean_usize_of_nat(v___x_647_);
v___x_654_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3(v_fst_642_, v_xs_646_, v___x_652_, v___x_653_, v_snd_634_);
lean_dec_ref(v_xs_646_);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 1, v___x_654_);
lean_ctor_set(v___x_644_, 0, v_fst_633_);
v___x_656_ = v___x_644_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_fst_633_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v___x_654_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
v___y_628_ = v___x_656_;
goto v___jp_627_;
}
}
}
else
{
size_t v___x_658_; size_t v___x_659_; lean_object* v___x_660_; lean_object* v___x_662_; 
lean_inc(v_snd_634_);
lean_inc(v_fst_633_);
lean_dec_ref(v_b_626_);
v___x_658_ = ((size_t)0ULL);
v___x_659_ = lean_usize_of_nat(v___x_647_);
v___x_660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3(v_fst_642_, v_xs_646_, v___x_658_, v___x_659_, v_snd_634_);
lean_dec_ref(v_xs_646_);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 1, v___x_660_);
lean_ctor_set(v___x_644_, 0, v_fst_633_);
v___x_662_ = v___x_644_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_fst_633_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v___x_660_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
v___y_628_ = v___x_662_;
goto v___jp_627_;
}
}
}
}
}
}
case 6:
{
lean_object* v_xs_701_; lean_object* v_fst_702_; lean_object* v_items_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v_fs_709_; lean_object* v___x_710_; lean_object* v___x_711_; uint8_t v___x_712_; 
lean_inc(v_snd_634_);
lean_inc(v_fst_633_);
lean_dec_ref(v_b_626_);
v_xs_701_ = lean_ctor_get(v_snd_641_, 1);
lean_inc_ref(v_xs_701_);
v_fst_702_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_fst_702_);
lean_dec(v___x_640_);
v_items_703_ = lean_ctor_get(v_xs_701_, 0);
lean_inc_ref(v_items_703_);
lean_dec_ref(v_xs_701_);
v___x_704_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__0));
v___x_705_ = l_Lake_Toml_ppKey(v_fst_702_);
v___x_706_ = lean_string_append(v___x_704_, v___x_705_);
lean_dec_ref(v___x_705_);
v___x_707_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___closed__1));
v___x_708_ = lean_string_append(v___x_706_, v___x_707_);
v_fs_709_ = lean_string_append(v_snd_634_, v___x_708_);
lean_dec_ref(v___x_708_);
v___x_710_ = lean_unsigned_to_nat(0u);
v___x_711_ = lean_array_get_size(v_items_703_);
v___x_712_ = lean_nat_dec_lt(v___x_710_, v___x_711_);
if (v___x_712_ == 0)
{
lean_dec_ref(v_items_703_);
v___y_636_ = v_fs_709_;
goto v___jp_635_;
}
else
{
uint8_t v___x_713_; 
v___x_713_ = lean_nat_dec_le(v___x_711_, v___x_711_);
if (v___x_713_ == 0)
{
if (v___x_712_ == 0)
{
lean_dec_ref(v_items_703_);
v___y_636_ = v_fs_709_;
goto v___jp_635_;
}
else
{
size_t v___x_714_; size_t v___x_715_; lean_object* v___x_716_; 
v___x_714_ = ((size_t)0ULL);
v___x_715_ = lean_usize_of_nat(v___x_711_);
v___x_716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_items_703_, v___x_714_, v___x_715_, v_fs_709_);
lean_dec_ref(v_items_703_);
v___y_636_ = v___x_716_;
goto v___jp_635_;
}
}
else
{
size_t v___x_717_; size_t v___x_718_; lean_object* v___x_719_; 
v___x_717_ = ((size_t)0ULL);
v___x_718_ = lean_usize_of_nat(v___x_711_);
v___x_719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_items_703_, v___x_717_, v___x_718_, v_fs_709_);
lean_dec_ref(v_items_703_);
v___y_636_ = v___x_719_;
goto v___jp_635_;
}
}
}
default: 
{
lean_object* v_fst_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_728_; 
lean_inc(v_snd_641_);
lean_inc(v_snd_634_);
lean_inc(v_fst_633_);
lean_dec_ref(v_b_626_);
v_fst_720_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_728_ == 0)
{
lean_object* v_unused_729_; 
v_unused_729_ = lean_ctor_get(v___x_640_, 1);
lean_dec(v_unused_729_);
v___x_722_ = v___x_640_;
v_isShared_723_ = v_isSharedCheck_728_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_fst_720_);
lean_dec(v___x_640_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_728_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_724_; lean_object* v___x_726_; 
v___x_724_ = l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval(v_fst_633_, v_fst_720_, v_snd_641_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 1, v_snd_634_);
lean_ctor_set(v___x_722_, 0, v___x_724_);
v___x_726_ = v___x_722_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v_snd_634_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
v___y_628_ = v___x_726_;
goto v___jp_627_;
}
}
}
}
v___jp_635_:
{
uint32_t v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_637_ = 10;
v___x_638_ = lean_string_push(v___y_636_, v___x_637_);
v___x_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_639_, 0, v_fst_633_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
v___y_628_ = v___x_639_;
goto v___jp_627_;
}
}
else
{
return v_b_626_;
}
v___jp_627_:
{
size_t v___x_629_; size_t v___x_630_; 
v___x_629_ = ((size_t)1ULL);
v___x_630_ = lean_usize_add(v_i_624_, v___x_629_);
v_i_624_ = v___x_630_;
v_b_626_ = v___y_628_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___boxed(lean_object* v_as_730_, lean_object* v_i_731_, lean_object* v_stop_732_, lean_object* v_b_733_){
_start:
{
size_t v_i_boxed_734_; size_t v_stop_boxed_735_; lean_object* v_res_736_; 
v_i_boxed_734_ = lean_unbox_usize(v_i_731_);
lean_dec(v_i_731_);
v_stop_boxed_735_ = lean_unbox_usize(v_stop_732_);
lean_dec(v_stop_732_);
v_res_736_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5(v_as_730_, v_i_boxed_734_, v_stop_boxed_735_, v_b_733_);
lean_dec_ref(v_as_730_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lake_Toml_ppTable_spec__0(lean_object* v_s_737_, lean_object* v_pos_738_){
_start:
{
lean_object* v_str_739_; lean_object* v_startInclusive_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v_decide_744_; 
v_str_739_ = lean_ctor_get(v_s_737_, 0);
v_startInclusive_740_ = lean_ctor_get(v_s_737_, 1);
v___x_741_ = lean_nat_add(v_startInclusive_740_, v_pos_738_);
v___x_742_ = lean_nat_sub(v___x_741_, v_startInclusive_740_);
v___x_743_ = lean_unsigned_to_nat(0u);
v_decide_744_ = lean_nat_dec_eq(v___x_742_, v___x_743_);
if (v_decide_744_ == 0)
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_753_; uint32_t v___x_754_; uint32_t v___x_755_; uint8_t v___x_756_; 
lean_inc(v_startInclusive_740_);
lean_inc_ref(v_str_739_);
v___x_745_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_745_, 0, v_str_739_);
lean_ctor_set(v___x_745_, 1, v_startInclusive_740_);
lean_ctor_set(v___x_745_, 2, v___x_741_);
v___x_746_ = lean_unsigned_to_nat(1u);
v___x_747_ = lean_nat_sub(v___x_742_, v___x_746_);
lean_dec(v___x_742_);
v___x_748_ = l_String_Slice_posLE(v___x_745_, v___x_747_);
lean_dec_ref_known(v___x_745_, 3);
v___x_753_ = lean_nat_add(v_startInclusive_740_, v___x_748_);
v___x_754_ = lean_string_utf8_get_fast(v_str_739_, v___x_753_);
lean_dec(v___x_753_);
v___x_755_ = 32;
v___x_756_ = lean_uint32_dec_eq(v___x_754_, v___x_755_);
if (v___x_756_ == 0)
{
uint32_t v___x_757_; uint8_t v___x_758_; 
v___x_757_ = 9;
v___x_758_ = lean_uint32_dec_eq(v___x_754_, v___x_757_);
if (v___x_758_ == 0)
{
uint32_t v___x_759_; uint8_t v___x_760_; 
v___x_759_ = 13;
v___x_760_ = lean_uint32_dec_eq(v___x_754_, v___x_759_);
if (v___x_760_ == 0)
{
uint32_t v___x_761_; uint8_t v___x_762_; 
v___x_761_ = 10;
v___x_762_ = lean_uint32_dec_eq(v___x_754_, v___x_761_);
if (v___x_762_ == 0)
{
lean_dec(v___x_748_);
return v_pos_738_;
}
else
{
goto v___jp_749_;
}
}
else
{
goto v___jp_749_;
}
}
else
{
goto v___jp_749_;
}
}
else
{
goto v___jp_749_;
}
v___jp_749_:
{
lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_750_ = lean_nat_add(v___x_748_, v___x_746_);
v___x_751_ = lean_nat_dec_le(v___x_750_, v_pos_738_);
lean_dec(v___x_750_);
if (v___x_751_ == 0)
{
lean_dec(v___x_748_);
return v_pos_738_;
}
else
{
lean_dec(v_pos_738_);
v_pos_738_ = v___x_748_;
goto _start;
}
}
}
else
{
lean_dec(v___x_742_);
lean_dec(v___x_741_);
return v_pos_738_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lake_Toml_ppTable_spec__0___boxed(lean_object* v_s_763_, lean_object* v_pos_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_String_Slice_Pos_revSkipWhile___at___00Lake_Toml_ppTable_spec__0(v_s_763_, v_pos_764_);
lean_dec_ref(v_s_763_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppTable(lean_object* v_t_768_){
_start:
{
lean_object* v_fst_770_; lean_object* v_snd_771_; lean_object* v___y_782_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v_items_787_; lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_785_ = ((lean_object*)(l_Lake_Toml_instInhabitedValue_default___closed__0));
v___x_786_ = ((lean_object*)(l_Lake_Toml_ppTable___closed__0));
v_items_787_ = lean_ctor_get(v_t_768_, 0);
v___x_788_ = lean_unsigned_to_nat(0u);
v___x_789_ = lean_array_get_size(v_items_787_);
v___x_790_ = lean_nat_dec_lt(v___x_788_, v___x_789_);
if (v___x_790_ == 0)
{
v_fst_770_ = v___x_785_;
v_snd_771_ = v___x_785_;
goto v___jp_769_;
}
else
{
uint8_t v___x_791_; 
v___x_791_ = lean_nat_dec_le(v___x_789_, v___x_789_);
if (v___x_791_ == 0)
{
if (v___x_790_ == 0)
{
v_fst_770_ = v___x_785_;
v_snd_771_ = v___x_785_;
goto v___jp_769_;
}
else
{
size_t v___x_792_; size_t v___x_793_; lean_object* v___x_794_; 
v___x_792_ = ((size_t)0ULL);
v___x_793_ = lean_usize_of_nat(v___x_789_);
v___x_794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5(v_items_787_, v___x_792_, v___x_793_, v___x_786_);
v___y_782_ = v___x_794_;
goto v___jp_781_;
}
}
else
{
size_t v___x_795_; size_t v___x_796_; lean_object* v___x_797_; 
v___x_795_ = ((size_t)0ULL);
v___x_796_ = lean_usize_of_nat(v___x_789_);
v___x_797_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5(v_items_787_, v___x_795_, v___x_796_, v___x_786_);
v___y_782_ = v___x_797_;
goto v___jp_781_;
}
}
v___jp_769_:
{
uint32_t v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_772_ = 10;
v___x_773_ = lean_string_push(v_fst_770_, v___x_772_);
v___x_774_ = lean_string_append(v___x_773_, v_snd_771_);
lean_dec_ref(v_snd_771_);
v___x_775_ = lean_unsigned_to_nat(0u);
v___x_776_ = lean_string_utf8_byte_size(v___x_774_);
lean_inc_ref(v___x_774_);
v___x_777_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_777_, 0, v___x_774_);
lean_ctor_set(v___x_777_, 1, v___x_775_);
lean_ctor_set(v___x_777_, 2, v___x_776_);
v___x_778_ = l_String_Slice_Pos_revSkipWhile___at___00Lake_Toml_ppTable_spec__0(v___x_777_, v___x_776_);
lean_dec_ref_known(v___x_777_, 3);
v___x_779_ = lean_string_utf8_extract_fast(v___x_774_, v___x_775_, v___x_778_);
lean_dec(v___x_778_);
lean_dec_ref(v___x_774_);
v___x_780_ = lean_string_push(v___x_779_, v___x_772_);
return v___x_780_;
}
v___jp_781_:
{
lean_object* v_fst_783_; lean_object* v_snd_784_; 
v_fst_783_ = lean_ctor_get(v___y_782_, 0);
lean_inc(v_fst_783_);
v_snd_784_ = lean_ctor_get(v___y_782_, 1);
lean_inc(v_snd_784_);
lean_dec_ref(v___y_782_);
v_fst_770_ = v_fst_783_;
v_snd_771_ = v_snd_784_;
goto v___jp_769_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppTable___boxed(lean_object* v_t_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lake_Toml_ppTable(v_t_798_);
lean_dec_ref(v_t_798_);
return v_res_799_;
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

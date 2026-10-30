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
lean_object* v_one_164_; lean_object* v_n_165_; lean_object* v___x_166_; lean_object* v_fst_167_; lean_object* v_snd_168_; lean_object* v___x_169_; lean_object* v_fst_170_; lean_object* v_snd_171_; uint8_t v___x_172_; 
v_one_164_ = lean_unsigned_to_nat(1u);
v_n_165_ = lean_nat_sub(v_x_161_, v_one_164_);
lean_dec(v_x_161_);
v___x_166_ = lean_array_fget_borrowed(v_xs_159_, v_n_165_);
v_fst_167_ = lean_ctor_get(v___x_166_, 0);
v_snd_168_ = lean_ctor_get(v___x_166_, 1);
v___x_169_ = lean_array_fget_borrowed(v_ys_160_, v_n_165_);
v_fst_170_ = lean_ctor_get(v___x_169_, 0);
v_snd_171_ = lean_ctor_get(v___x_169_, 1);
v___x_172_ = lean_name_eq(v_fst_167_, v_fst_170_);
if (v___x_172_ == 0)
{
lean_dec(v_n_165_);
return v___x_172_;
}
else
{
uint8_t v___x_173_; 
lean_inc(v_snd_171_);
lean_inc(v_snd_168_);
v___x_173_ = l_Lake_Toml_instBEqValue_beq(v_snd_168_, v_snd_171_);
if (v___x_173_ == 0)
{
lean_dec(v_n_165_);
return v___x_173_;
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
LEAN_EXPORT uint8_t l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1___redArg(lean_object* v_self_175_, lean_object* v_other_176_){
_start:
{
lean_object* v_items_177_; lean_object* v_items_178_; lean_object* v___x_179_; lean_object* v___x_180_; uint8_t v___x_181_; 
v_items_177_ = lean_ctor_get(v_self_175_, 0);
v_items_178_ = lean_ctor_get(v_other_176_, 0);
v___x_179_ = lean_array_get_size(v_items_177_);
v___x_180_ = lean_array_get_size(v_items_178_);
v___x_181_ = lean_nat_dec_eq(v___x_179_, v___x_180_);
if (v___x_181_ == 0)
{
return v___x_181_;
}
else
{
uint8_t v___x_182_; 
v___x_182_ = l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___redArg(v_items_177_, v_items_178_, v___x_179_);
return v___x_182_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1___redArg___boxed(lean_object* v_self_183_, lean_object* v_other_184_){
_start:
{
uint8_t v_res_185_; lean_object* v_r_186_; 
v_res_185_ = l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1___redArg(v_self_183_, v_other_184_);
lean_dec_ref(v_other_184_);
lean_dec_ref(v_self_183_);
v_r_186_ = lean_box(v_res_185_);
return v_r_186_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0___redArg___boxed(lean_object* v_xs_187_, lean_object* v_ys_188_, lean_object* v_x_189_){
_start:
{
uint8_t v_res_190_; lean_object* v_r_191_; 
v_res_190_ = l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0___redArg(v_xs_187_, v_ys_188_, v_x_189_);
lean_dec_ref(v_ys_188_);
lean_dec_ref(v_xs_187_);
v_r_191_ = lean_box(v_res_190_);
return v_r_191_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___redArg___boxed(lean_object* v_xs_192_, lean_object* v_ys_193_, lean_object* v_x_194_){
_start:
{
uint8_t v_res_195_; lean_object* v_r_196_; 
v_res_195_ = l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___redArg(v_xs_192_, v_ys_193_, v_x_194_);
lean_dec_ref(v_ys_193_);
lean_dec_ref(v_xs_192_);
v_r_196_ = lean_box(v_res_195_);
return v_r_196_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instBEqValue_beq___boxed(lean_object* v_x_197_, lean_object* v_x_198_){
_start:
{
uint8_t v_res_199_; lean_object* v_r_200_; 
v_res_199_ = l_Lake_Toml_instBEqValue_beq(v_x_197_, v_x_198_);
v_r_200_ = lean_box(v_res_199_);
return v_r_200_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0(lean_object* v_xs_201_, lean_object* v_ys_202_, lean_object* v_hsz_203_, lean_object* v_x_204_, lean_object* v_x_205_){
_start:
{
uint8_t v___x_206_; 
v___x_206_ = l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0___redArg(v_xs_201_, v_ys_202_, v_x_204_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0___boxed(lean_object* v_xs_207_, lean_object* v_ys_208_, lean_object* v_hsz_209_, lean_object* v_x_210_, lean_object* v_x_211_){
_start:
{
uint8_t v_res_212_; lean_object* v_r_213_; 
v_res_212_ = l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0(v_xs_207_, v_ys_208_, v_hsz_209_, v_x_210_, v_x_211_);
lean_dec_ref(v_ys_208_);
lean_dec_ref(v_xs_207_);
v_r_213_ = lean_box(v_res_212_);
return v_r_213_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1(lean_object* v_cmp_214_, lean_object* v_self_215_, lean_object* v_other_216_){
_start:
{
uint8_t v___x_217_; 
v___x_217_ = l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1___redArg(v_self_215_, v_other_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1___boxed(lean_object* v_cmp_218_, lean_object* v_self_219_, lean_object* v_other_220_){
_start:
{
uint8_t v_res_221_; lean_object* v_r_222_; 
v_res_221_ = l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1(v_cmp_218_, v_self_219_, v_other_220_);
lean_dec_ref(v_other_220_);
lean_dec_ref(v_self_219_);
lean_dec_ref(v_cmp_218_);
v_r_222_ = lean_box(v_res_221_);
return v_r_222_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1(lean_object* v_xs_223_, lean_object* v_ys_224_, lean_object* v_hsz_225_, lean_object* v_x_226_, lean_object* v_x_227_){
_start:
{
uint8_t v___x_228_; 
v___x_228_ = l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___redArg(v_xs_223_, v_ys_224_, v_x_226_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___boxed(lean_object* v_xs_229_, lean_object* v_ys_230_, lean_object* v_hsz_231_, lean_object* v_x_232_, lean_object* v_x_233_){
_start:
{
uint8_t v_res_234_; lean_object* v_r_235_; 
v_res_234_ = l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1(v_xs_229_, v_ys_230_, v_hsz_231_, v_x_232_, v_x_233_);
lean_dec_ref(v_ys_230_);
lean_dec_ref(v_xs_229_);
v_r_235_ = lean_box(v_res_234_);
return v_r_235_;
}
}
static lean_object* _init_l_Lake_Toml_Table_empty___closed__0(void){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_Lake_Toml_RBDict_empty___redArg();
return v___x_238_;
}
}
static lean_object* _init_l_Lake_Toml_Table_empty(void){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = lean_obj_once(&l_Lake_Toml_Table_empty___closed__0, &l_Lake_Toml_Table_empty___closed__0_once, _init_l_Lake_Toml_Table_empty___closed__0);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_mkEmpty(lean_object* v_capacity_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_Lake_Toml_RBDict_mkEmpty___redArg(v_capacity_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_mkEmpty___boxed(lean_object* v_capacity_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lake_Toml_Table_mkEmpty(v_capacity_242_);
lean_dec(v_capacity_242_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_table(lean_object* v_ref_244_, lean_object* v_t_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_246_, 0, v_ref_244_);
lean_ctor_set(v___x_246_, 1, v_t_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_ref(lean_object* v_x_247_){
_start:
{
lean_object* v_ref_248_; 
v_ref_248_ = lean_ctor_get(v_x_247_, 0);
lean_inc(v_ref_248_);
return v_ref_248_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_ref___boxed(lean_object* v_x_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lake_Toml_Value_ref(v_x_249_);
lean_dec_ref(v_x_249_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg(lean_object* v___x_259_, lean_object* v_s_260_, lean_object* v_a_261_, lean_object* v_b_262_){
_start:
{
uint8_t v_decide_263_; 
v_decide_263_ = lean_nat_dec_eq(v_a_261_, v___x_259_);
if (v_decide_263_ == 0)
{
uint32_t v___x_264_; lean_object* v___x_265_; uint32_t v___x_278_; uint8_t v___x_279_; 
v___x_264_ = lean_string_utf8_get_fast(v_s_260_, v_a_261_);
v___x_265_ = lean_string_utf8_next_fast(v_s_260_, v_a_261_);
lean_dec(v_a_261_);
v___x_278_ = 8;
v___x_279_ = lean_uint32_dec_eq(v___x_264_, v___x_278_);
if (v___x_279_ == 0)
{
uint32_t v___x_280_; uint8_t v___x_281_; 
v___x_280_ = 9;
v___x_281_ = lean_uint32_dec_eq(v___x_264_, v___x_280_);
if (v___x_281_ == 0)
{
uint32_t v___x_282_; uint8_t v___x_283_; 
v___x_282_ = 10;
v___x_283_ = lean_uint32_dec_eq(v___x_264_, v___x_282_);
if (v___x_283_ == 0)
{
uint32_t v___x_284_; uint8_t v___x_285_; 
v___x_284_ = 12;
v___x_285_ = lean_uint32_dec_eq(v___x_264_, v___x_284_);
if (v___x_285_ == 0)
{
uint32_t v___x_286_; uint8_t v___x_287_; 
v___x_286_ = 13;
v___x_287_ = lean_uint32_dec_eq(v___x_264_, v___x_286_);
if (v___x_287_ == 0)
{
uint32_t v___x_288_; uint8_t v___x_289_; 
v___x_288_ = 34;
v___x_289_ = lean_uint32_dec_eq(v___x_264_, v___x_288_);
if (v___x_289_ == 0)
{
uint32_t v___x_290_; uint8_t v___x_291_; 
v___x_290_ = 92;
v___x_291_ = lean_uint32_dec_eq(v___x_264_, v___x_290_);
if (v___x_291_ == 0)
{
uint32_t v___x_292_; uint8_t v___x_293_; 
v___x_292_ = 32;
v___x_293_ = lean_uint32_dec_lt(v___x_264_, v___x_292_);
if (v___x_293_ == 0)
{
uint32_t v___x_294_; uint8_t v___x_295_; 
v___x_294_ = 127;
v___x_295_ = lean_uint32_dec_eq(v___x_264_, v___x_294_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; 
v___x_296_ = lean_string_push(v_b_262_, v___x_264_);
v_a_261_ = v___x_265_;
v_b_262_ = v___x_296_;
goto _start;
}
else
{
goto v___jp_266_;
}
}
else
{
goto v___jp_266_;
}
}
else
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__1));
v___x_299_ = lean_string_append(v_b_262_, v___x_298_);
v_a_261_ = v___x_265_;
v_b_262_ = v___x_299_;
goto _start;
}
}
else
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__2));
v___x_302_ = lean_string_append(v_b_262_, v___x_301_);
v_a_261_ = v___x_265_;
v_b_262_ = v___x_302_;
goto _start;
}
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__3));
v___x_305_ = lean_string_append(v_b_262_, v___x_304_);
v_a_261_ = v___x_265_;
v_b_262_ = v___x_305_;
goto _start;
}
}
else
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__4));
v___x_308_ = lean_string_append(v_b_262_, v___x_307_);
v_a_261_ = v___x_265_;
v_b_262_ = v___x_308_;
goto _start;
}
}
else
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__5));
v___x_311_ = lean_string_append(v_b_262_, v___x_310_);
v_a_261_ = v___x_265_;
v_b_262_ = v___x_311_;
goto _start;
}
}
else
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__6));
v___x_314_ = lean_string_append(v_b_262_, v___x_313_);
v_a_261_ = v___x_265_;
v_b_262_ = v___x_314_;
goto _start;
}
}
else
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__7));
v___x_317_ = lean_string_append(v_b_262_, v___x_316_);
v_a_261_ = v___x_265_;
v_b_262_ = v___x_317_;
goto _start;
}
v___jp_266_:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; uint32_t v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_267_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__0));
v___x_268_ = lean_string_append(v_b_262_, v___x_267_);
v___x_269_ = lean_unsigned_to_nat(16u);
v___x_270_ = lean_uint32_to_nat(v___x_264_);
v___x_271_ = l_Nat_toDigits(v___x_269_, v___x_270_);
v___x_272_ = lean_string_mk(v___x_271_);
v___x_273_ = 48;
v___x_274_ = lean_unsigned_to_nat(4u);
v___x_275_ = l_Lake_lpadAscii(v___x_272_, v___x_273_, v___x_274_);
lean_dec_ref(v___x_272_);
v___x_276_ = lean_string_append(v___x_268_, v___x_275_);
lean_dec_ref(v___x_275_);
v_a_261_ = v___x_265_;
v_b_262_ = v___x_276_;
goto _start;
}
}
else
{
lean_dec(v_a_261_);
return v_b_262_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___boxed(lean_object* v___x_319_, lean_object* v_s_320_, lean_object* v_a_321_, lean_object* v_b_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg(v___x_319_, v_s_320_, v_a_321_, v_b_322_);
lean_dec_ref(v_s_320_);
lean_dec(v___x_319_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppString(lean_object* v_s_325_){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v_s_329_; uint32_t v___x_330_; lean_object* v___x_331_; 
v___x_326_ = ((lean_object*)(l_Lake_Toml_ppString___closed__0));
v___x_327_ = lean_string_utf8_byte_size(v_s_325_);
v___x_328_ = lean_unsigned_to_nat(0u);
v_s_329_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg(v___x_327_, v_s_325_, v___x_328_, v___x_326_);
v___x_330_ = 34;
v___x_331_ = lean_string_push(v_s_329_, v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppString___boxed(lean_object* v_s_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lake_Toml_ppString(v_s_332_);
lean_dec_ref(v_s_332_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0(lean_object* v___x_334_, lean_object* v___x_335_, lean_object* v_s_336_, lean_object* v_inst_337_, lean_object* v_R_338_, lean_object* v_a_339_, lean_object* v_b_340_, lean_object* v_c_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg(v___x_335_, v_s_336_, v_a_339_, v_b_340_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___boxed(lean_object* v___x_343_, lean_object* v___x_344_, lean_object* v_s_345_, lean_object* v_inst_346_, lean_object* v_R_347_, lean_object* v_a_348_, lean_object* v_b_349_, lean_object* v_c_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0(v___x_343_, v___x_344_, v_s_345_, v_inst_346_, v_R_347_, v_a_348_, v_b_349_, v_c_350_);
lean_dec_ref(v_s_345_);
lean_dec(v___x_344_);
lean_dec_ref(v___x_343_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lake_Toml_ppSimpleKey_spec__0(lean_object* v_s_352_, lean_object* v_pos_353_){
_start:
{
lean_object* v_str_354_; lean_object* v_startInclusive_355_; lean_object* v_endExclusive_356_; lean_object* v___x_357_; lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v_decide_368_; 
v_str_354_ = lean_ctor_get(v_s_352_, 0);
v_startInclusive_355_ = lean_ctor_get(v_s_352_, 1);
v_endExclusive_356_ = lean_ctor_get(v_s_352_, 2);
v___x_357_ = lean_nat_add(v_startInclusive_355_, v_pos_353_);
v___x_366_ = lean_unsigned_to_nat(0u);
v___x_367_ = lean_nat_sub(v_endExclusive_356_, v___x_357_);
v_decide_368_ = lean_nat_dec_eq(v___x_366_, v___x_367_);
lean_dec(v___x_367_);
if (v_decide_368_ == 0)
{
uint32_t v___x_369_; uint32_t v___x_385_; uint8_t v___x_386_; 
v___x_369_ = lean_string_utf8_get_fast(v_str_354_, v___x_357_);
v___x_385_ = 65;
v___x_386_ = lean_uint32_dec_le(v___x_385_, v___x_369_);
if (v___x_386_ == 0)
{
goto v___jp_380_;
}
else
{
uint32_t v___x_387_; uint8_t v___x_388_; 
v___x_387_ = 90;
v___x_388_ = lean_uint32_dec_le(v___x_369_, v___x_387_);
if (v___x_388_ == 0)
{
goto v___jp_380_;
}
else
{
goto v___jp_358_;
}
}
v___jp_370_:
{
uint32_t v___x_371_; uint8_t v___x_372_; 
v___x_371_ = 95;
v___x_372_ = lean_uint32_dec_eq(v___x_369_, v___x_371_);
if (v___x_372_ == 0)
{
uint32_t v___x_373_; uint8_t v___x_374_; 
v___x_373_ = 45;
v___x_374_ = lean_uint32_dec_eq(v___x_369_, v___x_373_);
if (v___x_374_ == 0)
{
lean_dec(v___x_357_);
return v_pos_353_;
}
else
{
goto v___jp_358_;
}
}
else
{
goto v___jp_358_;
}
}
v___jp_375_:
{
uint32_t v___x_376_; uint8_t v___x_377_; 
v___x_376_ = 48;
v___x_377_ = lean_uint32_dec_le(v___x_376_, v___x_369_);
if (v___x_377_ == 0)
{
goto v___jp_370_;
}
else
{
uint32_t v___x_378_; uint8_t v___x_379_; 
v___x_378_ = 57;
v___x_379_ = lean_uint32_dec_le(v___x_369_, v___x_378_);
if (v___x_379_ == 0)
{
goto v___jp_370_;
}
else
{
goto v___jp_358_;
}
}
}
v___jp_380_:
{
uint32_t v___x_381_; uint8_t v___x_382_; 
v___x_381_ = 97;
v___x_382_ = lean_uint32_dec_le(v___x_381_, v___x_369_);
if (v___x_382_ == 0)
{
goto v___jp_375_;
}
else
{
uint32_t v___x_383_; uint8_t v___x_384_; 
v___x_383_ = 122;
v___x_384_ = lean_uint32_dec_le(v___x_369_, v___x_383_);
if (v___x_384_ == 0)
{
goto v___jp_375_;
}
else
{
goto v___jp_358_;
}
}
}
}
else
{
lean_dec(v___x_357_);
return v_pos_353_;
}
v___jp_358_:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_359_ = lean_string_utf8_next_fast(v_str_354_, v___x_357_);
v___x_360_ = lean_nat_sub(v___x_359_, v___x_357_);
lean_dec(v___x_357_);
v___x_361_ = lean_nat_add(v_pos_353_, v___x_360_);
lean_dec(v___x_360_);
v___x_362_ = lean_unsigned_to_nat(1u);
v___x_363_ = lean_nat_add(v_pos_353_, v___x_362_);
v___x_364_ = lean_nat_dec_le(v___x_363_, v___x_361_);
lean_dec(v___x_363_);
if (v___x_364_ == 0)
{
lean_dec(v___x_361_);
return v_pos_353_;
}
else
{
lean_dec(v_pos_353_);
v_pos_353_ = v___x_361_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lake_Toml_ppSimpleKey_spec__0___boxed(lean_object* v_s_389_, lean_object* v_pos_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_String_Slice_Pos_skipWhile___at___00Lake_Toml_ppSimpleKey_spec__0(v_s_389_, v_pos_390_);
lean_dec_ref(v_s_389_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppSimpleKey(lean_object* v_k_392_){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; uint8_t v_decide_397_; 
v___x_393_ = lean_unsigned_to_nat(0u);
v___x_394_ = lean_string_utf8_byte_size(v_k_392_);
lean_inc_ref(v_k_392_);
v___x_395_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_395_, 0, v_k_392_);
lean_ctor_set(v___x_395_, 1, v___x_393_);
lean_ctor_set(v___x_395_, 2, v___x_394_);
v___x_396_ = l_String_Slice_Pos_skipWhile___at___00Lake_Toml_ppSimpleKey_spec__0(v___x_395_, v___x_393_);
lean_dec_ref_known(v___x_395_, 3);
v_decide_397_ = lean_nat_dec_eq(v___x_396_, v___x_394_);
lean_dec(v___x_396_);
if (v_decide_397_ == 0)
{
lean_object* v___x_398_; 
v___x_398_ = l_Lake_Toml_ppString(v_k_392_);
lean_dec_ref(v_k_392_);
return v___x_398_;
}
else
{
return v_k_392_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppKey(lean_object* v_k_400_){
_start:
{
if (lean_obj_tag(v_k_400_) == 1)
{
lean_object* v_pre_401_; lean_object* v_str_402_; uint8_t v___x_403_; 
v_pre_401_ = lean_ctor_get(v_k_400_, 0);
lean_inc(v_pre_401_);
v_str_402_ = lean_ctor_get(v_k_400_, 1);
lean_inc_ref(v_str_402_);
lean_dec_ref_known(v_k_400_, 2);
v___x_403_ = l_Lean_Name_isAnonymous(v_pre_401_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_404_ = l_Lake_Toml_ppKey(v_pre_401_);
v___x_405_ = ((lean_object*)(l_Lake_Toml_ppKey___closed__0));
v___x_406_ = lean_string_append(v___x_404_, v___x_405_);
v___x_407_ = l_Lake_Toml_ppSimpleKey(v_str_402_);
v___x_408_ = lean_string_append(v___x_406_, v___x_407_);
lean_dec_ref(v___x_407_);
return v___x_408_;
}
else
{
lean_object* v___x_409_; 
lean_dec(v_pre_401_);
v___x_409_ = l_Lake_Toml_ppSimpleKey(v_str_402_);
return v___x_409_;
}
}
else
{
lean_object* v___x_410_; 
lean_dec(v_k_400_);
v___x_410_ = ((lean_object*)(l_Lake_Toml_instInhabitedValue_default___closed__0));
return v___x_410_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0(size_t v_sz_417_, size_t v_i_418_, lean_object* v_bs_419_){
_start:
{
uint8_t v___x_420_; 
v___x_420_ = lean_usize_dec_lt(v_i_418_, v_sz_417_);
if (v___x_420_ == 0)
{
return v_bs_419_;
}
else
{
lean_object* v_v_421_; lean_object* v_fst_422_; lean_object* v_snd_423_; lean_object* v___x_424_; lean_object* v_bs_x27_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; size_t v___x_431_; size_t v___x_432_; lean_object* v___x_433_; 
v_v_421_ = lean_array_uget_borrowed(v_bs_419_, v_i_418_);
v_fst_422_ = lean_ctor_get(v_v_421_, 0);
lean_inc(v_fst_422_);
v_snd_423_ = lean_ctor_get(v_v_421_, 1);
lean_inc(v_snd_423_);
v___x_424_ = lean_unsigned_to_nat(0u);
v_bs_x27_425_ = lean_array_uset(v_bs_419_, v_i_418_, v___x_424_);
v___x_426_ = l_Lake_Toml_ppKey(v_fst_422_);
v___x_427_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___closed__0));
v___x_428_ = lean_string_append(v___x_426_, v___x_427_);
v___x_429_ = l_Lake_Toml_Value_toString(v_snd_423_);
v___x_430_ = lean_string_append(v___x_428_, v___x_429_);
lean_dec_ref(v___x_429_);
v___x_431_ = ((size_t)1ULL);
v___x_432_ = lean_usize_add(v_i_418_, v___x_431_);
v___x_433_ = lean_array_uset(v_bs_x27_425_, v_i_418_, v___x_430_);
v_i_418_ = v___x_432_;
v_bs_419_ = v___x_433_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppInlineTable(lean_object* v_t_437_){
_start:
{
lean_object* v_items_438_; size_t v_sz_439_; size_t v___x_440_; lean_object* v_xs_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v_items_438_ = lean_ctor_get(v_t_437_, 0);
lean_inc_ref(v_items_438_);
lean_dec_ref(v_t_437_);
v_sz_439_ = lean_array_size(v_items_438_);
v___x_440_ = ((size_t)0ULL);
v_xs_441_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0(v_sz_439_, v___x_440_, v_items_438_);
v___x_442_ = ((lean_object*)(l_Lake_Toml_ppInlineTable___closed__0));
v___x_443_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__1));
v___x_444_ = lean_array_to_list(v_xs_441_);
v___x_445_ = l_String_intercalate(v___x_443_, v___x_444_);
v___x_446_ = lean_string_append(v___x_442_, v___x_445_);
lean_dec_ref(v___x_445_);
v___x_447_ = ((lean_object*)(l_Lake_Toml_ppInlineTable___closed__1));
v___x_448_ = lean_string_append(v___x_446_, v___x_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_toString(lean_object* v_v_449_){
_start:
{
switch(lean_obj_tag(v_v_449_))
{
case 0:
{
lean_object* v_s_450_; lean_object* v___x_451_; 
v_s_450_ = lean_ctor_get(v_v_449_, 1);
lean_inc_ref(v_s_450_);
lean_dec_ref_known(v_v_449_, 2);
v___x_451_ = l_Lake_Toml_ppString(v_s_450_);
lean_dec_ref(v_s_450_);
return v___x_451_;
}
case 1:
{
lean_object* v_n_452_; lean_object* v___x_453_; 
v_n_452_ = lean_ctor_get(v_v_449_, 1);
lean_inc(v_n_452_);
lean_dec_ref_known(v_v_449_, 2);
v___x_453_ = l_Int_repr(v_n_452_);
lean_dec(v_n_452_);
return v___x_453_;
}
case 2:
{
double v_n_454_; lean_object* v___x_455_; 
v_n_454_ = lean_ctor_get_float(v_v_449_, sizeof(void*)*1);
lean_dec_ref_known(v_v_449_, 1);
v___x_455_ = lean_float_to_string(v_n_454_);
return v___x_455_;
}
case 3:
{
uint8_t v_b_456_; 
v_b_456_ = lean_ctor_get_uint8(v_v_449_, sizeof(void*)*1);
lean_dec_ref_known(v_v_449_, 1);
if (v_b_456_ == 0)
{
lean_object* v___x_457_; 
v___x_457_ = ((lean_object*)(l_Lake_Toml_Value_toString___closed__0));
return v___x_457_;
}
else
{
lean_object* v___x_458_; 
v___x_458_ = ((lean_object*)(l_Lake_Toml_Value_toString___closed__1));
return v___x_458_;
}
}
case 4:
{
lean_object* v_dt_459_; lean_object* v___x_460_; 
v_dt_459_ = lean_ctor_get(v_v_449_, 1);
lean_inc_ref(v_dt_459_);
lean_dec_ref_known(v_v_449_, 2);
v___x_460_ = l_Lake_Toml_DateTime_toString(v_dt_459_);
return v___x_460_;
}
case 5:
{
lean_object* v_xs_461_; lean_object* v___x_462_; 
v_xs_461_ = lean_ctor_get(v_v_449_, 1);
lean_inc_ref(v_xs_461_);
lean_dec_ref_known(v_v_449_, 2);
v___x_462_ = l_Lake_Toml_ppInlineArray(v_xs_461_);
return v___x_462_;
}
default: 
{
lean_object* v_xs_463_; lean_object* v___x_464_; 
v_xs_463_ = lean_ctor_get(v_v_449_, 1);
lean_inc_ref(v_xs_463_);
lean_dec_ref_known(v_v_449_, 2);
v___x_464_ = l_Lake_Toml_ppInlineTable(v_xs_463_);
return v___x_464_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3(size_t v_sz_465_, size_t v_i_466_, lean_object* v_bs_467_){
_start:
{
uint8_t v___x_468_; 
v___x_468_ = lean_usize_dec_lt(v_i_466_, v_sz_465_);
if (v___x_468_ == 0)
{
return v_bs_467_;
}
else
{
lean_object* v_v_469_; lean_object* v___x_470_; lean_object* v_bs_x27_471_; lean_object* v___x_472_; size_t v___x_473_; size_t v___x_474_; lean_object* v___x_475_; 
v_v_469_ = lean_array_uget(v_bs_467_, v_i_466_);
v___x_470_ = lean_unsigned_to_nat(0u);
v_bs_x27_471_ = lean_array_uset(v_bs_467_, v_i_466_, v___x_470_);
v___x_472_ = l_Lake_Toml_Value_toString(v_v_469_);
v___x_473_ = ((size_t)1ULL);
v___x_474_ = lean_usize_add(v_i_466_, v___x_473_);
v___x_475_ = lean_array_uset(v_bs_x27_471_, v_i_466_, v___x_472_);
v_i_466_ = v___x_474_;
v_bs_467_ = v___x_475_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppInlineArray(lean_object* v_vs_477_){
_start:
{
size_t v_sz_478_; size_t v___x_479_; lean_object* v_xs_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v_sz_478_ = lean_array_size(v_vs_477_);
v___x_479_ = ((size_t)0ULL);
v_xs_480_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3(v_sz_478_, v___x_479_, v_vs_477_);
v___x_481_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__0));
v___x_482_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__1));
v___x_483_ = lean_array_to_list(v_xs_480_);
v___x_484_ = l_String_intercalate(v___x_482_, v___x_483_);
v___x_485_ = lean_string_append(v___x_481_, v___x_484_);
lean_dec_ref(v___x_484_);
v___x_486_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__2));
v___x_487_ = lean_string_append(v___x_485_, v___x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3___boxed(lean_object* v_sz_488_, lean_object* v_i_489_, lean_object* v_bs_490_){
_start:
{
size_t v_sz_boxed_491_; size_t v_i_boxed_492_; lean_object* v_res_493_; 
v_sz_boxed_491_ = lean_unbox_usize(v_sz_488_);
lean_dec(v_sz_488_);
v_i_boxed_492_ = lean_unbox_usize(v_i_489_);
lean_dec(v_i_489_);
v_res_493_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3(v_sz_boxed_491_, v_i_boxed_492_, v_bs_490_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___boxed(lean_object* v_sz_494_, lean_object* v_i_495_, lean_object* v_bs_496_){
_start:
{
size_t v_sz_boxed_497_; size_t v_i_boxed_498_; lean_object* v_res_499_; 
v_sz_boxed_497_ = lean_unbox_usize(v_sz_494_);
lean_dec(v_sz_494_);
v_i_boxed_498_ = lean_unbox_usize(v_i_495_);
lean_dec(v_i_495_);
v_res_499_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0(v_sz_boxed_497_, v_i_boxed_498_, v_bs_496_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval(lean_object* v_s_503_, lean_object* v_k_504_, lean_object* v_v_505_){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_506_ = l_Lake_Toml_ppKey(v_k_504_);
v___x_507_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___closed__0));
v___x_508_ = lean_string_append(v___x_506_, v___x_507_);
v___x_509_ = l_Lake_Toml_Value_toString(v_v_505_);
v___x_510_ = lean_string_append(v___x_508_, v___x_509_);
lean_dec_ref(v___x_509_);
v___x_511_ = ((lean_object*)(l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval___closed__0));
v___x_512_ = lean_string_append(v___x_510_, v___x_511_);
v___x_513_ = lean_string_append(v_s_503_, v___x_512_);
lean_dec_ref(v___x_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lake_Toml_ppTable_spec__2(lean_object* v_msg_514_){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = ((lean_object*)(l_Lake_Toml_instInhabitedValue_default___closed__0));
v___x_516_ = lean_panic_fn_borrowed(v___x_515_, v_msg_514_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(lean_object* v_as_517_, size_t v_i_518_, size_t v_stop_519_, lean_object* v_b_520_){
_start:
{
uint8_t v___x_521_; 
v___x_521_ = lean_usize_dec_eq(v_i_518_, v_stop_519_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; lean_object* v_fst_523_; lean_object* v_snd_524_; lean_object* v___x_525_; size_t v___x_526_; size_t v___x_527_; 
v___x_522_ = lean_array_uget_borrowed(v_as_517_, v_i_518_);
v_fst_523_ = lean_ctor_get(v___x_522_, 0);
v_snd_524_ = lean_ctor_get(v___x_522_, 1);
lean_inc(v_snd_524_);
lean_inc(v_fst_523_);
v___x_525_ = l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval(v_b_520_, v_fst_523_, v_snd_524_);
v___x_526_ = ((size_t)1ULL);
v___x_527_ = lean_usize_add(v_i_518_, v___x_526_);
v_i_518_ = v___x_527_;
v_b_520_ = v___x_525_;
goto _start;
}
else
{
return v_b_520_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1___boxed(lean_object* v_as_529_, lean_object* v_i_530_, lean_object* v_stop_531_, lean_object* v_b_532_){
_start:
{
size_t v_i_boxed_533_; size_t v_stop_boxed_534_; lean_object* v_res_535_; 
v_i_boxed_533_ = lean_unbox_usize(v_i_530_);
lean_dec(v_i_530_);
v_stop_boxed_534_ = lean_unbox_usize(v_stop_531_);
lean_dec(v_stop_531_);
v_res_535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_as_529_, v_i_boxed_533_, v_stop_boxed_534_, v_b_532_);
lean_dec_ref(v_as_529_);
return v_res_535_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_541_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__4));
v___x_542_ = lean_unsigned_to_nat(17u);
v___x_543_ = lean_unsigned_to_nat(128u);
v___x_544_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__3));
v___x_545_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__2));
v___x_546_ = l_mkPanicMessageWithDecl(v___x_545_, v___x_544_, v___x_543_, v___x_542_, v___x_541_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3(lean_object* v_fst_547_, lean_object* v_as_548_, size_t v_i_549_, size_t v_stop_550_, lean_object* v_b_551_){
_start:
{
lean_object* v___y_553_; lean_object* v___y_558_; uint8_t v___x_561_; 
v___x_561_ = lean_usize_dec_eq(v_i_549_, v_stop_550_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; 
v___x_562_ = lean_array_uget_borrowed(v_as_548_, v_i_549_);
if (lean_obj_tag(v___x_562_) == 6)
{
lean_object* v_xs_563_; lean_object* v_items_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v_s_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v_xs_563_ = lean_ctor_get(v___x_562_, 1);
v_items_564_ = lean_ctor_get(v_xs_563_, 0);
v___x_565_ = lean_unsigned_to_nat(0u);
v___x_566_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__0));
lean_inc(v_fst_547_);
v___x_567_ = l_Lake_Toml_ppKey(v_fst_547_);
v___x_568_ = lean_string_append(v___x_566_, v___x_567_);
lean_dec_ref(v___x_567_);
v___x_569_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__1));
v___x_570_ = lean_string_append(v___x_568_, v___x_569_);
v_s_571_ = lean_string_append(v_b_551_, v___x_570_);
lean_dec_ref(v___x_570_);
v___x_572_ = lean_array_get_size(v_items_564_);
v___x_573_ = lean_nat_dec_lt(v___x_565_, v___x_572_);
if (v___x_573_ == 0)
{
v___y_558_ = v_s_571_;
goto v___jp_557_;
}
else
{
size_t v___x_574_; size_t v___x_575_; lean_object* v___x_576_; 
v___x_574_ = ((size_t)0ULL);
v___x_575_ = lean_usize_of_nat(v___x_572_);
v___x_576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_items_564_, v___x_574_, v___x_575_, v_s_571_);
v___y_558_ = v___x_576_;
goto v___jp_557_;
}
}
else
{
lean_object* v___x_577_; lean_object* v___x_578_; 
lean_dec_ref(v_b_551_);
v___x_577_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5);
v___x_578_ = l_panic___at___00Lake_Toml_ppTable_spec__2(v___x_577_);
v___y_553_ = v___x_578_;
goto v___jp_552_;
}
}
else
{
lean_dec(v_fst_547_);
return v_b_551_;
}
v___jp_552_:
{
size_t v___x_554_; size_t v___x_555_; 
v___x_554_ = ((size_t)1ULL);
v___x_555_ = lean_usize_add(v_i_549_, v___x_554_);
v_i_549_ = v___x_555_;
v_b_551_ = v___y_553_;
goto _start;
}
v___jp_557_:
{
uint32_t v___x_559_; lean_object* v___x_560_; 
v___x_559_ = 10;
v___x_560_ = lean_string_push(v___y_558_, v___x_559_);
v___y_553_ = v___x_560_;
goto v___jp_552_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___boxed(lean_object* v_fst_579_, lean_object* v_as_580_, lean_object* v_i_581_, lean_object* v_stop_582_, lean_object* v_b_583_){
_start:
{
size_t v_i_boxed_584_; size_t v_stop_boxed_585_; lean_object* v_res_586_; 
v_i_boxed_584_ = lean_unbox_usize(v_i_581_);
lean_dec(v_i_581_);
v_stop_boxed_585_ = lean_unbox_usize(v_stop_582_);
lean_dec(v_stop_582_);
v_res_586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3(v_fst_579_, v_as_580_, v_i_boxed_584_, v_stop_boxed_585_, v_b_583_);
lean_dec_ref(v_as_580_);
return v_res_586_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Toml_ppTable_spec__4(lean_object* v___x_587_, lean_object* v_as_588_, size_t v_i_589_, size_t v_stop_590_){
_start:
{
uint8_t v___x_591_; 
v___x_591_ = lean_usize_dec_eq(v_i_589_, v_stop_590_);
if (v___x_591_ == 0)
{
uint8_t v___x_592_; lean_object* v___x_593_; 
v___x_592_ = 1;
v___x_593_ = lean_array_uget_borrowed(v_as_588_, v_i_589_);
if (lean_obj_tag(v___x_593_) == 6)
{
lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_594_ = lean_unsigned_to_nat(0u);
v___x_595_ = lean_nat_dec_eq(v___x_587_, v___x_594_);
if (v___x_595_ == 0)
{
size_t v___x_596_; size_t v___x_597_; 
v___x_596_ = ((size_t)1ULL);
v___x_597_ = lean_usize_add(v_i_589_, v___x_596_);
v_i_589_ = v___x_597_;
goto _start;
}
else
{
return v___x_592_;
}
}
else
{
return v___x_592_;
}
}
else
{
uint8_t v___x_599_; 
v___x_599_ = 0;
return v___x_599_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Toml_ppTable_spec__4___boxed(lean_object* v___x_600_, lean_object* v_as_601_, lean_object* v_i_602_, lean_object* v_stop_603_){
_start:
{
size_t v_i_boxed_604_; size_t v_stop_boxed_605_; uint8_t v_res_606_; lean_object* v_r_607_; 
v_i_boxed_604_ = lean_unbox_usize(v_i_602_);
lean_dec(v_i_602_);
v_stop_boxed_605_ = lean_unbox_usize(v_stop_603_);
lean_dec(v_stop_603_);
v_res_606_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Toml_ppTable_spec__4(v___x_600_, v_as_601_, v_i_boxed_604_, v_stop_boxed_605_);
lean_dec_ref(v_as_601_);
lean_dec(v___x_600_);
v_r_607_ = lean_box(v_res_606_);
return v_r_607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5(lean_object* v_as_610_, size_t v_i_611_, size_t v_stop_612_, lean_object* v_b_613_){
_start:
{
lean_object* v___y_615_; uint8_t v___x_619_; 
v___x_619_ = lean_usize_dec_eq(v_i_611_, v_stop_612_);
if (v___x_619_ == 0)
{
lean_object* v_fst_620_; lean_object* v_snd_621_; lean_object* v___y_623_; lean_object* v___x_627_; lean_object* v_snd_628_; 
v_fst_620_ = lean_ctor_get(v_b_613_, 0);
v_snd_621_ = lean_ctor_get(v_b_613_, 1);
v___x_627_ = lean_array_uget(v_as_610_, v_i_611_);
v_snd_628_ = lean_ctor_get(v___x_627_, 1);
switch(lean_obj_tag(v_snd_628_))
{
case 5:
{
lean_object* v_fst_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_679_; 
lean_inc_ref(v_snd_628_);
v_fst_629_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_679_ == 0)
{
lean_object* v_unused_680_; 
v_unused_680_ = lean_ctor_get(v___x_627_, 1);
lean_dec(v_unused_680_);
v___x_631_ = v___x_627_;
v_isShared_632_ = v_isSharedCheck_679_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_fst_629_);
lean_dec(v___x_627_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_679_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v_xs_633_; lean_object* v___x_634_; lean_object* v___x_635_; uint8_t v___x_644_; 
v_xs_633_ = lean_ctor_get(v_snd_628_, 1);
lean_inc_ref(v_xs_633_);
lean_dec_ref_known(v_snd_628_, 2);
v___x_634_ = lean_array_get_size(v_xs_633_);
v___x_635_ = lean_unsigned_to_nat(0u);
v___x_644_ = lean_nat_dec_eq(v___x_634_, v___x_635_);
if (v___x_644_ == 0)
{
uint8_t v___x_645_; 
v___x_645_ = lean_nat_dec_lt(v___x_635_, v___x_634_);
if (v___x_645_ == 0)
{
goto v___jp_636_;
}
else
{
if (v___x_645_ == 0)
{
goto v___jp_636_;
}
else
{
size_t v___x_646_; size_t v___x_647_; uint8_t v___x_648_; 
v___x_646_ = ((size_t)0ULL);
v___x_647_ = lean_usize_of_nat(v___x_634_);
v___x_648_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Toml_ppTable_spec__4(v___x_634_, v_xs_633_, v___x_646_, v___x_647_);
if (v___x_648_ == 0)
{
goto v___jp_636_;
}
else
{
lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_663_; 
lean_inc(v_snd_621_);
lean_inc(v_fst_620_);
lean_del_object(v___x_631_);
v_isSharedCheck_663_ = !lean_is_exclusive(v_b_613_);
if (v_isSharedCheck_663_ == 0)
{
lean_object* v_unused_664_; lean_object* v_unused_665_; 
v_unused_664_ = lean_ctor_get(v_b_613_, 1);
lean_dec(v_unused_664_);
v_unused_665_ = lean_ctor_get(v_b_613_, 0);
lean_dec(v_unused_665_);
v___x_650_ = v_b_613_;
v_isShared_651_ = v_isSharedCheck_663_;
goto v_resetjp_649_;
}
else
{
lean_dec(v_b_613_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_663_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_652_ = l_Lake_Toml_ppKey(v_fst_629_);
v___x_653_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___closed__0));
v___x_654_ = lean_string_append(v___x_652_, v___x_653_);
v___x_655_ = l_Lake_Toml_ppInlineArray(v_xs_633_);
v___x_656_ = lean_string_append(v___x_654_, v___x_655_);
lean_dec_ref(v___x_655_);
v___x_657_ = ((lean_object*)(l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval___closed__0));
v___x_658_ = lean_string_append(v___x_656_, v___x_657_);
v___x_659_ = lean_string_append(v_fst_620_, v___x_658_);
lean_dec_ref(v___x_658_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 0, v___x_659_);
v___x_661_ = v___x_650_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
lean_ctor_set(v_reuseFailAlloc_662_, 1, v_snd_621_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
v___y_615_ = v___x_661_;
goto v___jp_614_;
}
}
}
}
}
}
else
{
lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_676_; 
lean_inc(v_snd_621_);
lean_inc(v_fst_620_);
lean_dec_ref(v_xs_633_);
lean_del_object(v___x_631_);
v_isSharedCheck_676_ = !lean_is_exclusive(v_b_613_);
if (v_isSharedCheck_676_ == 0)
{
lean_object* v_unused_677_; lean_object* v_unused_678_; 
v_unused_677_ = lean_ctor_get(v_b_613_, 1);
lean_dec(v_unused_677_);
v_unused_678_ = lean_ctor_get(v_b_613_, 0);
lean_dec(v_unused_678_);
v___x_667_ = v_b_613_;
v_isShared_668_ = v_isSharedCheck_676_;
goto v_resetjp_666_;
}
else
{
lean_dec(v_b_613_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_676_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_669_ = l_Lake_Toml_ppKey(v_fst_629_);
v___x_670_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___closed__0));
v___x_671_ = lean_string_append(v___x_669_, v___x_670_);
v___x_672_ = lean_string_append(v_fst_620_, v___x_671_);
lean_dec_ref(v___x_671_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_672_);
v___x_674_ = v___x_667_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_snd_621_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
v___y_615_ = v___x_674_;
goto v___jp_614_;
}
}
}
v___jp_636_:
{
uint8_t v___x_637_; 
v___x_637_ = lean_nat_dec_lt(v___x_635_, v___x_634_);
if (v___x_637_ == 0)
{
lean_dec_ref(v_xs_633_);
lean_del_object(v___x_631_);
lean_dec(v_fst_629_);
v___y_615_ = v_b_613_;
goto v___jp_614_;
}
else
{
size_t v___x_638_; size_t v___x_639_; lean_object* v___x_640_; lean_object* v___x_642_; 
lean_inc(v_snd_621_);
lean_inc(v_fst_620_);
lean_dec_ref(v_b_613_);
v___x_638_ = ((size_t)0ULL);
v___x_639_ = lean_usize_of_nat(v___x_634_);
v___x_640_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3(v_fst_629_, v_xs_633_, v___x_638_, v___x_639_, v_snd_621_);
lean_dec_ref(v_xs_633_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 1, v___x_640_);
lean_ctor_set(v___x_631_, 0, v_fst_620_);
v___x_642_ = v___x_631_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_fst_620_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v___x_640_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
v___y_615_ = v___x_642_;
goto v___jp_614_;
}
}
}
}
}
case 6:
{
lean_object* v_xs_681_; lean_object* v_fst_682_; lean_object* v_items_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v_fs_689_; lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
lean_inc(v_snd_621_);
lean_inc(v_fst_620_);
lean_dec_ref(v_b_613_);
v_xs_681_ = lean_ctor_get(v_snd_628_, 1);
lean_inc_ref(v_xs_681_);
v_fst_682_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_fst_682_);
lean_dec(v___x_627_);
v_items_683_ = lean_ctor_get(v_xs_681_, 0);
lean_inc_ref(v_items_683_);
lean_dec_ref(v_xs_681_);
v___x_684_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__0));
v___x_685_ = l_Lake_Toml_ppKey(v_fst_682_);
v___x_686_ = lean_string_append(v___x_684_, v___x_685_);
lean_dec_ref(v___x_685_);
v___x_687_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___closed__1));
v___x_688_ = lean_string_append(v___x_686_, v___x_687_);
v_fs_689_ = lean_string_append(v_snd_621_, v___x_688_);
lean_dec_ref(v___x_688_);
v___x_690_ = lean_unsigned_to_nat(0u);
v___x_691_ = lean_array_get_size(v_items_683_);
v___x_692_ = lean_nat_dec_lt(v___x_690_, v___x_691_);
if (v___x_692_ == 0)
{
lean_dec_ref(v_items_683_);
v___y_623_ = v_fs_689_;
goto v___jp_622_;
}
else
{
size_t v___x_693_; size_t v___x_694_; lean_object* v___x_695_; 
v___x_693_ = ((size_t)0ULL);
v___x_694_ = lean_usize_of_nat(v___x_691_);
v___x_695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_items_683_, v___x_693_, v___x_694_, v_fs_689_);
lean_dec_ref(v_items_683_);
v___y_623_ = v___x_695_;
goto v___jp_622_;
}
}
default: 
{
lean_object* v_fst_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_704_; 
lean_inc(v_snd_628_);
lean_inc(v_snd_621_);
lean_inc(v_fst_620_);
lean_dec_ref(v_b_613_);
v_fst_696_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_704_ == 0)
{
lean_object* v_unused_705_; 
v_unused_705_ = lean_ctor_get(v___x_627_, 1);
lean_dec(v_unused_705_);
v___x_698_ = v___x_627_;
v_isShared_699_ = v_isSharedCheck_704_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_fst_696_);
lean_dec(v___x_627_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_704_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v___x_702_; 
v___x_700_ = l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval(v_fst_620_, v_fst_696_, v_snd_628_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v_snd_621_);
lean_ctor_set(v___x_698_, 0, v___x_700_);
v___x_702_ = v___x_698_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v_snd_621_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
v___y_615_ = v___x_702_;
goto v___jp_614_;
}
}
}
}
v___jp_622_:
{
uint32_t v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_624_ = 10;
v___x_625_ = lean_string_push(v___y_623_, v___x_624_);
v___x_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_626_, 0, v_fst_620_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
v___y_615_ = v___x_626_;
goto v___jp_614_;
}
}
else
{
return v_b_613_;
}
v___jp_614_:
{
size_t v___x_616_; size_t v___x_617_; 
v___x_616_ = ((size_t)1ULL);
v___x_617_ = lean_usize_add(v_i_611_, v___x_616_);
v_i_611_ = v___x_617_;
v_b_613_ = v___y_615_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___boxed(lean_object* v_as_706_, lean_object* v_i_707_, lean_object* v_stop_708_, lean_object* v_b_709_){
_start:
{
size_t v_i_boxed_710_; size_t v_stop_boxed_711_; lean_object* v_res_712_; 
v_i_boxed_710_ = lean_unbox_usize(v_i_707_);
lean_dec(v_i_707_);
v_stop_boxed_711_ = lean_unbox_usize(v_stop_708_);
lean_dec(v_stop_708_);
v_res_712_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5(v_as_706_, v_i_boxed_710_, v_stop_boxed_711_, v_b_709_);
lean_dec_ref(v_as_706_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lake_Toml_ppTable_spec__0(lean_object* v_s_713_, lean_object* v_pos_714_){
_start:
{
lean_object* v_str_715_; lean_object* v_startInclusive_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v_decide_720_; 
v_str_715_ = lean_ctor_get(v_s_713_, 0);
v_startInclusive_716_ = lean_ctor_get(v_s_713_, 1);
v___x_717_ = lean_nat_add(v_startInclusive_716_, v_pos_714_);
v___x_718_ = lean_nat_sub(v___x_717_, v_startInclusive_716_);
v___x_719_ = lean_unsigned_to_nat(0u);
v_decide_720_ = lean_nat_dec_eq(v___x_718_, v___x_719_);
if (v_decide_720_ == 0)
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_729_; uint32_t v___x_730_; uint32_t v___x_731_; uint8_t v___x_732_; 
lean_inc(v_startInclusive_716_);
lean_inc_ref(v_str_715_);
v___x_721_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_721_, 0, v_str_715_);
lean_ctor_set(v___x_721_, 1, v_startInclusive_716_);
lean_ctor_set(v___x_721_, 2, v___x_717_);
v___x_722_ = lean_unsigned_to_nat(1u);
v___x_723_ = lean_nat_sub(v___x_718_, v___x_722_);
lean_dec(v___x_718_);
v___x_724_ = l_String_Slice_posLE(v___x_721_, v___x_723_);
lean_dec_ref_known(v___x_721_, 3);
v___x_729_ = lean_nat_add(v_startInclusive_716_, v___x_724_);
v___x_730_ = lean_string_utf8_get_fast(v_str_715_, v___x_729_);
lean_dec(v___x_729_);
v___x_731_ = 32;
v___x_732_ = lean_uint32_dec_eq(v___x_730_, v___x_731_);
if (v___x_732_ == 0)
{
uint32_t v___x_733_; uint8_t v___x_734_; 
v___x_733_ = 9;
v___x_734_ = lean_uint32_dec_eq(v___x_730_, v___x_733_);
if (v___x_734_ == 0)
{
uint32_t v___x_735_; uint8_t v___x_736_; 
v___x_735_ = 13;
v___x_736_ = lean_uint32_dec_eq(v___x_730_, v___x_735_);
if (v___x_736_ == 0)
{
uint32_t v___x_737_; uint8_t v___x_738_; 
v___x_737_ = 10;
v___x_738_ = lean_uint32_dec_eq(v___x_730_, v___x_737_);
if (v___x_738_ == 0)
{
lean_dec(v___x_724_);
return v_pos_714_;
}
else
{
goto v___jp_725_;
}
}
else
{
goto v___jp_725_;
}
}
else
{
goto v___jp_725_;
}
}
else
{
goto v___jp_725_;
}
v___jp_725_:
{
lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_726_ = lean_nat_add(v___x_724_, v___x_722_);
v___x_727_ = lean_nat_dec_le(v___x_726_, v_pos_714_);
lean_dec(v___x_726_);
if (v___x_727_ == 0)
{
lean_dec(v___x_724_);
return v_pos_714_;
}
else
{
lean_dec(v_pos_714_);
v_pos_714_ = v___x_724_;
goto _start;
}
}
}
else
{
lean_dec(v___x_718_);
lean_dec(v___x_717_);
return v_pos_714_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lake_Toml_ppTable_spec__0___boxed(lean_object* v_s_739_, lean_object* v_pos_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_String_Slice_Pos_revSkipWhile___at___00Lake_Toml_ppTable_spec__0(v_s_739_, v_pos_740_);
lean_dec_ref(v_s_739_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppTable(lean_object* v_t_744_){
_start:
{
lean_object* v_fst_746_; lean_object* v_snd_747_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v_items_759_; lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_757_ = ((lean_object*)(l_Lake_Toml_instInhabitedValue_default___closed__0));
v___x_758_ = ((lean_object*)(l_Lake_Toml_ppTable___closed__0));
v_items_759_ = lean_ctor_get(v_t_744_, 0);
v___x_760_ = lean_unsigned_to_nat(0u);
v___x_761_ = lean_array_get_size(v_items_759_);
v___x_762_ = lean_nat_dec_lt(v___x_760_, v___x_761_);
if (v___x_762_ == 0)
{
v_fst_746_ = v___x_757_;
v_snd_747_ = v___x_757_;
goto v___jp_745_;
}
else
{
size_t v___x_763_; size_t v___x_764_; lean_object* v___x_765_; lean_object* v_fst_766_; lean_object* v_snd_767_; 
v___x_763_ = ((size_t)0ULL);
v___x_764_ = lean_usize_of_nat(v___x_761_);
v___x_765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5(v_items_759_, v___x_763_, v___x_764_, v___x_758_);
v_fst_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_fst_766_);
v_snd_767_ = lean_ctor_get(v___x_765_, 1);
lean_inc(v_snd_767_);
lean_dec_ref(v___x_765_);
v_fst_746_ = v_fst_766_;
v_snd_747_ = v_snd_767_;
goto v___jp_745_;
}
v___jp_745_:
{
uint32_t v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_748_ = 10;
v___x_749_ = lean_string_push(v_fst_746_, v___x_748_);
v___x_750_ = lean_string_append(v___x_749_, v_snd_747_);
lean_dec_ref(v_snd_747_);
v___x_751_ = lean_unsigned_to_nat(0u);
v___x_752_ = lean_string_utf8_byte_size(v___x_750_);
lean_inc_ref(v___x_750_);
v___x_753_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_753_, 0, v___x_750_);
lean_ctor_set(v___x_753_, 1, v___x_751_);
lean_ctor_set(v___x_753_, 2, v___x_752_);
v___x_754_ = l_String_Slice_Pos_revSkipWhile___at___00Lake_Toml_ppTable_spec__0(v___x_753_, v___x_752_);
lean_dec_ref_known(v___x_753_, 3);
v___x_755_ = lean_string_utf8_extract_fast(v___x_750_, v___x_751_, v___x_754_);
lean_dec(v___x_754_);
lean_dec_ref(v___x_750_);
v___x_756_ = lean_string_push(v___x_755_, v___x_748_);
return v___x_756_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppTable___boxed(lean_object* v_t_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lake_Toml_ppTable(v_t_768_);
lean_dec_ref(v_t_768_);
return v_res_769_;
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

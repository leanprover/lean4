// Lean compiler output
// Module: Lake.Toml.Data.Value
// Imports: public import Init.Data.Float public import Lake.Toml.Data.Dict public import Lake.Toml.Data.DateTime import Lake.Util.String import Init.Data.String.TakeDrop import Init.Data.String.Search public import Init.Data.String.Defs import Init.Data.ToString.Macro
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
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Lake_Toml_RBDict_empty(lean_object*, lean_object*, lean_object*);
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_String_Slice_positions(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Nat_toDigits(lean_object*, lean_object*);
lean_object* lean_string_mk(lean_object*);
lean_object* l_Lake_lpad(lean_object*, uint32_t, lean_object*);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lake_Toml_RBDict_mkEmpty___redArg(lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lake_Toml_Table_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_Table_empty___closed__0 = (const lean_object*)&l_Lake_Toml_Table_empty___closed__0_value;
static lean_once_cell_t l_Lake_Toml_Table_empty___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_Table_empty___closed__1;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Toml_ppSimpleKey_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Toml_ppSimpleKey_spec__0___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lake_Toml_Value_toString___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_Value_toString___closed__0;
static const lean_string_object l_Lake_Toml_Value_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lake_Toml_Value_toString___closed__1 = (const lean_object*)&l_Lake_Toml_Value_toString___closed__1_value;
static const lean_string_object l_Lake_Toml_Value_toString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lake_Toml_Value_toString___closed__2 = (const lean_object*)&l_Lake_Toml_Value_toString___closed__2_value;
static const lean_string_object l_Lake_Toml_Value_toString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lake_Toml_Value_toString___closed__3 = (const lean_object*)&l_Lake_Toml_Value_toString___closed__3_value;
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00Lake_Toml_ppTable_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00Lake_Toml_ppTable_spec__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_Toml_ppTable___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_ppTable___closed__0;
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
lean_dec_ref(v_t_11_);
v___x_15_ = lean_apply_2(v_k_12_, v_ref_13_, v_n_14_);
return v___x_15_;
}
case 2:
{
lean_object* v_ref_16_; double v_n_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v_ref_16_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_ref_16_);
v_n_17_ = lean_ctor_get_float(v_t_11_, sizeof(void*)*1);
lean_dec_ref(v_t_11_);
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
lean_dec_ref(v_t_11_);
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
lean_dec_ref(v_x_112_);
v_ref_116_ = lean_ctor_get(v_x_113_, 0);
lean_inc(v_ref_116_);
v_s_117_ = lean_ctor_get(v_x_113_, 1);
lean_inc_ref(v_s_117_);
lean_dec_ref(v_x_113_);
v___x_118_ = l_Lean_Syntax_structEq(v_ref_114_, v_ref_116_);
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
lean_dec_ref(v_x_112_);
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
lean_dec_ref(v_x_112_);
v_ref_123_ = lean_ctor_get(v_x_113_, 0);
lean_inc(v_ref_123_);
v_n_124_ = lean_ctor_get(v_x_113_, 1);
lean_inc(v_n_124_);
lean_dec_ref(v_x_113_);
v___x_125_ = l_Lean_Syntax_structEq(v_ref_121_, v_ref_123_);
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
lean_dec_ref(v_x_112_);
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
lean_dec_ref(v_x_112_);
v_ref_130_ = lean_ctor_get(v_x_113_, 0);
lean_inc(v_ref_130_);
v_n_131_ = lean_ctor_get_float(v_x_113_, sizeof(void*)*1);
lean_dec_ref(v_x_113_);
v___x_132_ = l_Lean_Syntax_structEq(v_ref_128_, v_ref_130_);
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
lean_dec_ref(v_x_112_);
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
lean_dec_ref(v_x_112_);
v_ref_137_ = lean_ctor_get(v_x_113_, 0);
lean_inc(v_ref_137_);
v_b_138_ = lean_ctor_get_uint8(v_x_113_, sizeof(void*)*1);
lean_dec_ref(v_x_113_);
v___x_139_ = l_Lean_Syntax_structEq(v_ref_135_, v_ref_137_);
if (v___x_139_ == 0)
{
return v___x_139_;
}
else
{
if (v_b_136_ == 0)
{
if (v_b_138_ == 0)
{
return v___x_139_;
}
else
{
return v_b_136_;
}
}
else
{
return v_b_138_;
}
}
}
else
{
uint8_t v___x_140_; 
lean_dec_ref(v_x_112_);
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
lean_dec_ref(v_x_112_);
v_ref_143_ = lean_ctor_get(v_x_113_, 0);
lean_inc(v_ref_143_);
v_dt_144_ = lean_ctor_get(v_x_113_, 1);
lean_inc_ref(v_dt_144_);
lean_dec_ref(v_x_113_);
v___x_145_ = l_Lean_Syntax_structEq(v_ref_141_, v_ref_143_);
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
lean_dec_ref(v_x_112_);
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
lean_dec_ref(v_x_112_);
v_ref_150_ = lean_ctor_get(v_x_113_, 0);
lean_inc(v_ref_150_);
v_xs_151_ = lean_ctor_get(v_x_113_, 1);
lean_inc_ref(v_xs_151_);
lean_dec_ref(v_x_113_);
v___x_152_ = l_Lean_Syntax_structEq(v_ref_148_, v_ref_150_);
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
lean_dec_ref(v_x_112_);
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
lean_dec_ref(v_x_112_);
v_ref_160_ = lean_ctor_get(v_x_113_, 0);
lean_inc(v_ref_160_);
v_xs_161_ = lean_ctor_get(v_x_113_, 1);
lean_inc_ref(v_xs_161_);
lean_dec_ref(v_x_113_);
v___x_162_ = l_Lean_Syntax_structEq(v_ref_158_, v_ref_160_);
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
lean_dec_ref(v_x_112_);
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
static lean_object* _init_l_Lake_Toml_Table_empty___closed__1(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = ((lean_object*)(l_Lake_Toml_Table_empty___closed__0));
v___x_248_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_247_);
return v___x_248_;
}
}
static lean_object* _init_l_Lake_Toml_Table_empty(void){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = lean_obj_once(&l_Lake_Toml_Table_empty___closed__1, &l_Lake_Toml_Table_empty___closed__1_once, _init_l_Lake_Toml_Table_empty___closed__1);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_mkEmpty(lean_object* v_capacity_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = l_Lake_Toml_RBDict_mkEmpty___redArg(v_capacity_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_mkEmpty___boxed(lean_object* v_capacity_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lake_Toml_Table_mkEmpty(v_capacity_252_);
lean_dec(v_capacity_252_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_table(lean_object* v_ref_254_, lean_object* v_t_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_256_, 0, v_ref_254_);
lean_ctor_set(v___x_256_, 1, v_t_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_ref(lean_object* v_x_257_){
_start:
{
lean_object* v_ref_258_; 
v_ref_258_ = lean_ctor_get(v_x_257_, 0);
lean_inc(v_ref_258_);
return v_ref_258_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_ref___boxed(lean_object* v_x_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lake_Toml_Value_ref(v_x_259_);
lean_dec_ref(v_x_259_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg(lean_object* v___x_269_, lean_object* v_s_270_, lean_object* v_a_271_, lean_object* v_b_272_){
_start:
{
lean_object* v_startInclusive_273_; lean_object* v_endExclusive_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v_startInclusive_273_ = lean_ctor_get(v___x_269_, 1);
v_endExclusive_274_ = lean_ctor_get(v___x_269_, 2);
v___x_275_ = lean_nat_sub(v_endExclusive_274_, v_startInclusive_273_);
v___x_276_ = lean_nat_dec_eq(v_a_271_, v___x_275_);
lean_dec(v___x_275_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; uint32_t v___x_278_; uint8_t v___y_280_; uint32_t v___x_294_; uint8_t v___x_295_; 
v___x_277_ = lean_string_utf8_next_fast(v_s_270_, v_a_271_);
v___x_278_ = lean_string_utf8_get_fast(v_s_270_, v_a_271_);
lean_dec(v_a_271_);
v___x_294_ = 8;
v___x_295_ = lean_uint32_dec_eq(v___x_278_, v___x_294_);
if (v___x_295_ == 0)
{
uint32_t v___x_296_; uint8_t v___x_297_; 
v___x_296_ = 9;
v___x_297_ = lean_uint32_dec_eq(v___x_278_, v___x_296_);
if (v___x_297_ == 0)
{
uint32_t v___x_298_; uint8_t v___x_299_; 
v___x_298_ = 10;
v___x_299_ = lean_uint32_dec_eq(v___x_278_, v___x_298_);
if (v___x_299_ == 0)
{
uint32_t v___x_300_; uint8_t v___x_301_; 
v___x_300_ = 12;
v___x_301_ = lean_uint32_dec_eq(v___x_278_, v___x_300_);
if (v___x_301_ == 0)
{
uint32_t v___x_302_; uint8_t v___x_303_; 
v___x_302_ = 13;
v___x_303_ = lean_uint32_dec_eq(v___x_278_, v___x_302_);
if (v___x_303_ == 0)
{
uint32_t v___x_304_; uint8_t v___x_305_; 
v___x_304_ = 34;
v___x_305_ = lean_uint32_dec_eq(v___x_278_, v___x_304_);
if (v___x_305_ == 0)
{
uint32_t v___x_306_; uint8_t v___x_307_; 
v___x_306_ = 92;
v___x_307_ = lean_uint32_dec_eq(v___x_278_, v___x_306_);
if (v___x_307_ == 0)
{
uint32_t v___x_308_; uint8_t v___x_309_; 
v___x_308_ = 32;
v___x_309_ = lean_uint32_dec_lt(v___x_278_, v___x_308_);
if (v___x_309_ == 0)
{
uint32_t v___x_310_; uint8_t v___x_311_; 
v___x_310_ = 127;
v___x_311_ = lean_uint32_dec_eq(v___x_278_, v___x_310_);
v___y_280_ = v___x_311_;
goto v___jp_279_;
}
else
{
v___y_280_ = v___x_309_;
goto v___jp_279_;
}
}
else
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__1));
v___x_313_ = lean_string_append(v_b_272_, v___x_312_);
v_a_271_ = v___x_277_;
v_b_272_ = v___x_313_;
goto _start;
}
}
else
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__2));
v___x_316_ = lean_string_append(v_b_272_, v___x_315_);
v_a_271_ = v___x_277_;
v_b_272_ = v___x_316_;
goto _start;
}
}
else
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__3));
v___x_319_ = lean_string_append(v_b_272_, v___x_318_);
v_a_271_ = v___x_277_;
v_b_272_ = v___x_319_;
goto _start;
}
}
else
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__4));
v___x_322_ = lean_string_append(v_b_272_, v___x_321_);
v_a_271_ = v___x_277_;
v_b_272_ = v___x_322_;
goto _start;
}
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__5));
v___x_325_ = lean_string_append(v_b_272_, v___x_324_);
v_a_271_ = v___x_277_;
v_b_272_ = v___x_325_;
goto _start;
}
}
else
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__6));
v___x_328_ = lean_string_append(v_b_272_, v___x_327_);
v_a_271_ = v___x_277_;
v_b_272_ = v___x_328_;
goto _start;
}
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__7));
v___x_331_ = lean_string_append(v_b_272_, v___x_330_);
v_a_271_ = v___x_277_;
v_b_272_ = v___x_331_;
goto _start;
}
v___jp_279_:
{
if (v___y_280_ == 0)
{
lean_object* v___x_281_; 
v___x_281_ = lean_string_push(v_b_272_, v___x_278_);
v_a_271_ = v___x_277_;
v_b_272_ = v___x_281_;
goto _start;
}
else
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; uint32_t v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_283_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__0));
v___x_284_ = lean_string_append(v_b_272_, v___x_283_);
v___x_285_ = lean_unsigned_to_nat(16u);
v___x_286_ = lean_uint32_to_nat(v___x_278_);
v___x_287_ = l_Nat_toDigits(v___x_285_, v___x_286_);
v___x_288_ = lean_string_mk(v___x_287_);
v___x_289_ = 48;
v___x_290_ = lean_unsigned_to_nat(4u);
v___x_291_ = l_Lake_lpad(v___x_288_, v___x_289_, v___x_290_);
lean_dec_ref(v___x_288_);
v___x_292_ = lean_string_append(v___x_284_, v___x_291_);
lean_dec_ref(v___x_291_);
v_a_271_ = v___x_277_;
v_b_272_ = v___x_292_;
goto _start;
}
}
}
else
{
lean_dec(v_a_271_);
return v_b_272_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___boxed(lean_object* v___x_333_, lean_object* v_s_334_, lean_object* v_a_335_, lean_object* v_b_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg(v___x_333_, v_s_334_, v_a_335_, v_b_336_);
lean_dec_ref(v_s_334_);
lean_dec_ref(v___x_333_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppString(lean_object* v_s_339_){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v_s_345_; uint32_t v___x_346_; lean_object* v___x_347_; 
v___x_340_ = ((lean_object*)(l_Lake_Toml_ppString___closed__0));
v___x_341_ = lean_unsigned_to_nat(0u);
v___x_342_ = lean_string_utf8_byte_size(v_s_339_);
lean_inc_ref(v_s_339_);
v___x_343_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_343_, 0, v_s_339_);
lean_ctor_set(v___x_343_, 1, v___x_341_);
lean_ctor_set(v___x_343_, 2, v___x_342_);
v___x_344_ = l_String_Slice_positions(v___x_343_);
v_s_345_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg(v___x_343_, v_s_339_, v___x_344_, v___x_340_);
lean_dec_ref(v_s_339_);
lean_dec_ref(v___x_343_);
v___x_346_ = 34;
v___x_347_ = lean_string_push(v_s_345_, v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0(lean_object* v___x_348_, lean_object* v_s_349_, lean_object* v_inst_350_, lean_object* v_R_351_, lean_object* v_a_352_, lean_object* v_b_353_, lean_object* v_c_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg(v___x_348_, v_s_349_, v_a_352_, v_b_353_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___boxed(lean_object* v___x_356_, lean_object* v_s_357_, lean_object* v_inst_358_, lean_object* v_R_359_, lean_object* v_a_360_, lean_object* v_b_361_, lean_object* v_c_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0(v___x_356_, v_s_357_, v_inst_358_, v_R_359_, v_a_360_, v_b_361_, v_c_362_);
lean_dec_ref(v_s_357_);
lean_dec_ref(v___x_356_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Toml_ppSimpleKey_spec__0(lean_object* v_s_364_, lean_object* v_curr_365_){
_start:
{
lean_object* v_str_366_; lean_object* v_startInclusive_367_; lean_object* v_endExclusive_368_; lean_object* v___x_369_; lean_object* v___x_370_; uint8_t v___y_378_; lean_object* v___x_379_; lean_object* v___x_380_; uint8_t v___x_381_; 
v_str_366_ = lean_ctor_get(v_s_364_, 0);
v_startInclusive_367_ = lean_ctor_get(v_s_364_, 1);
v_endExclusive_368_ = lean_ctor_get(v_s_364_, 2);
v___x_369_ = lean_nat_add(v_startInclusive_367_, v_curr_365_);
lean_inc(v_endExclusive_368_);
lean_inc(v___x_369_);
lean_inc_ref(v_str_366_);
v___x_370_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_370_, 0, v_str_366_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
lean_ctor_set(v___x_370_, 2, v_endExclusive_368_);
v___x_379_ = lean_unsigned_to_nat(0u);
v___x_380_ = lean_nat_sub(v_endExclusive_368_, v___x_369_);
v___x_381_ = lean_nat_dec_eq(v___x_379_, v___x_380_);
lean_dec(v___x_380_);
if (v___x_381_ == 0)
{
uint32_t v___x_382_; uint8_t v___y_384_; uint8_t v___y_390_; uint32_t v___x_400_; uint8_t v___x_401_; 
v___x_382_ = lean_string_utf8_get_fast(v_str_366_, v___x_369_);
v___x_400_ = 65;
v___x_401_ = lean_uint32_dec_le(v___x_400_, v___x_382_);
if (v___x_401_ == 0)
{
goto v___jp_395_;
}
else
{
uint32_t v___x_402_; uint8_t v___x_403_; 
v___x_402_ = 90;
v___x_403_ = lean_uint32_dec_le(v___x_382_, v___x_402_);
if (v___x_403_ == 0)
{
goto v___jp_395_;
}
else
{
goto v___jp_371_;
}
}
v___jp_383_:
{
if (v___y_384_ == 0)
{
uint32_t v___x_385_; uint8_t v___x_386_; 
v___x_385_ = 95;
v___x_386_ = lean_uint32_dec_eq(v___x_382_, v___x_385_);
if (v___x_386_ == 0)
{
uint32_t v___x_387_; uint8_t v___x_388_; 
v___x_387_ = 45;
v___x_388_ = lean_uint32_dec_eq(v___x_382_, v___x_387_);
v___y_378_ = v___x_388_;
goto v___jp_377_;
}
else
{
v___y_378_ = v___x_386_;
goto v___jp_377_;
}
}
else
{
goto v___jp_371_;
}
}
v___jp_389_:
{
if (v___y_390_ == 0)
{
uint32_t v___x_391_; uint8_t v___x_392_; 
v___x_391_ = 48;
v___x_392_ = lean_uint32_dec_le(v___x_391_, v___x_382_);
if (v___x_392_ == 0)
{
v___y_384_ = v___x_392_;
goto v___jp_383_;
}
else
{
uint32_t v___x_393_; uint8_t v___x_394_; 
v___x_393_ = 57;
v___x_394_ = lean_uint32_dec_le(v___x_382_, v___x_393_);
v___y_384_ = v___x_394_;
goto v___jp_383_;
}
}
else
{
goto v___jp_371_;
}
}
v___jp_395_:
{
uint32_t v___x_396_; uint8_t v___x_397_; 
v___x_396_ = 97;
v___x_397_ = lean_uint32_dec_le(v___x_396_, v___x_382_);
if (v___x_397_ == 0)
{
v___y_390_ = v___x_397_;
goto v___jp_389_;
}
else
{
uint32_t v___x_398_; uint8_t v___x_399_; 
v___x_398_ = 122;
v___x_399_ = lean_uint32_dec_le(v___x_382_, v___x_398_);
v___y_390_ = v___x_399_;
goto v___jp_389_;
}
}
}
else
{
lean_dec(v___x_369_);
lean_dec(v_curr_365_);
return v___x_370_;
}
v___jp_371_:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_372_ = lean_string_utf8_next_fast(v_str_366_, v___x_369_);
v___x_373_ = lean_nat_sub(v___x_372_, v___x_369_);
lean_dec(v___x_369_);
v___x_374_ = lean_nat_add(v_curr_365_, v___x_373_);
lean_dec(v___x_373_);
v___x_375_ = lean_nat_dec_lt(v_curr_365_, v___x_374_);
lean_dec(v_curr_365_);
if (v___x_375_ == 0)
{
lean_dec(v___x_374_);
return v___x_370_;
}
else
{
lean_dec_ref(v___x_370_);
v_curr_365_ = v___x_374_;
goto _start;
}
}
v___jp_377_:
{
if (v___y_378_ == 0)
{
lean_dec(v___x_369_);
lean_dec(v_curr_365_);
return v___x_370_;
}
else
{
goto v___jp_371_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Toml_ppSimpleKey_spec__0___boxed(lean_object* v_s_404_, lean_object* v_curr_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Toml_ppSimpleKey_spec__0(v_s_404_, v_curr_405_);
lean_dec_ref(v_s_404_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppSimpleKey(lean_object* v_k_407_){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v_startInclusive_412_; lean_object* v_endExclusive_413_; lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_408_ = lean_unsigned_to_nat(0u);
v___x_409_ = lean_string_utf8_byte_size(v_k_407_);
lean_inc_ref(v_k_407_);
v___x_410_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_410_, 0, v_k_407_);
lean_ctor_set(v___x_410_, 1, v___x_408_);
lean_ctor_set(v___x_410_, 2, v___x_409_);
v___x_411_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Toml_ppSimpleKey_spec__0(v___x_410_, v___x_408_);
lean_dec_ref(v___x_410_);
v_startInclusive_412_ = lean_ctor_get(v___x_411_, 1);
lean_inc(v_startInclusive_412_);
v_endExclusive_413_ = lean_ctor_get(v___x_411_, 2);
lean_inc(v_endExclusive_413_);
lean_dec_ref(v___x_411_);
v___x_414_ = lean_nat_sub(v_endExclusive_413_, v_startInclusive_412_);
lean_dec(v_startInclusive_412_);
lean_dec(v_endExclusive_413_);
v___x_415_ = lean_nat_dec_eq(v___x_414_, v___x_408_);
lean_dec(v___x_414_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; 
v___x_416_ = l_Lake_Toml_ppString(v_k_407_);
return v___x_416_;
}
else
{
return v_k_407_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppKey(lean_object* v_k_418_){
_start:
{
if (lean_obj_tag(v_k_418_) == 1)
{
lean_object* v_pre_419_; lean_object* v_str_420_; uint8_t v___x_421_; 
v_pre_419_ = lean_ctor_get(v_k_418_, 0);
lean_inc(v_pre_419_);
v_str_420_ = lean_ctor_get(v_k_418_, 1);
lean_inc_ref(v_str_420_);
lean_dec_ref(v_k_418_);
v___x_421_ = l_Lean_Name_isAnonymous(v_pre_419_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_422_ = l_Lake_Toml_ppKey(v_pre_419_);
v___x_423_ = ((lean_object*)(l_Lake_Toml_ppKey___closed__0));
v___x_424_ = lean_string_append(v___x_422_, v___x_423_);
v___x_425_ = l_Lake_Toml_ppSimpleKey(v_str_420_);
v___x_426_ = lean_string_append(v___x_424_, v___x_425_);
lean_dec_ref(v___x_425_);
return v___x_426_;
}
else
{
lean_object* v___x_427_; 
lean_dec(v_pre_419_);
v___x_427_ = l_Lake_Toml_ppSimpleKey(v_str_420_);
return v___x_427_;
}
}
else
{
lean_object* v___x_428_; 
lean_dec(v_k_418_);
v___x_428_ = ((lean_object*)(l_Lake_Toml_instInhabitedValue_default___closed__0));
return v___x_428_;
}
}
}
static lean_object* _init_l_Lake_Toml_Value_toString___closed__0(void){
_start:
{
lean_object* v_natZero_432_; lean_object* v_intZero_433_; 
v_natZero_432_ = lean_unsigned_to_nat(0u);
v_intZero_433_ = lean_nat_to_int(v_natZero_432_);
return v_intZero_433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0(size_t v_sz_438_, size_t v_i_439_, lean_object* v_bs_440_){
_start:
{
uint8_t v___x_441_; 
v___x_441_ = lean_usize_dec_lt(v_i_439_, v_sz_438_);
if (v___x_441_ == 0)
{
return v_bs_440_;
}
else
{
lean_object* v_v_442_; lean_object* v_fst_443_; lean_object* v_snd_444_; lean_object* v___x_445_; lean_object* v_bs_x27_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; size_t v___x_452_; size_t v___x_453_; lean_object* v___x_454_; 
v_v_442_ = lean_array_uget_borrowed(v_bs_440_, v_i_439_);
v_fst_443_ = lean_ctor_get(v_v_442_, 0);
lean_inc(v_fst_443_);
v_snd_444_ = lean_ctor_get(v_v_442_, 1);
lean_inc(v_snd_444_);
v___x_445_ = lean_unsigned_to_nat(0u);
v_bs_x27_446_ = lean_array_uset(v_bs_440_, v_i_439_, v___x_445_);
v___x_447_ = l_Lake_Toml_ppKey(v_fst_443_);
v___x_448_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___closed__0));
v___x_449_ = lean_string_append(v___x_447_, v___x_448_);
v___x_450_ = l_Lake_Toml_Value_toString(v_snd_444_);
v___x_451_ = lean_string_append(v___x_449_, v___x_450_);
lean_dec_ref(v___x_450_);
v___x_452_ = ((size_t)1ULL);
v___x_453_ = lean_usize_add(v_i_439_, v___x_452_);
v___x_454_ = lean_array_uset(v_bs_x27_446_, v_i_439_, v___x_451_);
v_i_439_ = v___x_453_;
v_bs_440_ = v___x_454_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppInlineTable(lean_object* v_t_458_){
_start:
{
lean_object* v_items_459_; size_t v_sz_460_; size_t v___x_461_; lean_object* v_xs_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v_items_459_ = lean_ctor_get(v_t_458_, 0);
lean_inc_ref(v_items_459_);
lean_dec_ref(v_t_458_);
v_sz_460_ = lean_array_size(v_items_459_);
v___x_461_ = ((size_t)0ULL);
v_xs_462_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0(v_sz_460_, v___x_461_, v_items_459_);
v___x_463_ = ((lean_object*)(l_Lake_Toml_ppInlineTable___closed__0));
v___x_464_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__1));
v___x_465_ = lean_array_to_list(v_xs_462_);
v___x_466_ = l_String_intercalate(v___x_464_, v___x_465_);
v___x_467_ = lean_string_append(v___x_463_, v___x_466_);
lean_dec_ref(v___x_466_);
v___x_468_ = ((lean_object*)(l_Lake_Toml_ppInlineTable___closed__1));
v___x_469_ = lean_string_append(v___x_467_, v___x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_toString(lean_object* v_v_470_){
_start:
{
switch(lean_obj_tag(v_v_470_))
{
case 0:
{
lean_object* v_s_471_; lean_object* v___x_472_; 
v_s_471_ = lean_ctor_get(v_v_470_, 1);
lean_inc_ref(v_s_471_);
lean_dec_ref(v_v_470_);
v___x_472_ = l_Lake_Toml_ppString(v_s_471_);
return v___x_472_;
}
case 1:
{
lean_object* v_n_473_; lean_object* v_intZero_474_; uint8_t v_isNeg_475_; 
v_n_473_ = lean_ctor_get(v_v_470_, 1);
lean_inc(v_n_473_);
lean_dec_ref(v_v_470_);
v_intZero_474_ = lean_obj_once(&l_Lake_Toml_Value_toString___closed__0, &l_Lake_Toml_Value_toString___closed__0_once, _init_l_Lake_Toml_Value_toString___closed__0);
v_isNeg_475_ = lean_int_dec_lt(v_n_473_, v_intZero_474_);
if (v_isNeg_475_ == 0)
{
lean_object* v_a_476_; lean_object* v___x_477_; 
v_a_476_ = lean_nat_abs(v_n_473_);
lean_dec(v_n_473_);
v___x_477_ = l_Nat_reprFast(v_a_476_);
return v___x_477_;
}
else
{
lean_object* v_abs_478_; lean_object* v_one_479_; lean_object* v_a_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_abs_478_ = lean_nat_abs(v_n_473_);
lean_dec(v_n_473_);
v_one_479_ = lean_unsigned_to_nat(1u);
v_a_480_ = lean_nat_sub(v_abs_478_, v_one_479_);
lean_dec(v_abs_478_);
v___x_481_ = ((lean_object*)(l_Lake_Toml_Value_toString___closed__1));
v___x_482_ = lean_nat_add(v_a_480_, v_one_479_);
lean_dec(v_a_480_);
v___x_483_ = l_Nat_reprFast(v___x_482_);
v___x_484_ = lean_string_append(v___x_481_, v___x_483_);
lean_dec_ref(v___x_483_);
return v___x_484_;
}
}
case 2:
{
double v_n_485_; lean_object* v___x_486_; 
v_n_485_ = lean_ctor_get_float(v_v_470_, sizeof(void*)*1);
lean_dec_ref(v_v_470_);
v___x_486_ = lean_float_to_string(v_n_485_);
return v___x_486_;
}
case 3:
{
uint8_t v_b_487_; 
v_b_487_ = lean_ctor_get_uint8(v_v_470_, sizeof(void*)*1);
lean_dec_ref(v_v_470_);
if (v_b_487_ == 0)
{
lean_object* v___x_488_; 
v___x_488_ = ((lean_object*)(l_Lake_Toml_Value_toString___closed__2));
return v___x_488_;
}
else
{
lean_object* v___x_489_; 
v___x_489_ = ((lean_object*)(l_Lake_Toml_Value_toString___closed__3));
return v___x_489_;
}
}
case 4:
{
lean_object* v_dt_490_; lean_object* v___x_491_; 
v_dt_490_ = lean_ctor_get(v_v_470_, 1);
lean_inc_ref(v_dt_490_);
lean_dec_ref(v_v_470_);
v___x_491_ = l_Lake_Toml_DateTime_toString(v_dt_490_);
return v___x_491_;
}
case 5:
{
lean_object* v_xs_492_; lean_object* v___x_493_; 
v_xs_492_ = lean_ctor_get(v_v_470_, 1);
lean_inc_ref(v_xs_492_);
lean_dec_ref(v_v_470_);
v___x_493_ = l_Lake_Toml_ppInlineArray(v_xs_492_);
return v___x_493_;
}
default: 
{
lean_object* v_xs_494_; lean_object* v___x_495_; 
v_xs_494_ = lean_ctor_get(v_v_470_, 1);
lean_inc_ref(v_xs_494_);
lean_dec_ref(v_v_470_);
v___x_495_ = l_Lake_Toml_ppInlineTable(v_xs_494_);
return v___x_495_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3(size_t v_sz_496_, size_t v_i_497_, lean_object* v_bs_498_){
_start:
{
uint8_t v___x_499_; 
v___x_499_ = lean_usize_dec_lt(v_i_497_, v_sz_496_);
if (v___x_499_ == 0)
{
return v_bs_498_;
}
else
{
lean_object* v_v_500_; lean_object* v___x_501_; lean_object* v_bs_x27_502_; lean_object* v___x_503_; size_t v___x_504_; size_t v___x_505_; lean_object* v___x_506_; 
v_v_500_ = lean_array_uget(v_bs_498_, v_i_497_);
v___x_501_ = lean_unsigned_to_nat(0u);
v_bs_x27_502_ = lean_array_uset(v_bs_498_, v_i_497_, v___x_501_);
v___x_503_ = l_Lake_Toml_Value_toString(v_v_500_);
v___x_504_ = ((size_t)1ULL);
v___x_505_ = lean_usize_add(v_i_497_, v___x_504_);
v___x_506_ = lean_array_uset(v_bs_x27_502_, v_i_497_, v___x_503_);
v_i_497_ = v___x_505_;
v_bs_498_ = v___x_506_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppInlineArray(lean_object* v_vs_508_){
_start:
{
size_t v_sz_509_; size_t v___x_510_; lean_object* v_xs_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v_sz_509_ = lean_array_size(v_vs_508_);
v___x_510_ = ((size_t)0ULL);
v_xs_511_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3(v_sz_509_, v___x_510_, v_vs_508_);
v___x_512_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__0));
v___x_513_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__1));
v___x_514_ = lean_array_to_list(v_xs_511_);
v___x_515_ = l_String_intercalate(v___x_513_, v___x_514_);
v___x_516_ = lean_string_append(v___x_512_, v___x_515_);
lean_dec_ref(v___x_515_);
v___x_517_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__2));
v___x_518_ = lean_string_append(v___x_516_, v___x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3___boxed(lean_object* v_sz_519_, lean_object* v_i_520_, lean_object* v_bs_521_){
_start:
{
size_t v_sz_boxed_522_; size_t v_i_boxed_523_; lean_object* v_res_524_; 
v_sz_boxed_522_ = lean_unbox_usize(v_sz_519_);
lean_dec(v_sz_519_);
v_i_boxed_523_ = lean_unbox_usize(v_i_520_);
lean_dec(v_i_520_);
v_res_524_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3(v_sz_boxed_522_, v_i_boxed_523_, v_bs_521_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___boxed(lean_object* v_sz_525_, lean_object* v_i_526_, lean_object* v_bs_527_){
_start:
{
size_t v_sz_boxed_528_; size_t v_i_boxed_529_; lean_object* v_res_530_; 
v_sz_boxed_528_ = lean_unbox_usize(v_sz_525_);
lean_dec(v_sz_525_);
v_i_boxed_529_ = lean_unbox_usize(v_i_526_);
lean_dec(v_i_526_);
v_res_530_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0(v_sz_boxed_528_, v_i_boxed_529_, v_bs_527_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval(lean_object* v_s_534_, lean_object* v_k_535_, lean_object* v_v_536_){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_537_ = l_Lake_Toml_ppKey(v_k_535_);
v___x_538_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___closed__0));
v___x_539_ = lean_string_append(v___x_537_, v___x_538_);
v___x_540_ = l_Lake_Toml_Value_toString(v_v_536_);
v___x_541_ = lean_string_append(v___x_539_, v___x_540_);
lean_dec_ref(v___x_540_);
v___x_542_ = ((lean_object*)(l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval___closed__0));
v___x_543_ = lean_string_append(v___x_541_, v___x_542_);
v___x_544_ = lean_string_append(v_s_534_, v___x_543_);
lean_dec_ref(v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lake_Toml_ppTable_spec__2(lean_object* v_msg_545_){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = ((lean_object*)(l_Lake_Toml_instInhabitedValue_default___closed__0));
v___x_547_ = lean_panic_fn(v___x_546_, v_msg_545_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(lean_object* v_as_548_, size_t v_i_549_, size_t v_stop_550_, lean_object* v_b_551_){
_start:
{
uint8_t v___x_552_; 
v___x_552_ = lean_usize_dec_eq(v_i_549_, v_stop_550_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; lean_object* v_fst_554_; lean_object* v_snd_555_; lean_object* v___x_556_; size_t v___x_557_; size_t v___x_558_; 
v___x_553_ = lean_array_uget_borrowed(v_as_548_, v_i_549_);
v_fst_554_ = lean_ctor_get(v___x_553_, 0);
v_snd_555_ = lean_ctor_get(v___x_553_, 1);
lean_inc(v_snd_555_);
lean_inc(v_fst_554_);
v___x_556_ = l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval(v_b_551_, v_fst_554_, v_snd_555_);
v___x_557_ = ((size_t)1ULL);
v___x_558_ = lean_usize_add(v_i_549_, v___x_557_);
v_i_549_ = v___x_558_;
v_b_551_ = v___x_556_;
goto _start;
}
else
{
return v_b_551_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1___boxed(lean_object* v_as_560_, lean_object* v_i_561_, lean_object* v_stop_562_, lean_object* v_b_563_){
_start:
{
size_t v_i_boxed_564_; size_t v_stop_boxed_565_; lean_object* v_res_566_; 
v_i_boxed_564_ = lean_unbox_usize(v_i_561_);
lean_dec(v_i_561_);
v_stop_boxed_565_ = lean_unbox_usize(v_stop_562_);
lean_dec(v_stop_562_);
v_res_566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_as_560_, v_i_boxed_564_, v_stop_boxed_565_, v_b_563_);
lean_dec_ref(v_as_560_);
return v_res_566_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_572_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__4));
v___x_573_ = lean_unsigned_to_nat(17u);
v___x_574_ = lean_unsigned_to_nat(128u);
v___x_575_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__3));
v___x_576_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__2));
v___x_577_ = l_mkPanicMessageWithDecl(v___x_576_, v___x_575_, v___x_574_, v___x_573_, v___x_572_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3(lean_object* v_fst_578_, lean_object* v_as_579_, size_t v_i_580_, size_t v_stop_581_, lean_object* v_b_582_){
_start:
{
lean_object* v___y_584_; lean_object* v___y_589_; uint8_t v___x_592_; 
v___x_592_ = lean_usize_dec_eq(v_i_580_, v_stop_581_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; 
v___x_593_ = lean_array_uget_borrowed(v_as_579_, v_i_580_);
if (lean_obj_tag(v___x_593_) == 6)
{
lean_object* v_xs_594_; lean_object* v_items_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v_s_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v_xs_594_ = lean_ctor_get(v___x_593_, 1);
v_items_595_ = lean_ctor_get(v_xs_594_, 0);
v___x_596_ = lean_unsigned_to_nat(0u);
v___x_597_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__0));
lean_inc(v_fst_578_);
v___x_598_ = l_Lake_Toml_ppKey(v_fst_578_);
v___x_599_ = lean_string_append(v___x_597_, v___x_598_);
lean_dec_ref(v___x_598_);
v___x_600_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__1));
v___x_601_ = lean_string_append(v___x_599_, v___x_600_);
v_s_602_ = lean_string_append(v_b_582_, v___x_601_);
lean_dec_ref(v___x_601_);
v___x_603_ = lean_array_get_size(v_items_595_);
v___x_604_ = lean_nat_dec_lt(v___x_596_, v___x_603_);
if (v___x_604_ == 0)
{
v___y_589_ = v_s_602_;
goto v___jp_588_;
}
else
{
uint8_t v___x_605_; 
v___x_605_ = lean_nat_dec_le(v___x_603_, v___x_603_);
if (v___x_605_ == 0)
{
if (v___x_604_ == 0)
{
v___y_589_ = v_s_602_;
goto v___jp_588_;
}
else
{
size_t v___x_606_; size_t v___x_607_; lean_object* v___x_608_; 
v___x_606_ = ((size_t)0ULL);
v___x_607_ = lean_usize_of_nat(v___x_603_);
v___x_608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_items_595_, v___x_606_, v___x_607_, v_s_602_);
v___y_589_ = v___x_608_;
goto v___jp_588_;
}
}
else
{
size_t v___x_609_; size_t v___x_610_; lean_object* v___x_611_; 
v___x_609_ = ((size_t)0ULL);
v___x_610_ = lean_usize_of_nat(v___x_603_);
v___x_611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_items_595_, v___x_609_, v___x_610_, v_s_602_);
v___y_589_ = v___x_611_;
goto v___jp_588_;
}
}
}
else
{
lean_object* v___x_612_; lean_object* v___x_613_; 
lean_dec_ref(v_b_582_);
v___x_612_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5);
v___x_613_ = l_panic___at___00Lake_Toml_ppTable_spec__2(v___x_612_);
v___y_584_ = v___x_613_;
goto v___jp_583_;
}
}
else
{
lean_dec(v_fst_578_);
return v_b_582_;
}
v___jp_583_:
{
size_t v___x_585_; size_t v___x_586_; 
v___x_585_ = ((size_t)1ULL);
v___x_586_ = lean_usize_add(v_i_580_, v___x_585_);
v_i_580_ = v___x_586_;
v_b_582_ = v___y_584_;
goto _start;
}
v___jp_588_:
{
uint32_t v___x_590_; lean_object* v___x_591_; 
v___x_590_ = 10;
v___x_591_ = lean_string_push(v___y_589_, v___x_590_);
v___y_584_ = v___x_591_;
goto v___jp_583_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___boxed(lean_object* v_fst_614_, lean_object* v_as_615_, lean_object* v_i_616_, lean_object* v_stop_617_, lean_object* v_b_618_){
_start:
{
size_t v_i_boxed_619_; size_t v_stop_boxed_620_; lean_object* v_res_621_; 
v_i_boxed_619_ = lean_unbox_usize(v_i_616_);
lean_dec(v_i_616_);
v_stop_boxed_620_ = lean_unbox_usize(v_stop_617_);
lean_dec(v_stop_617_);
v_res_621_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3(v_fst_614_, v_as_615_, v_i_boxed_619_, v_stop_boxed_620_, v_b_618_);
lean_dec_ref(v_as_615_);
return v_res_621_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Toml_ppTable_spec__4(lean_object* v___x_622_, lean_object* v_as_623_, size_t v_i_624_, size_t v_stop_625_){
_start:
{
uint8_t v___x_626_; 
v___x_626_ = lean_usize_dec_eq(v_i_624_, v_stop_625_);
if (v___x_626_ == 0)
{
uint8_t v___x_627_; lean_object* v___x_628_; 
v___x_627_ = 1;
v___x_628_ = lean_array_uget_borrowed(v_as_623_, v_i_624_);
if (lean_obj_tag(v___x_628_) == 6)
{
lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_629_ = lean_unsigned_to_nat(0u);
v___x_630_ = lean_nat_dec_eq(v___x_622_, v___x_629_);
if (v___x_630_ == 0)
{
size_t v___x_631_; size_t v___x_632_; 
v___x_631_ = ((size_t)1ULL);
v___x_632_ = lean_usize_add(v_i_624_, v___x_631_);
v_i_624_ = v___x_632_;
goto _start;
}
else
{
return v___x_627_;
}
}
else
{
return v___x_627_;
}
}
else
{
uint8_t v___x_634_; 
v___x_634_ = 0;
return v___x_634_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Toml_ppTable_spec__4___boxed(lean_object* v___x_635_, lean_object* v_as_636_, lean_object* v_i_637_, lean_object* v_stop_638_){
_start:
{
size_t v_i_boxed_639_; size_t v_stop_boxed_640_; uint8_t v_res_641_; lean_object* v_r_642_; 
v_i_boxed_639_ = lean_unbox_usize(v_i_637_);
lean_dec(v_i_637_);
v_stop_boxed_640_ = lean_unbox_usize(v_stop_638_);
lean_dec(v_stop_638_);
v_res_641_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Toml_ppTable_spec__4(v___x_635_, v_as_636_, v_i_boxed_639_, v_stop_boxed_640_);
lean_dec_ref(v_as_636_);
lean_dec(v___x_635_);
v_r_642_ = lean_box(v_res_641_);
return v_r_642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5(lean_object* v_as_645_, size_t v_i_646_, size_t v_stop_647_, lean_object* v_b_648_){
_start:
{
lean_object* v___y_650_; uint8_t v___x_654_; 
v___x_654_ = lean_usize_dec_eq(v_i_646_, v_stop_647_);
if (v___x_654_ == 0)
{
lean_object* v_fst_655_; lean_object* v_snd_656_; lean_object* v___y_658_; lean_object* v___x_662_; lean_object* v_snd_663_; 
v_fst_655_ = lean_ctor_get(v_b_648_, 0);
v_snd_656_ = lean_ctor_get(v_b_648_, 1);
v___x_662_ = lean_array_uget(v_as_645_, v_i_646_);
v_snd_663_ = lean_ctor_get(v___x_662_, 1);
switch(lean_obj_tag(v_snd_663_))
{
case 5:
{
lean_object* v_fst_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_721_; 
lean_inc_ref(v_snd_663_);
v_fst_664_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_721_ == 0)
{
lean_object* v_unused_722_; 
v_unused_722_ = lean_ctor_get(v___x_662_, 1);
lean_dec(v_unused_722_);
v___x_666_ = v___x_662_;
v_isShared_667_ = v_isSharedCheck_721_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_fst_664_);
lean_dec(v___x_662_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_721_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v_xs_668_; lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_686_; 
v_xs_668_ = lean_ctor_get(v_snd_663_, 1);
lean_inc_ref(v_xs_668_);
lean_dec_ref(v_snd_663_);
v___x_669_ = lean_array_get_size(v_xs_668_);
v___x_670_ = lean_unsigned_to_nat(0u);
v___x_686_ = lean_nat_dec_eq(v___x_669_, v___x_670_);
if (v___x_686_ == 0)
{
uint8_t v___x_687_; 
v___x_687_ = lean_nat_dec_lt(v___x_670_, v___x_669_);
if (v___x_687_ == 0)
{
goto v___jp_671_;
}
else
{
if (v___x_687_ == 0)
{
goto v___jp_671_;
}
else
{
size_t v___x_688_; size_t v___x_689_; uint8_t v___x_690_; 
v___x_688_ = ((size_t)0ULL);
v___x_689_ = lean_usize_of_nat(v___x_669_);
v___x_690_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Toml_ppTable_spec__4(v___x_669_, v_xs_668_, v___x_688_, v___x_689_);
if (v___x_690_ == 0)
{
goto v___jp_671_;
}
else
{
if (v___x_686_ == 0)
{
lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_705_; 
lean_inc(v_snd_656_);
lean_inc(v_fst_655_);
lean_del_object(v___x_666_);
v_isSharedCheck_705_ = !lean_is_exclusive(v_b_648_);
if (v_isSharedCheck_705_ == 0)
{
lean_object* v_unused_706_; lean_object* v_unused_707_; 
v_unused_706_ = lean_ctor_get(v_b_648_, 1);
lean_dec(v_unused_706_);
v_unused_707_ = lean_ctor_get(v_b_648_, 0);
lean_dec(v_unused_707_);
v___x_692_ = v_b_648_;
v_isShared_693_ = v_isSharedCheck_705_;
goto v_resetjp_691_;
}
else
{
lean_dec(v_b_648_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_705_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_694_ = l_Lake_Toml_ppKey(v_fst_664_);
v___x_695_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___closed__0));
v___x_696_ = lean_string_append(v___x_694_, v___x_695_);
v___x_697_ = l_Lake_Toml_ppInlineArray(v_xs_668_);
v___x_698_ = lean_string_append(v___x_696_, v___x_697_);
lean_dec_ref(v___x_697_);
v___x_699_ = ((lean_object*)(l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval___closed__0));
v___x_700_ = lean_string_append(v___x_698_, v___x_699_);
v___x_701_ = lean_string_append(v_fst_655_, v___x_700_);
lean_dec_ref(v___x_700_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v___x_701_);
v___x_703_ = v___x_692_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_701_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_snd_656_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
v___y_650_ = v___x_703_;
goto v___jp_649_;
}
}
}
else
{
goto v___jp_671_;
}
}
}
}
}
else
{
lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_718_; 
lean_inc(v_snd_656_);
lean_inc(v_fst_655_);
lean_dec_ref(v_xs_668_);
lean_del_object(v___x_666_);
v_isSharedCheck_718_ = !lean_is_exclusive(v_b_648_);
if (v_isSharedCheck_718_ == 0)
{
lean_object* v_unused_719_; lean_object* v_unused_720_; 
v_unused_719_ = lean_ctor_get(v_b_648_, 1);
lean_dec(v_unused_719_);
v_unused_720_ = lean_ctor_get(v_b_648_, 0);
lean_dec(v_unused_720_);
v___x_709_ = v_b_648_;
v_isShared_710_ = v_isSharedCheck_718_;
goto v_resetjp_708_;
}
else
{
lean_dec(v_b_648_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_718_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_711_ = l_Lake_Toml_ppKey(v_fst_664_);
v___x_712_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___closed__0));
v___x_713_ = lean_string_append(v___x_711_, v___x_712_);
v___x_714_ = lean_string_append(v_fst_655_, v___x_713_);
lean_dec_ref(v___x_713_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v___x_714_);
v___x_716_ = v___x_709_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_snd_656_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
v___y_650_ = v___x_716_;
goto v___jp_649_;
}
}
}
v___jp_671_:
{
uint8_t v___x_672_; 
v___x_672_ = lean_nat_dec_lt(v___x_670_, v___x_669_);
if (v___x_672_ == 0)
{
lean_dec_ref(v_xs_668_);
lean_del_object(v___x_666_);
lean_dec(v_fst_664_);
v___y_650_ = v_b_648_;
goto v___jp_649_;
}
else
{
uint8_t v___x_673_; 
v___x_673_ = lean_nat_dec_le(v___x_669_, v___x_669_);
if (v___x_673_ == 0)
{
if (v___x_672_ == 0)
{
lean_dec_ref(v_xs_668_);
lean_del_object(v___x_666_);
lean_dec(v_fst_664_);
v___y_650_ = v_b_648_;
goto v___jp_649_;
}
else
{
size_t v___x_674_; size_t v___x_675_; lean_object* v___x_676_; lean_object* v___x_678_; 
lean_inc(v_snd_656_);
lean_inc(v_fst_655_);
lean_dec_ref(v_b_648_);
v___x_674_ = ((size_t)0ULL);
v___x_675_ = lean_usize_of_nat(v___x_669_);
v___x_676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3(v_fst_664_, v_xs_668_, v___x_674_, v___x_675_, v_snd_656_);
lean_dec_ref(v_xs_668_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 1, v___x_676_);
lean_ctor_set(v___x_666_, 0, v_fst_655_);
v___x_678_ = v___x_666_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_fst_655_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v___x_676_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
v___y_650_ = v___x_678_;
goto v___jp_649_;
}
}
}
else
{
size_t v___x_680_; size_t v___x_681_; lean_object* v___x_682_; lean_object* v___x_684_; 
lean_inc(v_snd_656_);
lean_inc(v_fst_655_);
lean_dec_ref(v_b_648_);
v___x_680_ = ((size_t)0ULL);
v___x_681_ = lean_usize_of_nat(v___x_669_);
v___x_682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3(v_fst_664_, v_xs_668_, v___x_680_, v___x_681_, v_snd_656_);
lean_dec_ref(v_xs_668_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 1, v___x_682_);
lean_ctor_set(v___x_666_, 0, v_fst_655_);
v___x_684_ = v___x_666_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_fst_655_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v___x_682_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
v___y_650_ = v___x_684_;
goto v___jp_649_;
}
}
}
}
}
}
case 6:
{
lean_object* v_xs_723_; lean_object* v_fst_724_; lean_object* v_items_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v_fs_731_; lean_object* v___x_732_; lean_object* v___x_733_; uint8_t v___x_734_; 
lean_inc(v_snd_656_);
lean_inc(v_fst_655_);
lean_dec_ref(v_b_648_);
v_xs_723_ = lean_ctor_get(v_snd_663_, 1);
lean_inc_ref(v_xs_723_);
v_fst_724_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_fst_724_);
lean_dec(v___x_662_);
v_items_725_ = lean_ctor_get(v_xs_723_, 0);
lean_inc_ref(v_items_725_);
lean_dec_ref(v_xs_723_);
v___x_726_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__0));
v___x_727_ = l_Lake_Toml_ppKey(v_fst_724_);
v___x_728_ = lean_string_append(v___x_726_, v___x_727_);
lean_dec_ref(v___x_727_);
v___x_729_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___closed__1));
v___x_730_ = lean_string_append(v___x_728_, v___x_729_);
v_fs_731_ = lean_string_append(v_snd_656_, v___x_730_);
lean_dec_ref(v___x_730_);
v___x_732_ = lean_unsigned_to_nat(0u);
v___x_733_ = lean_array_get_size(v_items_725_);
v___x_734_ = lean_nat_dec_lt(v___x_732_, v___x_733_);
if (v___x_734_ == 0)
{
lean_dec_ref(v_items_725_);
v___y_658_ = v_fs_731_;
goto v___jp_657_;
}
else
{
uint8_t v___x_735_; 
v___x_735_ = lean_nat_dec_le(v___x_733_, v___x_733_);
if (v___x_735_ == 0)
{
if (v___x_734_ == 0)
{
lean_dec_ref(v_items_725_);
v___y_658_ = v_fs_731_;
goto v___jp_657_;
}
else
{
size_t v___x_736_; size_t v___x_737_; lean_object* v___x_738_; 
v___x_736_ = ((size_t)0ULL);
v___x_737_ = lean_usize_of_nat(v___x_733_);
v___x_738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_items_725_, v___x_736_, v___x_737_, v_fs_731_);
lean_dec_ref(v_items_725_);
v___y_658_ = v___x_738_;
goto v___jp_657_;
}
}
else
{
size_t v___x_739_; size_t v___x_740_; lean_object* v___x_741_; 
v___x_739_ = ((size_t)0ULL);
v___x_740_ = lean_usize_of_nat(v___x_733_);
v___x_741_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_items_725_, v___x_739_, v___x_740_, v_fs_731_);
lean_dec_ref(v_items_725_);
v___y_658_ = v___x_741_;
goto v___jp_657_;
}
}
}
default: 
{
lean_object* v_fst_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_750_; 
lean_inc(v_snd_663_);
lean_inc(v_snd_656_);
lean_inc(v_fst_655_);
lean_dec_ref(v_b_648_);
v_fst_742_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_750_ == 0)
{
lean_object* v_unused_751_; 
v_unused_751_ = lean_ctor_get(v___x_662_, 1);
lean_dec(v_unused_751_);
v___x_744_ = v___x_662_;
v_isShared_745_ = v_isSharedCheck_750_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_fst_742_);
lean_dec(v___x_662_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_750_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; lean_object* v___x_748_; 
v___x_746_ = l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval(v_fst_655_, v_fst_742_, v_snd_663_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 1, v_snd_656_);
lean_ctor_set(v___x_744_, 0, v___x_746_);
v___x_748_ = v___x_744_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_746_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v_snd_656_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
v___y_650_ = v___x_748_;
goto v___jp_649_;
}
}
}
}
v___jp_657_:
{
uint32_t v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_659_ = 10;
v___x_660_ = lean_string_push(v___y_658_, v___x_659_);
v___x_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_661_, 0, v_fst_655_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
v___y_650_ = v___x_661_;
goto v___jp_649_;
}
}
else
{
return v_b_648_;
}
v___jp_649_:
{
size_t v___x_651_; size_t v___x_652_; 
v___x_651_ = ((size_t)1ULL);
v___x_652_ = lean_usize_add(v_i_646_, v___x_651_);
v_i_646_ = v___x_652_;
v_b_648_ = v___y_650_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___boxed(lean_object* v_as_752_, lean_object* v_i_753_, lean_object* v_stop_754_, lean_object* v_b_755_){
_start:
{
size_t v_i_boxed_756_; size_t v_stop_boxed_757_; lean_object* v_res_758_; 
v_i_boxed_756_ = lean_unbox_usize(v_i_753_);
lean_dec(v_i_753_);
v_stop_boxed_757_ = lean_unbox_usize(v_stop_754_);
lean_dec(v_stop_754_);
v_res_758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5(v_as_752_, v_i_boxed_756_, v_stop_boxed_757_, v_b_755_);
lean_dec_ref(v_as_752_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00Lake_Toml_ppTable_spec__0(lean_object* v_s_759_, lean_object* v_curr_760_){
_start:
{
lean_object* v_str_761_; lean_object* v_startInclusive_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v_str_761_ = lean_ctor_get(v_s_759_, 0);
v_startInclusive_762_ = lean_ctor_get(v_s_759_, 1);
v___x_763_ = lean_nat_add(v_startInclusive_762_, v_curr_760_);
lean_inc(v___x_763_);
lean_inc(v_startInclusive_762_);
lean_inc_ref(v_str_761_);
v___x_764_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_764_, 0, v_str_761_);
lean_ctor_set(v___x_764_, 1, v_startInclusive_762_);
lean_ctor_set(v___x_764_, 2, v___x_763_);
v___x_765_ = lean_nat_sub(v___x_763_, v_startInclusive_762_);
lean_dec(v___x_763_);
v___x_766_ = lean_unsigned_to_nat(0u);
v___x_767_ = lean_nat_dec_eq(v___x_765_, v___x_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___y_775_; lean_object* v___x_776_; uint32_t v___x_777_; uint8_t v___y_779_; uint32_t v___x_784_; uint8_t v___x_785_; 
v___x_768_ = lean_unsigned_to_nat(1u);
v___x_769_ = lean_nat_sub(v___x_765_, v___x_768_);
lean_dec(v___x_765_);
v___x_770_ = l_String_Slice_posLE(v___x_764_, v___x_769_);
v___x_776_ = lean_nat_add(v_startInclusive_762_, v___x_770_);
v___x_777_ = lean_string_utf8_get_fast(v_str_761_, v___x_776_);
lean_dec(v___x_776_);
v___x_784_ = 32;
v___x_785_ = lean_uint32_dec_eq(v___x_777_, v___x_784_);
if (v___x_785_ == 0)
{
uint32_t v___x_786_; uint8_t v___x_787_; 
v___x_786_ = 9;
v___x_787_ = lean_uint32_dec_eq(v___x_777_, v___x_786_);
v___y_779_ = v___x_787_;
goto v___jp_778_;
}
else
{
v___y_779_ = v___x_785_;
goto v___jp_778_;
}
v___jp_771_:
{
uint8_t v___x_772_; 
v___x_772_ = lean_nat_dec_lt(v___x_770_, v_curr_760_);
lean_dec(v_curr_760_);
if (v___x_772_ == 0)
{
lean_dec(v___x_770_);
return v___x_764_;
}
else
{
lean_dec_ref(v___x_764_);
v_curr_760_ = v___x_770_;
goto _start;
}
}
v___jp_774_:
{
if (v___y_775_ == 0)
{
lean_dec(v___x_770_);
lean_dec(v_curr_760_);
return v___x_764_;
}
else
{
goto v___jp_771_;
}
}
v___jp_778_:
{
if (v___y_779_ == 0)
{
uint32_t v___x_780_; uint8_t v___x_781_; 
v___x_780_ = 13;
v___x_781_ = lean_uint32_dec_eq(v___x_777_, v___x_780_);
if (v___x_781_ == 0)
{
uint32_t v___x_782_; uint8_t v___x_783_; 
v___x_782_ = 10;
v___x_783_ = lean_uint32_dec_eq(v___x_777_, v___x_782_);
v___y_775_ = v___x_783_;
goto v___jp_774_;
}
else
{
v___y_775_ = v___x_781_;
goto v___jp_774_;
}
}
else
{
goto v___jp_771_;
}
}
}
else
{
lean_dec(v___x_765_);
lean_dec(v_curr_760_);
return v___x_764_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00Lake_Toml_ppTable_spec__0___boxed(lean_object* v_s_788_, lean_object* v_curr_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00Lake_Toml_ppTable_spec__0(v_s_788_, v_curr_789_);
lean_dec_ref(v_s_788_);
return v_res_790_;
}
}
static lean_object* _init_l_Lake_Toml_ppTable___closed__0(void){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = ((lean_object*)(l_Lake_Toml_instInhabitedValue_default___closed__0));
v___x_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
lean_ctor_set(v___x_792_, 1, v___x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppTable(lean_object* v_t_793_){
_start:
{
lean_object* v_fst_795_; lean_object* v_snd_796_; lean_object* v___y_810_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v_items_815_; lean_object* v___x_816_; lean_object* v___x_817_; uint8_t v___x_818_; 
v___x_813_ = ((lean_object*)(l_Lake_Toml_instInhabitedValue_default___closed__0));
v___x_814_ = lean_obj_once(&l_Lake_Toml_ppTable___closed__0, &l_Lake_Toml_ppTable___closed__0_once, _init_l_Lake_Toml_ppTable___closed__0);
v_items_815_ = lean_ctor_get(v_t_793_, 0);
v___x_816_ = lean_unsigned_to_nat(0u);
v___x_817_ = lean_array_get_size(v_items_815_);
v___x_818_ = lean_nat_dec_lt(v___x_816_, v___x_817_);
if (v___x_818_ == 0)
{
v_fst_795_ = v___x_813_;
v_snd_796_ = v___x_813_;
goto v___jp_794_;
}
else
{
uint8_t v___x_819_; 
v___x_819_ = lean_nat_dec_le(v___x_817_, v___x_817_);
if (v___x_819_ == 0)
{
if (v___x_818_ == 0)
{
v_fst_795_ = v___x_813_;
v_snd_796_ = v___x_813_;
goto v___jp_794_;
}
else
{
size_t v___x_820_; size_t v___x_821_; lean_object* v___x_822_; 
v___x_820_ = ((size_t)0ULL);
v___x_821_ = lean_usize_of_nat(v___x_817_);
v___x_822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5(v_items_815_, v___x_820_, v___x_821_, v___x_814_);
v___y_810_ = v___x_822_;
goto v___jp_809_;
}
}
else
{
size_t v___x_823_; size_t v___x_824_; lean_object* v___x_825_; 
v___x_823_ = ((size_t)0ULL);
v___x_824_ = lean_usize_of_nat(v___x_817_);
v___x_825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5(v_items_815_, v___x_823_, v___x_824_, v___x_814_);
v___y_810_ = v___x_825_;
goto v___jp_809_;
}
}
v___jp_794_:
{
uint32_t v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v_str_804_; lean_object* v_startInclusive_805_; lean_object* v_endExclusive_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_797_ = 10;
v___x_798_ = lean_string_push(v_fst_795_, v___x_797_);
v___x_799_ = lean_string_append(v___x_798_, v_snd_796_);
lean_dec_ref(v_snd_796_);
v___x_800_ = lean_unsigned_to_nat(0u);
v___x_801_ = lean_string_utf8_byte_size(v___x_799_);
v___x_802_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_802_, 0, v___x_799_);
lean_ctor_set(v___x_802_, 1, v___x_800_);
lean_ctor_set(v___x_802_, 2, v___x_801_);
v___x_803_ = l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00Lake_Toml_ppTable_spec__0(v___x_802_, v___x_801_);
lean_dec_ref(v___x_802_);
v_str_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc_ref(v_str_804_);
v_startInclusive_805_ = lean_ctor_get(v___x_803_, 1);
lean_inc(v_startInclusive_805_);
v_endExclusive_806_ = lean_ctor_get(v___x_803_, 2);
lean_inc(v_endExclusive_806_);
lean_dec_ref(v___x_803_);
v___x_807_ = lean_string_utf8_extract(v_str_804_, v_startInclusive_805_, v_endExclusive_806_);
lean_dec(v_endExclusive_806_);
lean_dec(v_startInclusive_805_);
lean_dec_ref(v_str_804_);
v___x_808_ = lean_string_push(v___x_807_, v___x_797_);
return v___x_808_;
}
v___jp_809_:
{
lean_object* v_fst_811_; lean_object* v_snd_812_; 
v_fst_811_ = lean_ctor_get(v___y_810_, 0);
lean_inc(v_fst_811_);
v_snd_812_ = lean_ctor_get(v___y_810_, 1);
lean_inc(v_snd_812_);
lean_dec_ref(v___y_810_);
v_fst_795_ = v_fst_811_;
v_snd_796_ = v_snd_812_;
goto v___jp_794_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppTable___boxed(lean_object* v_t_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lake_Toml_ppTable(v_t_826_);
lean_dec_ref(v_t_826_);
return v_res_827_;
}
}
lean_object* runtime_initialize_Init_Data_Float(uint8_t builtin);
lean_object* runtime_initialize_Lake_Toml_Data_Dict(uint8_t builtin);
lean_object* runtime_initialize_Lake_Toml_Data_DateTime(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_String(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Toml_Data_Value(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Float(builtin);
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
lean_object* initialize_Init_Data_Float(uint8_t builtin);
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
res = initialize_Init_Data_Float(builtin);
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

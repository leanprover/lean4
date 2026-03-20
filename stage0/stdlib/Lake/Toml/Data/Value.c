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
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lake_Toml_ppTable_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lake_Toml_ppTable_spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lake_Toml_ppSimpleKey_spec__0(lean_object* v_s_364_, lean_object* v_pos_365_){
_start:
{
lean_object* v_str_366_; lean_object* v_startInclusive_367_; lean_object* v_endExclusive_368_; lean_object* v___x_369_; uint8_t v___y_377_; lean_object* v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; 
v_str_366_ = lean_ctor_get(v_s_364_, 0);
v_startInclusive_367_ = lean_ctor_get(v_s_364_, 1);
v_endExclusive_368_ = lean_ctor_get(v_s_364_, 2);
v___x_369_ = lean_nat_add(v_startInclusive_367_, v_pos_365_);
v___x_378_ = lean_unsigned_to_nat(0u);
v___x_379_ = lean_nat_sub(v_endExclusive_368_, v___x_369_);
v___x_380_ = lean_nat_dec_eq(v___x_378_, v___x_379_);
lean_dec(v___x_379_);
if (v___x_380_ == 0)
{
uint32_t v___x_381_; uint8_t v___y_383_; uint8_t v___y_389_; uint32_t v___x_399_; uint8_t v___x_400_; 
v___x_381_ = lean_string_utf8_get_fast(v_str_366_, v___x_369_);
v___x_399_ = 65;
v___x_400_ = lean_uint32_dec_le(v___x_399_, v___x_381_);
if (v___x_400_ == 0)
{
goto v___jp_394_;
}
else
{
uint32_t v___x_401_; uint8_t v___x_402_; 
v___x_401_ = 90;
v___x_402_ = lean_uint32_dec_le(v___x_381_, v___x_401_);
if (v___x_402_ == 0)
{
goto v___jp_394_;
}
else
{
goto v___jp_370_;
}
}
v___jp_382_:
{
if (v___y_383_ == 0)
{
uint32_t v___x_384_; uint8_t v___x_385_; 
v___x_384_ = 95;
v___x_385_ = lean_uint32_dec_eq(v___x_381_, v___x_384_);
if (v___x_385_ == 0)
{
uint32_t v___x_386_; uint8_t v___x_387_; 
v___x_386_ = 45;
v___x_387_ = lean_uint32_dec_eq(v___x_381_, v___x_386_);
v___y_377_ = v___x_387_;
goto v___jp_376_;
}
else
{
v___y_377_ = v___x_385_;
goto v___jp_376_;
}
}
else
{
goto v___jp_370_;
}
}
v___jp_388_:
{
if (v___y_389_ == 0)
{
uint32_t v___x_390_; uint8_t v___x_391_; 
v___x_390_ = 48;
v___x_391_ = lean_uint32_dec_le(v___x_390_, v___x_381_);
if (v___x_391_ == 0)
{
v___y_383_ = v___x_391_;
goto v___jp_382_;
}
else
{
uint32_t v___x_392_; uint8_t v___x_393_; 
v___x_392_ = 57;
v___x_393_ = lean_uint32_dec_le(v___x_381_, v___x_392_);
v___y_383_ = v___x_393_;
goto v___jp_382_;
}
}
else
{
goto v___jp_370_;
}
}
v___jp_394_:
{
uint32_t v___x_395_; uint8_t v___x_396_; 
v___x_395_ = 97;
v___x_396_ = lean_uint32_dec_le(v___x_395_, v___x_381_);
if (v___x_396_ == 0)
{
v___y_389_ = v___x_396_;
goto v___jp_388_;
}
else
{
uint32_t v___x_397_; uint8_t v___x_398_; 
v___x_397_ = 122;
v___x_398_ = lean_uint32_dec_le(v___x_381_, v___x_397_);
v___y_389_ = v___x_398_;
goto v___jp_388_;
}
}
}
else
{
lean_dec(v___x_369_);
return v_pos_365_;
}
v___jp_370_:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; uint8_t v___x_374_; 
v___x_371_ = lean_string_utf8_next_fast(v_str_366_, v___x_369_);
v___x_372_ = lean_nat_sub(v___x_371_, v___x_369_);
lean_dec(v___x_369_);
v___x_373_ = lean_nat_add(v_pos_365_, v___x_372_);
lean_dec(v___x_372_);
v___x_374_ = lean_nat_dec_lt(v_pos_365_, v___x_373_);
if (v___x_374_ == 0)
{
lean_dec(v___x_373_);
return v_pos_365_;
}
else
{
lean_dec(v_pos_365_);
v_pos_365_ = v___x_373_;
goto _start;
}
}
v___jp_376_:
{
if (v___y_377_ == 0)
{
lean_dec(v___x_369_);
return v_pos_365_;
}
else
{
goto v___jp_370_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lake_Toml_ppSimpleKey_spec__0___boxed(lean_object* v_s_403_, lean_object* v_pos_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_String_Slice_Pos_skipWhile___at___00Lake_Toml_ppSimpleKey_spec__0(v_s_403_, v_pos_404_);
lean_dec_ref(v_s_403_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppSimpleKey(lean_object* v_k_406_){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_407_ = lean_unsigned_to_nat(0u);
v___x_408_ = lean_string_utf8_byte_size(v_k_406_);
lean_inc_ref(v_k_406_);
v___x_409_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_409_, 0, v_k_406_);
lean_ctor_set(v___x_409_, 1, v___x_407_);
lean_ctor_set(v___x_409_, 2, v___x_408_);
v___x_410_ = l_String_Slice_Pos_skipWhile___at___00Lake_Toml_ppSimpleKey_spec__0(v___x_409_, v___x_407_);
lean_dec_ref(v___x_409_);
v___x_411_ = lean_nat_sub(v___x_408_, v___x_410_);
lean_dec(v___x_410_);
v___x_412_ = lean_nat_dec_eq(v___x_411_, v___x_407_);
lean_dec(v___x_411_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; 
v___x_413_ = l_Lake_Toml_ppString(v_k_406_);
return v___x_413_;
}
else
{
return v_k_406_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppKey(lean_object* v_k_415_){
_start:
{
if (lean_obj_tag(v_k_415_) == 1)
{
lean_object* v_pre_416_; lean_object* v_str_417_; uint8_t v___x_418_; 
v_pre_416_ = lean_ctor_get(v_k_415_, 0);
lean_inc(v_pre_416_);
v_str_417_ = lean_ctor_get(v_k_415_, 1);
lean_inc_ref(v_str_417_);
lean_dec_ref(v_k_415_);
v___x_418_ = l_Lean_Name_isAnonymous(v_pre_416_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_419_ = l_Lake_Toml_ppKey(v_pre_416_);
v___x_420_ = ((lean_object*)(l_Lake_Toml_ppKey___closed__0));
v___x_421_ = lean_string_append(v___x_419_, v___x_420_);
v___x_422_ = l_Lake_Toml_ppSimpleKey(v_str_417_);
v___x_423_ = lean_string_append(v___x_421_, v___x_422_);
lean_dec_ref(v___x_422_);
return v___x_423_;
}
else
{
lean_object* v___x_424_; 
lean_dec(v_pre_416_);
v___x_424_ = l_Lake_Toml_ppSimpleKey(v_str_417_);
return v___x_424_;
}
}
else
{
lean_object* v___x_425_; 
lean_dec(v_k_415_);
v___x_425_ = ((lean_object*)(l_Lake_Toml_instInhabitedValue_default___closed__0));
return v___x_425_;
}
}
}
static lean_object* _init_l_Lake_Toml_Value_toString___closed__0(void){
_start:
{
lean_object* v_natZero_429_; lean_object* v_intZero_430_; 
v_natZero_429_ = lean_unsigned_to_nat(0u);
v_intZero_430_ = lean_nat_to_int(v_natZero_429_);
return v_intZero_430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0(size_t v_sz_435_, size_t v_i_436_, lean_object* v_bs_437_){
_start:
{
uint8_t v___x_438_; 
v___x_438_ = lean_usize_dec_lt(v_i_436_, v_sz_435_);
if (v___x_438_ == 0)
{
return v_bs_437_;
}
else
{
lean_object* v_v_439_; lean_object* v_fst_440_; lean_object* v_snd_441_; lean_object* v___x_442_; lean_object* v_bs_x27_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; size_t v___x_449_; size_t v___x_450_; lean_object* v___x_451_; 
v_v_439_ = lean_array_uget_borrowed(v_bs_437_, v_i_436_);
v_fst_440_ = lean_ctor_get(v_v_439_, 0);
lean_inc(v_fst_440_);
v_snd_441_ = lean_ctor_get(v_v_439_, 1);
lean_inc(v_snd_441_);
v___x_442_ = lean_unsigned_to_nat(0u);
v_bs_x27_443_ = lean_array_uset(v_bs_437_, v_i_436_, v___x_442_);
v___x_444_ = l_Lake_Toml_ppKey(v_fst_440_);
v___x_445_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___closed__0));
v___x_446_ = lean_string_append(v___x_444_, v___x_445_);
v___x_447_ = l_Lake_Toml_Value_toString(v_snd_441_);
v___x_448_ = lean_string_append(v___x_446_, v___x_447_);
lean_dec_ref(v___x_447_);
v___x_449_ = ((size_t)1ULL);
v___x_450_ = lean_usize_add(v_i_436_, v___x_449_);
v___x_451_ = lean_array_uset(v_bs_x27_443_, v_i_436_, v___x_448_);
v_i_436_ = v___x_450_;
v_bs_437_ = v___x_451_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppInlineTable(lean_object* v_t_455_){
_start:
{
lean_object* v_items_456_; size_t v_sz_457_; size_t v___x_458_; lean_object* v_xs_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v_items_456_ = lean_ctor_get(v_t_455_, 0);
lean_inc_ref(v_items_456_);
lean_dec_ref(v_t_455_);
v_sz_457_ = lean_array_size(v_items_456_);
v___x_458_ = ((size_t)0ULL);
v_xs_459_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0(v_sz_457_, v___x_458_, v_items_456_);
v___x_460_ = ((lean_object*)(l_Lake_Toml_ppInlineTable___closed__0));
v___x_461_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__1));
v___x_462_ = lean_array_to_list(v_xs_459_);
v___x_463_ = l_String_intercalate(v___x_461_, v___x_462_);
v___x_464_ = lean_string_append(v___x_460_, v___x_463_);
lean_dec_ref(v___x_463_);
v___x_465_ = ((lean_object*)(l_Lake_Toml_ppInlineTable___closed__1));
v___x_466_ = lean_string_append(v___x_464_, v___x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_toString(lean_object* v_v_467_){
_start:
{
switch(lean_obj_tag(v_v_467_))
{
case 0:
{
lean_object* v_s_468_; lean_object* v___x_469_; 
v_s_468_ = lean_ctor_get(v_v_467_, 1);
lean_inc_ref(v_s_468_);
lean_dec_ref(v_v_467_);
v___x_469_ = l_Lake_Toml_ppString(v_s_468_);
return v___x_469_;
}
case 1:
{
lean_object* v_n_470_; lean_object* v_intZero_471_; uint8_t v_isNeg_472_; 
v_n_470_ = lean_ctor_get(v_v_467_, 1);
lean_inc(v_n_470_);
lean_dec_ref(v_v_467_);
v_intZero_471_ = lean_obj_once(&l_Lake_Toml_Value_toString___closed__0, &l_Lake_Toml_Value_toString___closed__0_once, _init_l_Lake_Toml_Value_toString___closed__0);
v_isNeg_472_ = lean_int_dec_lt(v_n_470_, v_intZero_471_);
if (v_isNeg_472_ == 0)
{
lean_object* v_a_473_; lean_object* v___x_474_; 
v_a_473_ = lean_nat_abs(v_n_470_);
lean_dec(v_n_470_);
v___x_474_ = l_Nat_reprFast(v_a_473_);
return v___x_474_;
}
else
{
lean_object* v_abs_475_; lean_object* v_one_476_; lean_object* v_a_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v_abs_475_ = lean_nat_abs(v_n_470_);
lean_dec(v_n_470_);
v_one_476_ = lean_unsigned_to_nat(1u);
v_a_477_ = lean_nat_sub(v_abs_475_, v_one_476_);
lean_dec(v_abs_475_);
v___x_478_ = ((lean_object*)(l_Lake_Toml_Value_toString___closed__1));
v___x_479_ = lean_nat_add(v_a_477_, v_one_476_);
lean_dec(v_a_477_);
v___x_480_ = l_Nat_reprFast(v___x_479_);
v___x_481_ = lean_string_append(v___x_478_, v___x_480_);
lean_dec_ref(v___x_480_);
return v___x_481_;
}
}
case 2:
{
double v_n_482_; lean_object* v___x_483_; 
v_n_482_ = lean_ctor_get_float(v_v_467_, sizeof(void*)*1);
lean_dec_ref(v_v_467_);
v___x_483_ = lean_float_to_string(v_n_482_);
return v___x_483_;
}
case 3:
{
uint8_t v_b_484_; 
v_b_484_ = lean_ctor_get_uint8(v_v_467_, sizeof(void*)*1);
lean_dec_ref(v_v_467_);
if (v_b_484_ == 0)
{
lean_object* v___x_485_; 
v___x_485_ = ((lean_object*)(l_Lake_Toml_Value_toString___closed__2));
return v___x_485_;
}
else
{
lean_object* v___x_486_; 
v___x_486_ = ((lean_object*)(l_Lake_Toml_Value_toString___closed__3));
return v___x_486_;
}
}
case 4:
{
lean_object* v_dt_487_; lean_object* v___x_488_; 
v_dt_487_ = lean_ctor_get(v_v_467_, 1);
lean_inc_ref(v_dt_487_);
lean_dec_ref(v_v_467_);
v___x_488_ = l_Lake_Toml_DateTime_toString(v_dt_487_);
return v___x_488_;
}
case 5:
{
lean_object* v_xs_489_; lean_object* v___x_490_; 
v_xs_489_ = lean_ctor_get(v_v_467_, 1);
lean_inc_ref(v_xs_489_);
lean_dec_ref(v_v_467_);
v___x_490_ = l_Lake_Toml_ppInlineArray(v_xs_489_);
return v___x_490_;
}
default: 
{
lean_object* v_xs_491_; lean_object* v___x_492_; 
v_xs_491_ = lean_ctor_get(v_v_467_, 1);
lean_inc_ref(v_xs_491_);
lean_dec_ref(v_v_467_);
v___x_492_ = l_Lake_Toml_ppInlineTable(v_xs_491_);
return v___x_492_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3(size_t v_sz_493_, size_t v_i_494_, lean_object* v_bs_495_){
_start:
{
uint8_t v___x_496_; 
v___x_496_ = lean_usize_dec_lt(v_i_494_, v_sz_493_);
if (v___x_496_ == 0)
{
return v_bs_495_;
}
else
{
lean_object* v_v_497_; lean_object* v___x_498_; lean_object* v_bs_x27_499_; lean_object* v___x_500_; size_t v___x_501_; size_t v___x_502_; lean_object* v___x_503_; 
v_v_497_ = lean_array_uget(v_bs_495_, v_i_494_);
v___x_498_ = lean_unsigned_to_nat(0u);
v_bs_x27_499_ = lean_array_uset(v_bs_495_, v_i_494_, v___x_498_);
v___x_500_ = l_Lake_Toml_Value_toString(v_v_497_);
v___x_501_ = ((size_t)1ULL);
v___x_502_ = lean_usize_add(v_i_494_, v___x_501_);
v___x_503_ = lean_array_uset(v_bs_x27_499_, v_i_494_, v___x_500_);
v_i_494_ = v___x_502_;
v_bs_495_ = v___x_503_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppInlineArray(lean_object* v_vs_505_){
_start:
{
size_t v_sz_506_; size_t v___x_507_; lean_object* v_xs_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v_sz_506_ = lean_array_size(v_vs_505_);
v___x_507_ = ((size_t)0ULL);
v_xs_508_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3(v_sz_506_, v___x_507_, v_vs_505_);
v___x_509_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__0));
v___x_510_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__1));
v___x_511_ = lean_array_to_list(v_xs_508_);
v___x_512_ = l_String_intercalate(v___x_510_, v___x_511_);
v___x_513_ = lean_string_append(v___x_509_, v___x_512_);
lean_dec_ref(v___x_512_);
v___x_514_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__2));
v___x_515_ = lean_string_append(v___x_513_, v___x_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3___boxed(lean_object* v_sz_516_, lean_object* v_i_517_, lean_object* v_bs_518_){
_start:
{
size_t v_sz_boxed_519_; size_t v_i_boxed_520_; lean_object* v_res_521_; 
v_sz_boxed_519_ = lean_unbox_usize(v_sz_516_);
lean_dec(v_sz_516_);
v_i_boxed_520_ = lean_unbox_usize(v_i_517_);
lean_dec(v_i_517_);
v_res_521_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3(v_sz_boxed_519_, v_i_boxed_520_, v_bs_518_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___boxed(lean_object* v_sz_522_, lean_object* v_i_523_, lean_object* v_bs_524_){
_start:
{
size_t v_sz_boxed_525_; size_t v_i_boxed_526_; lean_object* v_res_527_; 
v_sz_boxed_525_ = lean_unbox_usize(v_sz_522_);
lean_dec(v_sz_522_);
v_i_boxed_526_ = lean_unbox_usize(v_i_523_);
lean_dec(v_i_523_);
v_res_527_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0(v_sz_boxed_525_, v_i_boxed_526_, v_bs_524_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval(lean_object* v_s_531_, lean_object* v_k_532_, lean_object* v_v_533_){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_534_ = l_Lake_Toml_ppKey(v_k_532_);
v___x_535_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___closed__0));
v___x_536_ = lean_string_append(v___x_534_, v___x_535_);
v___x_537_ = l_Lake_Toml_Value_toString(v_v_533_);
v___x_538_ = lean_string_append(v___x_536_, v___x_537_);
lean_dec_ref(v___x_537_);
v___x_539_ = ((lean_object*)(l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval___closed__0));
v___x_540_ = lean_string_append(v___x_538_, v___x_539_);
v___x_541_ = lean_string_append(v_s_531_, v___x_540_);
lean_dec_ref(v___x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lake_Toml_ppTable_spec__2(lean_object* v_msg_542_){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = ((lean_object*)(l_Lake_Toml_instInhabitedValue_default___closed__0));
v___x_544_ = lean_panic_fn(v___x_543_, v_msg_542_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(lean_object* v_as_545_, size_t v_i_546_, size_t v_stop_547_, lean_object* v_b_548_){
_start:
{
uint8_t v___x_549_; 
v___x_549_ = lean_usize_dec_eq(v_i_546_, v_stop_547_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; lean_object* v_fst_551_; lean_object* v_snd_552_; lean_object* v___x_553_; size_t v___x_554_; size_t v___x_555_; 
v___x_550_ = lean_array_uget_borrowed(v_as_545_, v_i_546_);
v_fst_551_ = lean_ctor_get(v___x_550_, 0);
v_snd_552_ = lean_ctor_get(v___x_550_, 1);
lean_inc(v_snd_552_);
lean_inc(v_fst_551_);
v___x_553_ = l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval(v_b_548_, v_fst_551_, v_snd_552_);
v___x_554_ = ((size_t)1ULL);
v___x_555_ = lean_usize_add(v_i_546_, v___x_554_);
v_i_546_ = v___x_555_;
v_b_548_ = v___x_553_;
goto _start;
}
else
{
return v_b_548_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1___boxed(lean_object* v_as_557_, lean_object* v_i_558_, lean_object* v_stop_559_, lean_object* v_b_560_){
_start:
{
size_t v_i_boxed_561_; size_t v_stop_boxed_562_; lean_object* v_res_563_; 
v_i_boxed_561_ = lean_unbox_usize(v_i_558_);
lean_dec(v_i_558_);
v_stop_boxed_562_ = lean_unbox_usize(v_stop_559_);
lean_dec(v_stop_559_);
v_res_563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_as_557_, v_i_boxed_561_, v_stop_boxed_562_, v_b_560_);
lean_dec_ref(v_as_557_);
return v_res_563_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_569_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__4));
v___x_570_ = lean_unsigned_to_nat(17u);
v___x_571_ = lean_unsigned_to_nat(128u);
v___x_572_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__3));
v___x_573_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__2));
v___x_574_ = l_mkPanicMessageWithDecl(v___x_573_, v___x_572_, v___x_571_, v___x_570_, v___x_569_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3(lean_object* v_fst_575_, lean_object* v_as_576_, size_t v_i_577_, size_t v_stop_578_, lean_object* v_b_579_){
_start:
{
lean_object* v___y_581_; lean_object* v___y_586_; uint8_t v___x_589_; 
v___x_589_ = lean_usize_dec_eq(v_i_577_, v_stop_578_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; 
v___x_590_ = lean_array_uget_borrowed(v_as_576_, v_i_577_);
if (lean_obj_tag(v___x_590_) == 6)
{
lean_object* v_xs_591_; lean_object* v_items_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v_s_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
v_xs_591_ = lean_ctor_get(v___x_590_, 1);
v_items_592_ = lean_ctor_get(v_xs_591_, 0);
v___x_593_ = lean_unsigned_to_nat(0u);
v___x_594_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__0));
lean_inc(v_fst_575_);
v___x_595_ = l_Lake_Toml_ppKey(v_fst_575_);
v___x_596_ = lean_string_append(v___x_594_, v___x_595_);
lean_dec_ref(v___x_595_);
v___x_597_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__1));
v___x_598_ = lean_string_append(v___x_596_, v___x_597_);
v_s_599_ = lean_string_append(v_b_579_, v___x_598_);
lean_dec_ref(v___x_598_);
v___x_600_ = lean_array_get_size(v_items_592_);
v___x_601_ = lean_nat_dec_lt(v___x_593_, v___x_600_);
if (v___x_601_ == 0)
{
v___y_586_ = v_s_599_;
goto v___jp_585_;
}
else
{
uint8_t v___x_602_; 
v___x_602_ = lean_nat_dec_le(v___x_600_, v___x_600_);
if (v___x_602_ == 0)
{
if (v___x_601_ == 0)
{
v___y_586_ = v_s_599_;
goto v___jp_585_;
}
else
{
size_t v___x_603_; size_t v___x_604_; lean_object* v___x_605_; 
v___x_603_ = ((size_t)0ULL);
v___x_604_ = lean_usize_of_nat(v___x_600_);
v___x_605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_items_592_, v___x_603_, v___x_604_, v_s_599_);
v___y_586_ = v___x_605_;
goto v___jp_585_;
}
}
else
{
size_t v___x_606_; size_t v___x_607_; lean_object* v___x_608_; 
v___x_606_ = ((size_t)0ULL);
v___x_607_ = lean_usize_of_nat(v___x_600_);
v___x_608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_items_592_, v___x_606_, v___x_607_, v_s_599_);
v___y_586_ = v___x_608_;
goto v___jp_585_;
}
}
}
else
{
lean_object* v___x_609_; lean_object* v___x_610_; 
lean_dec_ref(v_b_579_);
v___x_609_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5);
v___x_610_ = l_panic___at___00Lake_Toml_ppTable_spec__2(v___x_609_);
v___y_581_ = v___x_610_;
goto v___jp_580_;
}
}
else
{
lean_dec(v_fst_575_);
return v_b_579_;
}
v___jp_580_:
{
size_t v___x_582_; size_t v___x_583_; 
v___x_582_ = ((size_t)1ULL);
v___x_583_ = lean_usize_add(v_i_577_, v___x_582_);
v_i_577_ = v___x_583_;
v_b_579_ = v___y_581_;
goto _start;
}
v___jp_585_:
{
uint32_t v___x_587_; lean_object* v___x_588_; 
v___x_587_ = 10;
v___x_588_ = lean_string_push(v___y_586_, v___x_587_);
v___y_581_ = v___x_588_;
goto v___jp_580_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___boxed(lean_object* v_fst_611_, lean_object* v_as_612_, lean_object* v_i_613_, lean_object* v_stop_614_, lean_object* v_b_615_){
_start:
{
size_t v_i_boxed_616_; size_t v_stop_boxed_617_; lean_object* v_res_618_; 
v_i_boxed_616_ = lean_unbox_usize(v_i_613_);
lean_dec(v_i_613_);
v_stop_boxed_617_ = lean_unbox_usize(v_stop_614_);
lean_dec(v_stop_614_);
v_res_618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3(v_fst_611_, v_as_612_, v_i_boxed_616_, v_stop_boxed_617_, v_b_615_);
lean_dec_ref(v_as_612_);
return v_res_618_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Toml_ppTable_spec__4(lean_object* v___x_619_, lean_object* v_as_620_, size_t v_i_621_, size_t v_stop_622_){
_start:
{
uint8_t v___x_623_; 
v___x_623_ = lean_usize_dec_eq(v_i_621_, v_stop_622_);
if (v___x_623_ == 0)
{
uint8_t v___x_624_; lean_object* v___x_625_; 
v___x_624_ = 1;
v___x_625_ = lean_array_uget_borrowed(v_as_620_, v_i_621_);
if (lean_obj_tag(v___x_625_) == 6)
{
lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_626_ = lean_unsigned_to_nat(0u);
v___x_627_ = lean_nat_dec_eq(v___x_619_, v___x_626_);
if (v___x_627_ == 0)
{
size_t v___x_628_; size_t v___x_629_; 
v___x_628_ = ((size_t)1ULL);
v___x_629_ = lean_usize_add(v_i_621_, v___x_628_);
v_i_621_ = v___x_629_;
goto _start;
}
else
{
return v___x_624_;
}
}
else
{
return v___x_624_;
}
}
else
{
uint8_t v___x_631_; 
v___x_631_ = 0;
return v___x_631_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Toml_ppTable_spec__4___boxed(lean_object* v___x_632_, lean_object* v_as_633_, lean_object* v_i_634_, lean_object* v_stop_635_){
_start:
{
size_t v_i_boxed_636_; size_t v_stop_boxed_637_; uint8_t v_res_638_; lean_object* v_r_639_; 
v_i_boxed_636_ = lean_unbox_usize(v_i_634_);
lean_dec(v_i_634_);
v_stop_boxed_637_ = lean_unbox_usize(v_stop_635_);
lean_dec(v_stop_635_);
v_res_638_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Toml_ppTable_spec__4(v___x_632_, v_as_633_, v_i_boxed_636_, v_stop_boxed_637_);
lean_dec_ref(v_as_633_);
lean_dec(v___x_632_);
v_r_639_ = lean_box(v_res_638_);
return v_r_639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5(lean_object* v_as_642_, size_t v_i_643_, size_t v_stop_644_, lean_object* v_b_645_){
_start:
{
lean_object* v___y_647_; uint8_t v___x_651_; 
v___x_651_ = lean_usize_dec_eq(v_i_643_, v_stop_644_);
if (v___x_651_ == 0)
{
lean_object* v_fst_652_; lean_object* v_snd_653_; lean_object* v___y_655_; lean_object* v___x_659_; lean_object* v_snd_660_; 
v_fst_652_ = lean_ctor_get(v_b_645_, 0);
v_snd_653_ = lean_ctor_get(v_b_645_, 1);
v___x_659_ = lean_array_uget(v_as_642_, v_i_643_);
v_snd_660_ = lean_ctor_get(v___x_659_, 1);
switch(lean_obj_tag(v_snd_660_))
{
case 5:
{
lean_object* v_fst_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_718_; 
lean_inc_ref(v_snd_660_);
v_fst_661_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_718_ == 0)
{
lean_object* v_unused_719_; 
v_unused_719_ = lean_ctor_get(v___x_659_, 1);
lean_dec(v_unused_719_);
v___x_663_ = v___x_659_;
v_isShared_664_ = v_isSharedCheck_718_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_fst_661_);
lean_dec(v___x_659_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_718_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v_xs_665_; lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_683_; 
v_xs_665_ = lean_ctor_get(v_snd_660_, 1);
lean_inc_ref(v_xs_665_);
lean_dec_ref(v_snd_660_);
v___x_666_ = lean_array_get_size(v_xs_665_);
v___x_667_ = lean_unsigned_to_nat(0u);
v___x_683_ = lean_nat_dec_eq(v___x_666_, v___x_667_);
if (v___x_683_ == 0)
{
uint8_t v___x_684_; 
v___x_684_ = lean_nat_dec_lt(v___x_667_, v___x_666_);
if (v___x_684_ == 0)
{
goto v___jp_668_;
}
else
{
if (v___x_684_ == 0)
{
goto v___jp_668_;
}
else
{
size_t v___x_685_; size_t v___x_686_; uint8_t v___x_687_; 
v___x_685_ = ((size_t)0ULL);
v___x_686_ = lean_usize_of_nat(v___x_666_);
v___x_687_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Toml_ppTable_spec__4(v___x_666_, v_xs_665_, v___x_685_, v___x_686_);
if (v___x_687_ == 0)
{
goto v___jp_668_;
}
else
{
if (v___x_683_ == 0)
{
lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_702_; 
lean_inc(v_snd_653_);
lean_inc(v_fst_652_);
lean_del_object(v___x_663_);
v_isSharedCheck_702_ = !lean_is_exclusive(v_b_645_);
if (v_isSharedCheck_702_ == 0)
{
lean_object* v_unused_703_; lean_object* v_unused_704_; 
v_unused_703_ = lean_ctor_get(v_b_645_, 1);
lean_dec(v_unused_703_);
v_unused_704_ = lean_ctor_get(v_b_645_, 0);
lean_dec(v_unused_704_);
v___x_689_ = v_b_645_;
v_isShared_690_ = v_isSharedCheck_702_;
goto v_resetjp_688_;
}
else
{
lean_dec(v_b_645_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_702_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_691_ = l_Lake_Toml_ppKey(v_fst_661_);
v___x_692_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___closed__0));
v___x_693_ = lean_string_append(v___x_691_, v___x_692_);
v___x_694_ = l_Lake_Toml_ppInlineArray(v_xs_665_);
v___x_695_ = lean_string_append(v___x_693_, v___x_694_);
lean_dec_ref(v___x_694_);
v___x_696_ = ((lean_object*)(l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval___closed__0));
v___x_697_ = lean_string_append(v___x_695_, v___x_696_);
v___x_698_ = lean_string_append(v_fst_652_, v___x_697_);
lean_dec_ref(v___x_697_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 0, v___x_698_);
v___x_700_ = v___x_689_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_698_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_snd_653_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
v___y_647_ = v___x_700_;
goto v___jp_646_;
}
}
}
else
{
goto v___jp_668_;
}
}
}
}
}
else
{
lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_715_; 
lean_inc(v_snd_653_);
lean_inc(v_fst_652_);
lean_dec_ref(v_xs_665_);
lean_del_object(v___x_663_);
v_isSharedCheck_715_ = !lean_is_exclusive(v_b_645_);
if (v_isSharedCheck_715_ == 0)
{
lean_object* v_unused_716_; lean_object* v_unused_717_; 
v_unused_716_ = lean_ctor_get(v_b_645_, 1);
lean_dec(v_unused_716_);
v_unused_717_ = lean_ctor_get(v_b_645_, 0);
lean_dec(v_unused_717_);
v___x_706_ = v_b_645_;
v_isShared_707_ = v_isSharedCheck_715_;
goto v_resetjp_705_;
}
else
{
lean_dec(v_b_645_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_715_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_713_; 
v___x_708_ = l_Lake_Toml_ppKey(v_fst_661_);
v___x_709_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___closed__0));
v___x_710_ = lean_string_append(v___x_708_, v___x_709_);
v___x_711_ = lean_string_append(v_fst_652_, v___x_710_);
lean_dec_ref(v___x_710_);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 0, v___x_711_);
v___x_713_ = v___x_706_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_711_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v_snd_653_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
v___y_647_ = v___x_713_;
goto v___jp_646_;
}
}
}
v___jp_668_:
{
uint8_t v___x_669_; 
v___x_669_ = lean_nat_dec_lt(v___x_667_, v___x_666_);
if (v___x_669_ == 0)
{
lean_dec_ref(v_xs_665_);
lean_del_object(v___x_663_);
lean_dec(v_fst_661_);
v___y_647_ = v_b_645_;
goto v___jp_646_;
}
else
{
uint8_t v___x_670_; 
v___x_670_ = lean_nat_dec_le(v___x_666_, v___x_666_);
if (v___x_670_ == 0)
{
if (v___x_669_ == 0)
{
lean_dec_ref(v_xs_665_);
lean_del_object(v___x_663_);
lean_dec(v_fst_661_);
v___y_647_ = v_b_645_;
goto v___jp_646_;
}
else
{
size_t v___x_671_; size_t v___x_672_; lean_object* v___x_673_; lean_object* v___x_675_; 
lean_inc(v_snd_653_);
lean_inc(v_fst_652_);
lean_dec_ref(v_b_645_);
v___x_671_ = ((size_t)0ULL);
v___x_672_ = lean_usize_of_nat(v___x_666_);
v___x_673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3(v_fst_661_, v_xs_665_, v___x_671_, v___x_672_, v_snd_653_);
lean_dec_ref(v_xs_665_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 1, v___x_673_);
lean_ctor_set(v___x_663_, 0, v_fst_652_);
v___x_675_ = v___x_663_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_fst_652_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v___x_673_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
v___y_647_ = v___x_675_;
goto v___jp_646_;
}
}
}
else
{
size_t v___x_677_; size_t v___x_678_; lean_object* v___x_679_; lean_object* v___x_681_; 
lean_inc(v_snd_653_);
lean_inc(v_fst_652_);
lean_dec_ref(v_b_645_);
v___x_677_ = ((size_t)0ULL);
v___x_678_ = lean_usize_of_nat(v___x_666_);
v___x_679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3(v_fst_661_, v_xs_665_, v___x_677_, v___x_678_, v_snd_653_);
lean_dec_ref(v_xs_665_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 1, v___x_679_);
lean_ctor_set(v___x_663_, 0, v_fst_652_);
v___x_681_ = v___x_663_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_fst_652_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v___x_679_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
v___y_647_ = v___x_681_;
goto v___jp_646_;
}
}
}
}
}
}
case 6:
{
lean_object* v_xs_720_; lean_object* v_fst_721_; lean_object* v_items_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v_fs_728_; lean_object* v___x_729_; lean_object* v___x_730_; uint8_t v___x_731_; 
lean_inc(v_snd_653_);
lean_inc(v_fst_652_);
lean_dec_ref(v_b_645_);
v_xs_720_ = lean_ctor_get(v_snd_660_, 1);
lean_inc_ref(v_xs_720_);
v_fst_721_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_fst_721_);
lean_dec(v___x_659_);
v_items_722_ = lean_ctor_get(v_xs_720_, 0);
lean_inc_ref(v_items_722_);
lean_dec_ref(v_xs_720_);
v___x_723_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__0));
v___x_724_ = l_Lake_Toml_ppKey(v_fst_721_);
v___x_725_ = lean_string_append(v___x_723_, v___x_724_);
lean_dec_ref(v___x_724_);
v___x_726_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___closed__1));
v___x_727_ = lean_string_append(v___x_725_, v___x_726_);
v_fs_728_ = lean_string_append(v_snd_653_, v___x_727_);
lean_dec_ref(v___x_727_);
v___x_729_ = lean_unsigned_to_nat(0u);
v___x_730_ = lean_array_get_size(v_items_722_);
v___x_731_ = lean_nat_dec_lt(v___x_729_, v___x_730_);
if (v___x_731_ == 0)
{
lean_dec_ref(v_items_722_);
v___y_655_ = v_fs_728_;
goto v___jp_654_;
}
else
{
uint8_t v___x_732_; 
v___x_732_ = lean_nat_dec_le(v___x_730_, v___x_730_);
if (v___x_732_ == 0)
{
if (v___x_731_ == 0)
{
lean_dec_ref(v_items_722_);
v___y_655_ = v_fs_728_;
goto v___jp_654_;
}
else
{
size_t v___x_733_; size_t v___x_734_; lean_object* v___x_735_; 
v___x_733_ = ((size_t)0ULL);
v___x_734_ = lean_usize_of_nat(v___x_730_);
v___x_735_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_items_722_, v___x_733_, v___x_734_, v_fs_728_);
lean_dec_ref(v_items_722_);
v___y_655_ = v___x_735_;
goto v___jp_654_;
}
}
else
{
size_t v___x_736_; size_t v___x_737_; lean_object* v___x_738_; 
v___x_736_ = ((size_t)0ULL);
v___x_737_ = lean_usize_of_nat(v___x_730_);
v___x_738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_items_722_, v___x_736_, v___x_737_, v_fs_728_);
lean_dec_ref(v_items_722_);
v___y_655_ = v___x_738_;
goto v___jp_654_;
}
}
}
default: 
{
lean_object* v_fst_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_747_; 
lean_inc(v_snd_660_);
lean_inc(v_snd_653_);
lean_inc(v_fst_652_);
lean_dec_ref(v_b_645_);
v_fst_739_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_747_ == 0)
{
lean_object* v_unused_748_; 
v_unused_748_ = lean_ctor_get(v___x_659_, 1);
lean_dec(v_unused_748_);
v___x_741_ = v___x_659_;
v_isShared_742_ = v_isSharedCheck_747_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_fst_739_);
lean_dec(v___x_659_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_747_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_743_; lean_object* v___x_745_; 
v___x_743_ = l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval(v_fst_652_, v_fst_739_, v_snd_660_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 1, v_snd_653_);
lean_ctor_set(v___x_741_, 0, v___x_743_);
v___x_745_ = v___x_741_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_743_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_snd_653_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
v___y_647_ = v___x_745_;
goto v___jp_646_;
}
}
}
}
v___jp_654_:
{
uint32_t v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_656_ = 10;
v___x_657_ = lean_string_push(v___y_655_, v___x_656_);
v___x_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_658_, 0, v_fst_652_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
v___y_647_ = v___x_658_;
goto v___jp_646_;
}
}
else
{
return v_b_645_;
}
v___jp_646_:
{
size_t v___x_648_; size_t v___x_649_; 
v___x_648_ = ((size_t)1ULL);
v___x_649_ = lean_usize_add(v_i_643_, v___x_648_);
v_i_643_ = v___x_649_;
v_b_645_ = v___y_647_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___boxed(lean_object* v_as_749_, lean_object* v_i_750_, lean_object* v_stop_751_, lean_object* v_b_752_){
_start:
{
size_t v_i_boxed_753_; size_t v_stop_boxed_754_; lean_object* v_res_755_; 
v_i_boxed_753_ = lean_unbox_usize(v_i_750_);
lean_dec(v_i_750_);
v_stop_boxed_754_ = lean_unbox_usize(v_stop_751_);
lean_dec(v_stop_751_);
v_res_755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5(v_as_749_, v_i_boxed_753_, v_stop_boxed_754_, v_b_752_);
lean_dec_ref(v_as_749_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lake_Toml_ppTable_spec__0(lean_object* v_s_756_, lean_object* v_pos_757_){
_start:
{
lean_object* v_str_758_; lean_object* v_startInclusive_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; uint8_t v___x_763_; 
v_str_758_ = lean_ctor_get(v_s_756_, 0);
v_startInclusive_759_ = lean_ctor_get(v_s_756_, 1);
v___x_760_ = lean_nat_add(v_startInclusive_759_, v_pos_757_);
v___x_761_ = lean_nat_sub(v___x_760_, v_startInclusive_759_);
v___x_762_ = lean_unsigned_to_nat(0u);
v___x_763_ = lean_nat_dec_eq(v___x_761_, v___x_762_);
if (v___x_763_ == 0)
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___y_772_; lean_object* v___x_773_; uint32_t v___x_774_; uint8_t v___y_776_; uint32_t v___x_781_; uint8_t v___x_782_; 
lean_inc(v_startInclusive_759_);
lean_inc_ref(v_str_758_);
v___x_764_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_764_, 0, v_str_758_);
lean_ctor_set(v___x_764_, 1, v_startInclusive_759_);
lean_ctor_set(v___x_764_, 2, v___x_760_);
v___x_765_ = lean_unsigned_to_nat(1u);
v___x_766_ = lean_nat_sub(v___x_761_, v___x_765_);
lean_dec(v___x_761_);
v___x_767_ = l_String_Slice_posLE(v___x_764_, v___x_766_);
lean_dec_ref(v___x_764_);
v___x_773_ = lean_nat_add(v_startInclusive_759_, v___x_767_);
v___x_774_ = lean_string_utf8_get_fast(v_str_758_, v___x_773_);
lean_dec(v___x_773_);
v___x_781_ = 32;
v___x_782_ = lean_uint32_dec_eq(v___x_774_, v___x_781_);
if (v___x_782_ == 0)
{
uint32_t v___x_783_; uint8_t v___x_784_; 
v___x_783_ = 9;
v___x_784_ = lean_uint32_dec_eq(v___x_774_, v___x_783_);
v___y_776_ = v___x_784_;
goto v___jp_775_;
}
else
{
v___y_776_ = v___x_782_;
goto v___jp_775_;
}
v___jp_768_:
{
uint8_t v___x_769_; 
v___x_769_ = lean_nat_dec_lt(v___x_767_, v_pos_757_);
if (v___x_769_ == 0)
{
lean_dec(v___x_767_);
return v_pos_757_;
}
else
{
lean_dec(v_pos_757_);
v_pos_757_ = v___x_767_;
goto _start;
}
}
v___jp_771_:
{
if (v___y_772_ == 0)
{
lean_dec(v___x_767_);
return v_pos_757_;
}
else
{
goto v___jp_768_;
}
}
v___jp_775_:
{
if (v___y_776_ == 0)
{
uint32_t v___x_777_; uint8_t v___x_778_; 
v___x_777_ = 13;
v___x_778_ = lean_uint32_dec_eq(v___x_774_, v___x_777_);
if (v___x_778_ == 0)
{
uint32_t v___x_779_; uint8_t v___x_780_; 
v___x_779_ = 10;
v___x_780_ = lean_uint32_dec_eq(v___x_774_, v___x_779_);
v___y_772_ = v___x_780_;
goto v___jp_771_;
}
else
{
v___y_772_ = v___x_778_;
goto v___jp_771_;
}
}
else
{
goto v___jp_768_;
}
}
}
else
{
lean_dec(v___x_761_);
lean_dec(v___x_760_);
return v_pos_757_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lake_Toml_ppTable_spec__0___boxed(lean_object* v_s_785_, lean_object* v_pos_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_String_Slice_Pos_revSkipWhile___at___00Lake_Toml_ppTable_spec__0(v_s_785_, v_pos_786_);
lean_dec_ref(v_s_785_);
return v_res_787_;
}
}
static lean_object* _init_l_Lake_Toml_ppTable___closed__0(void){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = ((lean_object*)(l_Lake_Toml_instInhabitedValue_default___closed__0));
v___x_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppTable(lean_object* v_t_790_){
_start:
{
lean_object* v_fst_792_; lean_object* v_snd_793_; lean_object* v___y_804_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v_items_809_; lean_object* v___x_810_; lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_807_ = ((lean_object*)(l_Lake_Toml_instInhabitedValue_default___closed__0));
v___x_808_ = lean_obj_once(&l_Lake_Toml_ppTable___closed__0, &l_Lake_Toml_ppTable___closed__0_once, _init_l_Lake_Toml_ppTable___closed__0);
v_items_809_ = lean_ctor_get(v_t_790_, 0);
v___x_810_ = lean_unsigned_to_nat(0u);
v___x_811_ = lean_array_get_size(v_items_809_);
v___x_812_ = lean_nat_dec_lt(v___x_810_, v___x_811_);
if (v___x_812_ == 0)
{
v_fst_792_ = v___x_807_;
v_snd_793_ = v___x_807_;
goto v___jp_791_;
}
else
{
uint8_t v___x_813_; 
v___x_813_ = lean_nat_dec_le(v___x_811_, v___x_811_);
if (v___x_813_ == 0)
{
if (v___x_812_ == 0)
{
v_fst_792_ = v___x_807_;
v_snd_793_ = v___x_807_;
goto v___jp_791_;
}
else
{
size_t v___x_814_; size_t v___x_815_; lean_object* v___x_816_; 
v___x_814_ = ((size_t)0ULL);
v___x_815_ = lean_usize_of_nat(v___x_811_);
v___x_816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5(v_items_809_, v___x_814_, v___x_815_, v___x_808_);
v___y_804_ = v___x_816_;
goto v___jp_803_;
}
}
else
{
size_t v___x_817_; size_t v___x_818_; lean_object* v___x_819_; 
v___x_817_ = ((size_t)0ULL);
v___x_818_ = lean_usize_of_nat(v___x_811_);
v___x_819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5(v_items_809_, v___x_817_, v___x_818_, v___x_808_);
v___y_804_ = v___x_819_;
goto v___jp_803_;
}
}
v___jp_791_:
{
uint32_t v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_794_ = 10;
v___x_795_ = lean_string_push(v_fst_792_, v___x_794_);
v___x_796_ = lean_string_append(v___x_795_, v_snd_793_);
lean_dec_ref(v_snd_793_);
v___x_797_ = lean_unsigned_to_nat(0u);
v___x_798_ = lean_string_utf8_byte_size(v___x_796_);
lean_inc_ref(v___x_796_);
v___x_799_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_799_, 0, v___x_796_);
lean_ctor_set(v___x_799_, 1, v___x_797_);
lean_ctor_set(v___x_799_, 2, v___x_798_);
v___x_800_ = l_String_Slice_Pos_revSkipWhile___at___00Lake_Toml_ppTable_spec__0(v___x_799_, v___x_798_);
lean_dec_ref(v___x_799_);
v___x_801_ = lean_string_utf8_extract(v___x_796_, v___x_797_, v___x_800_);
lean_dec(v___x_800_);
lean_dec_ref(v___x_796_);
v___x_802_ = lean_string_push(v___x_801_, v___x_794_);
return v___x_802_;
}
v___jp_803_:
{
lean_object* v_fst_805_; lean_object* v_snd_806_; 
v_fst_805_ = lean_ctor_get(v___y_804_, 0);
lean_inc(v_fst_805_);
v_snd_806_ = lean_ctor_get(v___y_804_, 1);
lean_inc(v_snd_806_);
lean_dec_ref(v___y_804_);
v_fst_792_ = v_fst_805_;
v_snd_793_ = v_snd_806_;
goto v___jp_791_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppTable___boxed(lean_object* v_t_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lake_Toml_ppTable(v_t_820_);
lean_dec_ref(v_t_820_);
return v_res_821_;
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

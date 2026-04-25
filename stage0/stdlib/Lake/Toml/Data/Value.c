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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
uint32_t v___x_277_; lean_object* v___x_278_; uint8_t v___y_280_; uint32_t v___x_294_; uint8_t v___x_295_; 
v___x_277_ = lean_string_utf8_get_fast(v_s_270_, v_a_271_);
v___x_278_ = lean_string_utf8_next_fast(v_s_270_, v_a_271_);
lean_dec(v_a_271_);
v___x_294_ = 8;
v___x_295_ = lean_uint32_dec_eq(v___x_277_, v___x_294_);
if (v___x_295_ == 0)
{
uint32_t v___x_296_; uint8_t v___x_297_; 
v___x_296_ = 9;
v___x_297_ = lean_uint32_dec_eq(v___x_277_, v___x_296_);
if (v___x_297_ == 0)
{
uint32_t v___x_298_; uint8_t v___x_299_; 
v___x_298_ = 10;
v___x_299_ = lean_uint32_dec_eq(v___x_277_, v___x_298_);
if (v___x_299_ == 0)
{
uint32_t v___x_300_; uint8_t v___x_301_; 
v___x_300_ = 12;
v___x_301_ = lean_uint32_dec_eq(v___x_277_, v___x_300_);
if (v___x_301_ == 0)
{
uint32_t v___x_302_; uint8_t v___x_303_; 
v___x_302_ = 13;
v___x_303_ = lean_uint32_dec_eq(v___x_277_, v___x_302_);
if (v___x_303_ == 0)
{
uint32_t v___x_304_; uint8_t v___x_305_; 
v___x_304_ = 34;
v___x_305_ = lean_uint32_dec_eq(v___x_277_, v___x_304_);
if (v___x_305_ == 0)
{
uint32_t v___x_306_; uint8_t v___x_307_; 
v___x_306_ = 92;
v___x_307_ = lean_uint32_dec_eq(v___x_277_, v___x_306_);
if (v___x_307_ == 0)
{
uint32_t v___x_308_; uint8_t v___x_309_; 
v___x_308_ = 32;
v___x_309_ = lean_uint32_dec_lt(v___x_277_, v___x_308_);
if (v___x_309_ == 0)
{
uint32_t v___x_310_; uint8_t v___x_311_; 
v___x_310_ = 127;
v___x_311_ = lean_uint32_dec_eq(v___x_277_, v___x_310_);
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
v_a_271_ = v___x_278_;
v_b_272_ = v___x_313_;
goto _start;
}
}
else
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__2));
v___x_316_ = lean_string_append(v_b_272_, v___x_315_);
v_a_271_ = v___x_278_;
v_b_272_ = v___x_316_;
goto _start;
}
}
else
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__3));
v___x_319_ = lean_string_append(v_b_272_, v___x_318_);
v_a_271_ = v___x_278_;
v_b_272_ = v___x_319_;
goto _start;
}
}
else
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__4));
v___x_322_ = lean_string_append(v_b_272_, v___x_321_);
v_a_271_ = v___x_278_;
v_b_272_ = v___x_322_;
goto _start;
}
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__5));
v___x_325_ = lean_string_append(v_b_272_, v___x_324_);
v_a_271_ = v___x_278_;
v_b_272_ = v___x_325_;
goto _start;
}
}
else
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__6));
v___x_328_ = lean_string_append(v_b_272_, v___x_327_);
v_a_271_ = v___x_278_;
v_b_272_ = v___x_328_;
goto _start;
}
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__7));
v___x_331_ = lean_string_append(v_b_272_, v___x_330_);
v_a_271_ = v___x_278_;
v_b_272_ = v___x_331_;
goto _start;
}
v___jp_279_:
{
if (v___y_280_ == 0)
{
lean_object* v___x_281_; 
v___x_281_ = lean_string_push(v_b_272_, v___x_277_);
v_a_271_ = v___x_278_;
v_b_272_ = v___x_281_;
goto _start;
}
else
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; uint32_t v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_283_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__0));
v___x_284_ = lean_string_append(v_b_272_, v___x_283_);
v___x_285_ = lean_unsigned_to_nat(16u);
v___x_286_ = lean_uint32_to_nat(v___x_277_);
v___x_287_ = l_Nat_toDigits(v___x_285_, v___x_286_);
v___x_288_ = lean_string_mk(v___x_287_);
v___x_289_ = 48;
v___x_290_ = lean_unsigned_to_nat(4u);
v___x_291_ = l_Lake_lpad(v___x_288_, v___x_289_, v___x_290_);
lean_dec_ref(v___x_288_);
v___x_292_ = lean_string_append(v___x_284_, v___x_291_);
lean_dec_ref(v___x_291_);
v_a_271_ = v___x_278_;
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
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_407_ = lean_unsigned_to_nat(0u);
v___x_408_ = lean_string_utf8_byte_size(v_k_406_);
lean_inc_ref(v_k_406_);
v___x_409_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_409_, 0, v_k_406_);
lean_ctor_set(v___x_409_, 1, v___x_407_);
lean_ctor_set(v___x_409_, 2, v___x_408_);
v___x_410_ = l_String_Slice_Pos_skipWhile___at___00Lake_Toml_ppSimpleKey_spec__0(v___x_409_, v___x_407_);
lean_dec_ref(v___x_409_);
v___x_411_ = lean_nat_dec_eq(v___x_410_, v___x_408_);
lean_dec(v___x_410_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; 
v___x_412_ = l_Lake_Toml_ppString(v_k_406_);
return v___x_412_;
}
else
{
return v_k_406_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppKey(lean_object* v_k_414_){
_start:
{
if (lean_obj_tag(v_k_414_) == 1)
{
lean_object* v_pre_415_; lean_object* v_str_416_; uint8_t v___x_417_; 
v_pre_415_ = lean_ctor_get(v_k_414_, 0);
lean_inc(v_pre_415_);
v_str_416_ = lean_ctor_get(v_k_414_, 1);
lean_inc_ref(v_str_416_);
lean_dec_ref(v_k_414_);
v___x_417_ = l_Lean_Name_isAnonymous(v_pre_415_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_418_ = l_Lake_Toml_ppKey(v_pre_415_);
v___x_419_ = ((lean_object*)(l_Lake_Toml_ppKey___closed__0));
v___x_420_ = lean_string_append(v___x_418_, v___x_419_);
v___x_421_ = l_Lake_Toml_ppSimpleKey(v_str_416_);
v___x_422_ = lean_string_append(v___x_420_, v___x_421_);
lean_dec_ref(v___x_421_);
return v___x_422_;
}
else
{
lean_object* v___x_423_; 
lean_dec(v_pre_415_);
v___x_423_ = l_Lake_Toml_ppSimpleKey(v_str_416_);
return v___x_423_;
}
}
else
{
lean_object* v___x_424_; 
lean_dec(v_k_414_);
v___x_424_ = ((lean_object*)(l_Lake_Toml_instInhabitedValue_default___closed__0));
return v___x_424_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0(size_t v_sz_431_, size_t v_i_432_, lean_object* v_bs_433_){
_start:
{
uint8_t v___x_434_; 
v___x_434_ = lean_usize_dec_lt(v_i_432_, v_sz_431_);
if (v___x_434_ == 0)
{
return v_bs_433_;
}
else
{
lean_object* v_v_435_; lean_object* v_fst_436_; lean_object* v_snd_437_; lean_object* v___x_438_; lean_object* v_bs_x27_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; size_t v___x_445_; size_t v___x_446_; lean_object* v___x_447_; 
v_v_435_ = lean_array_uget_borrowed(v_bs_433_, v_i_432_);
v_fst_436_ = lean_ctor_get(v_v_435_, 0);
lean_inc(v_fst_436_);
v_snd_437_ = lean_ctor_get(v_v_435_, 1);
lean_inc(v_snd_437_);
v___x_438_ = lean_unsigned_to_nat(0u);
v_bs_x27_439_ = lean_array_uset(v_bs_433_, v_i_432_, v___x_438_);
v___x_440_ = l_Lake_Toml_ppKey(v_fst_436_);
v___x_441_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___closed__0));
v___x_442_ = lean_string_append(v___x_440_, v___x_441_);
v___x_443_ = l_Lake_Toml_Value_toString(v_snd_437_);
v___x_444_ = lean_string_append(v___x_442_, v___x_443_);
lean_dec_ref(v___x_443_);
v___x_445_ = ((size_t)1ULL);
v___x_446_ = lean_usize_add(v_i_432_, v___x_445_);
v___x_447_ = lean_array_uset(v_bs_x27_439_, v_i_432_, v___x_444_);
v_i_432_ = v___x_446_;
v_bs_433_ = v___x_447_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppInlineTable(lean_object* v_t_451_){
_start:
{
lean_object* v_items_452_; size_t v_sz_453_; size_t v___x_454_; lean_object* v_xs_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_items_452_ = lean_ctor_get(v_t_451_, 0);
lean_inc_ref(v_items_452_);
lean_dec_ref(v_t_451_);
v_sz_453_ = lean_array_size(v_items_452_);
v___x_454_ = ((size_t)0ULL);
v_xs_455_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0(v_sz_453_, v___x_454_, v_items_452_);
v___x_456_ = ((lean_object*)(l_Lake_Toml_ppInlineTable___closed__0));
v___x_457_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__1));
v___x_458_ = lean_array_to_list(v_xs_455_);
v___x_459_ = l_String_intercalate(v___x_457_, v___x_458_);
v___x_460_ = lean_string_append(v___x_456_, v___x_459_);
lean_dec_ref(v___x_459_);
v___x_461_ = ((lean_object*)(l_Lake_Toml_ppInlineTable___closed__1));
v___x_462_ = lean_string_append(v___x_460_, v___x_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_toString(lean_object* v_v_463_){
_start:
{
switch(lean_obj_tag(v_v_463_))
{
case 0:
{
lean_object* v_s_464_; lean_object* v___x_465_; 
v_s_464_ = lean_ctor_get(v_v_463_, 1);
lean_inc_ref(v_s_464_);
lean_dec_ref(v_v_463_);
v___x_465_ = l_Lake_Toml_ppString(v_s_464_);
return v___x_465_;
}
case 1:
{
lean_object* v_n_466_; lean_object* v___x_467_; 
v_n_466_ = lean_ctor_get(v_v_463_, 1);
lean_inc(v_n_466_);
lean_dec_ref(v_v_463_);
v___x_467_ = l_Int_repr(v_n_466_);
lean_dec(v_n_466_);
return v___x_467_;
}
case 2:
{
double v_n_468_; lean_object* v___x_469_; 
v_n_468_ = lean_ctor_get_float(v_v_463_, sizeof(void*)*1);
lean_dec_ref(v_v_463_);
v___x_469_ = lean_float_to_string(v_n_468_);
return v___x_469_;
}
case 3:
{
uint8_t v_b_470_; 
v_b_470_ = lean_ctor_get_uint8(v_v_463_, sizeof(void*)*1);
lean_dec_ref(v_v_463_);
if (v_b_470_ == 0)
{
lean_object* v___x_471_; 
v___x_471_ = ((lean_object*)(l_Lake_Toml_Value_toString___closed__0));
return v___x_471_;
}
else
{
lean_object* v___x_472_; 
v___x_472_ = ((lean_object*)(l_Lake_Toml_Value_toString___closed__1));
return v___x_472_;
}
}
case 4:
{
lean_object* v_dt_473_; lean_object* v___x_474_; 
v_dt_473_ = lean_ctor_get(v_v_463_, 1);
lean_inc_ref(v_dt_473_);
lean_dec_ref(v_v_463_);
v___x_474_ = l_Lake_Toml_DateTime_toString(v_dt_473_);
return v___x_474_;
}
case 5:
{
lean_object* v_xs_475_; lean_object* v___x_476_; 
v_xs_475_ = lean_ctor_get(v_v_463_, 1);
lean_inc_ref(v_xs_475_);
lean_dec_ref(v_v_463_);
v___x_476_ = l_Lake_Toml_ppInlineArray(v_xs_475_);
return v___x_476_;
}
default: 
{
lean_object* v_xs_477_; lean_object* v___x_478_; 
v_xs_477_ = lean_ctor_get(v_v_463_, 1);
lean_inc_ref(v_xs_477_);
lean_dec_ref(v_v_463_);
v___x_478_ = l_Lake_Toml_ppInlineTable(v_xs_477_);
return v___x_478_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3(size_t v_sz_479_, size_t v_i_480_, lean_object* v_bs_481_){
_start:
{
uint8_t v___x_482_; 
v___x_482_ = lean_usize_dec_lt(v_i_480_, v_sz_479_);
if (v___x_482_ == 0)
{
return v_bs_481_;
}
else
{
lean_object* v_v_483_; lean_object* v___x_484_; lean_object* v_bs_x27_485_; lean_object* v___x_486_; size_t v___x_487_; size_t v___x_488_; lean_object* v___x_489_; 
v_v_483_ = lean_array_uget(v_bs_481_, v_i_480_);
v___x_484_ = lean_unsigned_to_nat(0u);
v_bs_x27_485_ = lean_array_uset(v_bs_481_, v_i_480_, v___x_484_);
v___x_486_ = l_Lake_Toml_Value_toString(v_v_483_);
v___x_487_ = ((size_t)1ULL);
v___x_488_ = lean_usize_add(v_i_480_, v___x_487_);
v___x_489_ = lean_array_uset(v_bs_x27_485_, v_i_480_, v___x_486_);
v_i_480_ = v___x_488_;
v_bs_481_ = v___x_489_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppInlineArray(lean_object* v_vs_491_){
_start:
{
size_t v_sz_492_; size_t v___x_493_; lean_object* v_xs_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v_sz_492_ = lean_array_size(v_vs_491_);
v___x_493_ = ((size_t)0ULL);
v_xs_494_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3(v_sz_492_, v___x_493_, v_vs_491_);
v___x_495_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__0));
v___x_496_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__1));
v___x_497_ = lean_array_to_list(v_xs_494_);
v___x_498_ = l_String_intercalate(v___x_496_, v___x_497_);
v___x_499_ = lean_string_append(v___x_495_, v___x_498_);
lean_dec_ref(v___x_498_);
v___x_500_ = ((lean_object*)(l_Lake_Toml_ppInlineArray___closed__2));
v___x_501_ = lean_string_append(v___x_499_, v___x_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3___boxed(lean_object* v_sz_502_, lean_object* v_i_503_, lean_object* v_bs_504_){
_start:
{
size_t v_sz_boxed_505_; size_t v_i_boxed_506_; lean_object* v_res_507_; 
v_sz_boxed_505_ = lean_unbox_usize(v_sz_502_);
lean_dec(v_sz_502_);
v_i_boxed_506_ = lean_unbox_usize(v_i_503_);
lean_dec(v_i_503_);
v_res_507_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3(v_sz_boxed_505_, v_i_boxed_506_, v_bs_504_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___boxed(lean_object* v_sz_508_, lean_object* v_i_509_, lean_object* v_bs_510_){
_start:
{
size_t v_sz_boxed_511_; size_t v_i_boxed_512_; lean_object* v_res_513_; 
v_sz_boxed_511_ = lean_unbox_usize(v_sz_508_);
lean_dec(v_sz_508_);
v_i_boxed_512_ = lean_unbox_usize(v_i_509_);
lean_dec(v_i_509_);
v_res_513_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0(v_sz_boxed_511_, v_i_boxed_512_, v_bs_510_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval(lean_object* v_s_517_, lean_object* v_k_518_, lean_object* v_v_519_){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_520_ = l_Lake_Toml_ppKey(v_k_518_);
v___x_521_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___closed__0));
v___x_522_ = lean_string_append(v___x_520_, v___x_521_);
v___x_523_ = l_Lake_Toml_Value_toString(v_v_519_);
v___x_524_ = lean_string_append(v___x_522_, v___x_523_);
lean_dec_ref(v___x_523_);
v___x_525_ = ((lean_object*)(l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval___closed__0));
v___x_526_ = lean_string_append(v___x_524_, v___x_525_);
v___x_527_ = lean_string_append(v_s_517_, v___x_526_);
lean_dec_ref(v___x_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lake_Toml_ppTable_spec__2(lean_object* v_msg_528_){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = ((lean_object*)(l_Lake_Toml_instInhabitedValue_default___closed__0));
v___x_530_ = lean_panic_fn_borrowed(v___x_529_, v_msg_528_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(lean_object* v_as_531_, size_t v_i_532_, size_t v_stop_533_, lean_object* v_b_534_){
_start:
{
uint8_t v___x_535_; 
v___x_535_ = lean_usize_dec_eq(v_i_532_, v_stop_533_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; lean_object* v_fst_537_; lean_object* v_snd_538_; lean_object* v___x_539_; size_t v___x_540_; size_t v___x_541_; 
v___x_536_ = lean_array_uget_borrowed(v_as_531_, v_i_532_);
v_fst_537_ = lean_ctor_get(v___x_536_, 0);
v_snd_538_ = lean_ctor_get(v___x_536_, 1);
lean_inc(v_snd_538_);
lean_inc(v_fst_537_);
v___x_539_ = l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval(v_b_534_, v_fst_537_, v_snd_538_);
v___x_540_ = ((size_t)1ULL);
v___x_541_ = lean_usize_add(v_i_532_, v___x_540_);
v_i_532_ = v___x_541_;
v_b_534_ = v___x_539_;
goto _start;
}
else
{
return v_b_534_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1___boxed(lean_object* v_as_543_, lean_object* v_i_544_, lean_object* v_stop_545_, lean_object* v_b_546_){
_start:
{
size_t v_i_boxed_547_; size_t v_stop_boxed_548_; lean_object* v_res_549_; 
v_i_boxed_547_ = lean_unbox_usize(v_i_544_);
lean_dec(v_i_544_);
v_stop_boxed_548_ = lean_unbox_usize(v_stop_545_);
lean_dec(v_stop_545_);
v_res_549_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_as_543_, v_i_boxed_547_, v_stop_boxed_548_, v_b_546_);
lean_dec_ref(v_as_543_);
return v_res_549_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_555_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__4));
v___x_556_ = lean_unsigned_to_nat(17u);
v___x_557_ = lean_unsigned_to_nat(128u);
v___x_558_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__3));
v___x_559_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__2));
v___x_560_ = l_mkPanicMessageWithDecl(v___x_559_, v___x_558_, v___x_557_, v___x_556_, v___x_555_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3(lean_object* v_fst_561_, lean_object* v_as_562_, size_t v_i_563_, size_t v_stop_564_, lean_object* v_b_565_){
_start:
{
lean_object* v___y_567_; lean_object* v___y_572_; uint8_t v___x_575_; 
v___x_575_ = lean_usize_dec_eq(v_i_563_, v_stop_564_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; 
v___x_576_ = lean_array_uget_borrowed(v_as_562_, v_i_563_);
if (lean_obj_tag(v___x_576_) == 6)
{
lean_object* v_xs_577_; lean_object* v_items_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v_s_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v_xs_577_ = lean_ctor_get(v___x_576_, 1);
v_items_578_ = lean_ctor_get(v_xs_577_, 0);
v___x_579_ = lean_unsigned_to_nat(0u);
v___x_580_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__0));
lean_inc(v_fst_561_);
v___x_581_ = l_Lake_Toml_ppKey(v_fst_561_);
v___x_582_ = lean_string_append(v___x_580_, v___x_581_);
lean_dec_ref(v___x_581_);
v___x_583_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__1));
v___x_584_ = lean_string_append(v___x_582_, v___x_583_);
v_s_585_ = lean_string_append(v_b_565_, v___x_584_);
lean_dec_ref(v___x_584_);
v___x_586_ = lean_array_get_size(v_items_578_);
v___x_587_ = lean_nat_dec_lt(v___x_579_, v___x_586_);
if (v___x_587_ == 0)
{
v___y_572_ = v_s_585_;
goto v___jp_571_;
}
else
{
uint8_t v___x_588_; 
v___x_588_ = lean_nat_dec_le(v___x_586_, v___x_586_);
if (v___x_588_ == 0)
{
if (v___x_587_ == 0)
{
v___y_572_ = v_s_585_;
goto v___jp_571_;
}
else
{
size_t v___x_589_; size_t v___x_590_; lean_object* v___x_591_; 
v___x_589_ = ((size_t)0ULL);
v___x_590_ = lean_usize_of_nat(v___x_586_);
v___x_591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_items_578_, v___x_589_, v___x_590_, v_s_585_);
v___y_572_ = v___x_591_;
goto v___jp_571_;
}
}
else
{
size_t v___x_592_; size_t v___x_593_; lean_object* v___x_594_; 
v___x_592_ = ((size_t)0ULL);
v___x_593_ = lean_usize_of_nat(v___x_586_);
v___x_594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_items_578_, v___x_592_, v___x_593_, v_s_585_);
v___y_572_ = v___x_594_;
goto v___jp_571_;
}
}
}
else
{
lean_object* v___x_595_; lean_object* v___x_596_; 
lean_dec_ref(v_b_565_);
v___x_595_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5);
v___x_596_ = l_panic___at___00Lake_Toml_ppTable_spec__2(v___x_595_);
v___y_567_ = v___x_596_;
goto v___jp_566_;
}
}
else
{
lean_dec(v_fst_561_);
return v_b_565_;
}
v___jp_566_:
{
size_t v___x_568_; size_t v___x_569_; 
v___x_568_ = ((size_t)1ULL);
v___x_569_ = lean_usize_add(v_i_563_, v___x_568_);
v_i_563_ = v___x_569_;
v_b_565_ = v___y_567_;
goto _start;
}
v___jp_571_:
{
uint32_t v___x_573_; lean_object* v___x_574_; 
v___x_573_ = 10;
v___x_574_ = lean_string_push(v___y_572_, v___x_573_);
v___y_567_ = v___x_574_;
goto v___jp_566_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___boxed(lean_object* v_fst_597_, lean_object* v_as_598_, lean_object* v_i_599_, lean_object* v_stop_600_, lean_object* v_b_601_){
_start:
{
size_t v_i_boxed_602_; size_t v_stop_boxed_603_; lean_object* v_res_604_; 
v_i_boxed_602_ = lean_unbox_usize(v_i_599_);
lean_dec(v_i_599_);
v_stop_boxed_603_ = lean_unbox_usize(v_stop_600_);
lean_dec(v_stop_600_);
v_res_604_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3(v_fst_597_, v_as_598_, v_i_boxed_602_, v_stop_boxed_603_, v_b_601_);
lean_dec_ref(v_as_598_);
return v_res_604_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Toml_ppTable_spec__4(lean_object* v___x_605_, lean_object* v_as_606_, size_t v_i_607_, size_t v_stop_608_){
_start:
{
uint8_t v___x_609_; 
v___x_609_ = lean_usize_dec_eq(v_i_607_, v_stop_608_);
if (v___x_609_ == 0)
{
uint8_t v___x_610_; lean_object* v___x_611_; 
v___x_610_ = 1;
v___x_611_ = lean_array_uget_borrowed(v_as_606_, v_i_607_);
if (lean_obj_tag(v___x_611_) == 6)
{
lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_612_ = lean_unsigned_to_nat(0u);
v___x_613_ = lean_nat_dec_eq(v___x_605_, v___x_612_);
if (v___x_613_ == 0)
{
size_t v___x_614_; size_t v___x_615_; 
v___x_614_ = ((size_t)1ULL);
v___x_615_ = lean_usize_add(v_i_607_, v___x_614_);
v_i_607_ = v___x_615_;
goto _start;
}
else
{
return v___x_610_;
}
}
else
{
return v___x_610_;
}
}
else
{
uint8_t v___x_617_; 
v___x_617_ = 0;
return v___x_617_;
}
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5(lean_object* v_as_628_, size_t v_i_629_, size_t v_stop_630_, lean_object* v_b_631_){
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
lean_dec_ref(v_snd_646_);
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
if (v___x_669_ == 0)
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
else
{
goto v___jp_654_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___boxed(lean_object* v_as_735_, lean_object* v_i_736_, lean_object* v_stop_737_, lean_object* v_b_738_){
_start:
{
size_t v_i_boxed_739_; size_t v_stop_boxed_740_; lean_object* v_res_741_; 
v_i_boxed_739_ = lean_unbox_usize(v_i_736_);
lean_dec(v_i_736_);
v_stop_boxed_740_ = lean_unbox_usize(v_stop_737_);
lean_dec(v_stop_737_);
v_res_741_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5(v_as_735_, v_i_boxed_739_, v_stop_boxed_740_, v_b_738_);
lean_dec_ref(v_as_735_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lake_Toml_ppTable_spec__0(lean_object* v_s_742_, lean_object* v_pos_743_){
_start:
{
lean_object* v_str_744_; lean_object* v_startInclusive_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; uint8_t v___x_749_; 
v_str_744_ = lean_ctor_get(v_s_742_, 0);
v_startInclusive_745_ = lean_ctor_get(v_s_742_, 1);
v___x_746_ = lean_nat_add(v_startInclusive_745_, v_pos_743_);
v___x_747_ = lean_nat_sub(v___x_746_, v_startInclusive_745_);
v___x_748_ = lean_unsigned_to_nat(0u);
v___x_749_ = lean_nat_dec_eq(v___x_747_, v___x_748_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; uint8_t v___y_758_; lean_object* v___x_759_; uint32_t v___x_760_; uint8_t v___y_762_; uint32_t v___x_767_; uint8_t v___x_768_; 
lean_inc(v_startInclusive_745_);
lean_inc_ref(v_str_744_);
v___x_750_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_750_, 0, v_str_744_);
lean_ctor_set(v___x_750_, 1, v_startInclusive_745_);
lean_ctor_set(v___x_750_, 2, v___x_746_);
v___x_751_ = lean_unsigned_to_nat(1u);
v___x_752_ = lean_nat_sub(v___x_747_, v___x_751_);
lean_dec(v___x_747_);
v___x_753_ = l_String_Slice_posLE(v___x_750_, v___x_752_);
lean_dec_ref(v___x_750_);
v___x_759_ = lean_nat_add(v_startInclusive_745_, v___x_753_);
v___x_760_ = lean_string_utf8_get_fast(v_str_744_, v___x_759_);
lean_dec(v___x_759_);
v___x_767_ = 32;
v___x_768_ = lean_uint32_dec_eq(v___x_760_, v___x_767_);
if (v___x_768_ == 0)
{
uint32_t v___x_769_; uint8_t v___x_770_; 
v___x_769_ = 9;
v___x_770_ = lean_uint32_dec_eq(v___x_760_, v___x_769_);
v___y_762_ = v___x_770_;
goto v___jp_761_;
}
else
{
v___y_762_ = v___x_768_;
goto v___jp_761_;
}
v___jp_754_:
{
uint8_t v___x_755_; 
v___x_755_ = lean_nat_dec_lt(v___x_753_, v_pos_743_);
if (v___x_755_ == 0)
{
lean_dec(v___x_753_);
return v_pos_743_;
}
else
{
lean_dec(v_pos_743_);
v_pos_743_ = v___x_753_;
goto _start;
}
}
v___jp_757_:
{
if (v___y_758_ == 0)
{
lean_dec(v___x_753_);
return v_pos_743_;
}
else
{
goto v___jp_754_;
}
}
v___jp_761_:
{
if (v___y_762_ == 0)
{
uint32_t v___x_763_; uint8_t v___x_764_; 
v___x_763_ = 13;
v___x_764_ = lean_uint32_dec_eq(v___x_760_, v___x_763_);
if (v___x_764_ == 0)
{
uint32_t v___x_765_; uint8_t v___x_766_; 
v___x_765_ = 10;
v___x_766_ = lean_uint32_dec_eq(v___x_760_, v___x_765_);
v___y_758_ = v___x_766_;
goto v___jp_757_;
}
else
{
v___y_758_ = v___x_764_;
goto v___jp_757_;
}
}
else
{
goto v___jp_754_;
}
}
}
else
{
lean_dec(v___x_747_);
lean_dec(v___x_746_);
return v_pos_743_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lake_Toml_ppTable_spec__0___boxed(lean_object* v_s_771_, lean_object* v_pos_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_String_Slice_Pos_revSkipWhile___at___00Lake_Toml_ppTable_spec__0(v_s_771_, v_pos_772_);
lean_dec_ref(v_s_771_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppTable(lean_object* v_t_776_){
_start:
{
lean_object* v_fst_778_; lean_object* v_snd_779_; lean_object* v___y_790_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v_items_795_; lean_object* v___x_796_; lean_object* v___x_797_; uint8_t v___x_798_; 
v___x_793_ = ((lean_object*)(l_Lake_Toml_instInhabitedValue_default___closed__0));
v___x_794_ = ((lean_object*)(l_Lake_Toml_ppTable___closed__0));
v_items_795_ = lean_ctor_get(v_t_776_, 0);
v___x_796_ = lean_unsigned_to_nat(0u);
v___x_797_ = lean_array_get_size(v_items_795_);
v___x_798_ = lean_nat_dec_lt(v___x_796_, v___x_797_);
if (v___x_798_ == 0)
{
v_fst_778_ = v___x_793_;
v_snd_779_ = v___x_793_;
goto v___jp_777_;
}
else
{
uint8_t v___x_799_; 
v___x_799_ = lean_nat_dec_le(v___x_797_, v___x_797_);
if (v___x_799_ == 0)
{
if (v___x_798_ == 0)
{
v_fst_778_ = v___x_793_;
v_snd_779_ = v___x_793_;
goto v___jp_777_;
}
else
{
size_t v___x_800_; size_t v___x_801_; lean_object* v___x_802_; 
v___x_800_ = ((size_t)0ULL);
v___x_801_ = lean_usize_of_nat(v___x_797_);
v___x_802_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5(v_items_795_, v___x_800_, v___x_801_, v___x_794_);
v___y_790_ = v___x_802_;
goto v___jp_789_;
}
}
else
{
size_t v___x_803_; size_t v___x_804_; lean_object* v___x_805_; 
v___x_803_ = ((size_t)0ULL);
v___x_804_ = lean_usize_of_nat(v___x_797_);
v___x_805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5(v_items_795_, v___x_803_, v___x_804_, v___x_794_);
v___y_790_ = v___x_805_;
goto v___jp_789_;
}
}
v___jp_777_:
{
uint32_t v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_780_ = 10;
v___x_781_ = lean_string_push(v_fst_778_, v___x_780_);
v___x_782_ = lean_string_append(v___x_781_, v_snd_779_);
lean_dec_ref(v_snd_779_);
v___x_783_ = lean_unsigned_to_nat(0u);
v___x_784_ = lean_string_utf8_byte_size(v___x_782_);
lean_inc_ref(v___x_782_);
v___x_785_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_785_, 0, v___x_782_);
lean_ctor_set(v___x_785_, 1, v___x_783_);
lean_ctor_set(v___x_785_, 2, v___x_784_);
v___x_786_ = l_String_Slice_Pos_revSkipWhile___at___00Lake_Toml_ppTable_spec__0(v___x_785_, v___x_784_);
lean_dec_ref(v___x_785_);
v___x_787_ = lean_string_utf8_extract(v___x_782_, v___x_783_, v___x_786_);
lean_dec(v___x_786_);
lean_dec_ref(v___x_782_);
v___x_788_ = lean_string_push(v___x_787_, v___x_780_);
return v___x_788_;
}
v___jp_789_:
{
lean_object* v_fst_791_; lean_object* v_snd_792_; 
v_fst_791_ = lean_ctor_get(v___y_790_, 0);
lean_inc(v_fst_791_);
v_snd_792_ = lean_ctor_get(v___y_790_, 1);
lean_inc(v_snd_792_);
lean_dec_ref(v___y_790_);
v_fst_778_ = v_fst_791_;
v_snd_779_ = v_snd_792_;
goto v___jp_777_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppTable___boxed(lean_object* v_t_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Lake_Toml_ppTable(v_t_806_);
lean_dec_ref(v_t_806_);
return v_res_807_;
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

// Lean compiler output
// Module: Lake.Util.Url
// Imports: public import Lake.Util.Log import Lake.Util.JsonObject import Lake.Util.Proc import Init.Data.String.TakeDrop import Init.Data.String.Search import Init.TacticsExtra
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
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_shift_right(uint32_t, uint32_t);
uint8_t lean_uint32_to_uint8(uint32_t);
uint8_t lean_uint8_land(uint8_t, uint8_t);
uint8_t lean_uint8_lor(uint8_t, uint8_t);
lean_object* lean_string_push(lean_object*, uint32_t);
uint8_t lean_uint8_shift_right(uint8_t, uint8_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JsonObject_getJson_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
lean_object* l_Lake_captureProc_x27(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_String_Slice_positions(lean_object*);
LEAN_EXPORT uint32_t l_Lake_hexEncodeByte(uint8_t);
LEAN_EXPORT lean_object* l_Lake_hexEncodeByte___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_uriEscapeByte(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_uriEscapeByte___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__0(uint32_t, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__1(uint32_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__2(uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__4(uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__3(uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg(lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M(lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___redArg___lam__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_foldlUtf8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_foldlUtf8___redArg___closed__0 = (const lean_object*)&l_Lake_foldlUtf8___redArg___closed__0_value;
static const lean_closure_object l_Lake_foldlUtf8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_foldlUtf8___redArg___closed__1 = (const lean_object*)&l_Lake_foldlUtf8___redArg___closed__1_value;
static const lean_closure_object l_Lake_foldlUtf8___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_foldlUtf8___redArg___closed__2 = (const lean_object*)&l_Lake_foldlUtf8___redArg___closed__2_value;
static const lean_closure_object l_Lake_foldlUtf8___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_foldlUtf8___redArg___closed__3 = (const lean_object*)&l_Lake_foldlUtf8___redArg___closed__3_value;
static const lean_closure_object l_Lake_foldlUtf8___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_foldlUtf8___redArg___closed__4 = (const lean_object*)&l_Lake_foldlUtf8___redArg___closed__4_value;
static const lean_closure_object l_Lake_foldlUtf8___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_foldlUtf8___redArg___closed__5 = (const lean_object*)&l_Lake_foldlUtf8___redArg___closed__5_value;
static const lean_closure_object l_Lake_foldlUtf8___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_foldlUtf8___redArg___closed__6 = (const lean_object*)&l_Lake_foldlUtf8___redArg___closed__6_value;
static const lean_ctor_object l_Lake_foldlUtf8___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_foldlUtf8___redArg___closed__0_value),((lean_object*)&l_Lake_foldlUtf8___redArg___closed__1_value)}};
static const lean_object* l_Lake_foldlUtf8___redArg___closed__7 = (const lean_object*)&l_Lake_foldlUtf8___redArg___closed__7_value;
static const lean_ctor_object l_Lake_foldlUtf8___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_foldlUtf8___redArg___closed__7_value),((lean_object*)&l_Lake_foldlUtf8___redArg___closed__2_value),((lean_object*)&l_Lake_foldlUtf8___redArg___closed__3_value),((lean_object*)&l_Lake_foldlUtf8___redArg___closed__4_value),((lean_object*)&l_Lake_foldlUtf8___redArg___closed__5_value)}};
static const lean_object* l_Lake_foldlUtf8___redArg___closed__8 = (const lean_object*)&l_Lake_foldlUtf8___redArg___closed__8_value;
static const lean_ctor_object l_Lake_foldlUtf8___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_foldlUtf8___redArg___closed__8_value),((lean_object*)&l_Lake_foldlUtf8___redArg___closed__6_value)}};
static const lean_object* l_Lake_foldlUtf8___redArg___closed__9 = (const lean_object*)&l_Lake_foldlUtf8___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___redArg(uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8(lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___at___00Lake_uriEscapeChar_spec__0(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___at___00Lake_uriEscapeChar_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_uriEscapeChar(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_uriEscapeChar___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_isUriUnreservedMark(uint32_t);
LEAN_EXPORT lean_object* l_Lake_isUriUnreservedMark___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_uriEncodeChar(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_uriEncodeChar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_uriEncode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-H"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_getUrl_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "curl's JSON output contained an invalid JSON response code: "};
static const lean_object* l_Lake_getUrl_x3f___closed__0 = (const lean_object*)&l_Lake_getUrl_x3f___closed__0_value;
static const lean_string_object l_Lake_getUrl_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "curl's JSON output did not contain a response code"};
static const lean_object* l_Lake_getUrl_x3f___closed__1 = (const lean_object*)&l_Lake_getUrl_x3f___closed__1_value;
static const lean_ctor_object l_Lake_getUrl_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_getUrl_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(3, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_getUrl_x3f___closed__2 = (const lean_object*)&l_Lake_getUrl_x3f___closed__2_value;
static const lean_string_object l_Lake_getUrl_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "curl produced invalid JSON output: "};
static const lean_object* l_Lake_getUrl_x3f___closed__3 = (const lean_object*)&l_Lake_getUrl_x3f___closed__3_value;
static const lean_string_object l_Lake_getUrl_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "failed to GET URL, error "};
static const lean_object* l_Lake_getUrl_x3f___closed__4 = (const lean_object*)&l_Lake_getUrl_x3f___closed__4_value;
static const lean_string_object l_Lake_getUrl_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "; received:\n"};
static const lean_object* l_Lake_getUrl_x3f___closed__5 = (const lean_object*)&l_Lake_getUrl_x3f___closed__5_value;
static const lean_string_object l_Lake_getUrl_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "http_code"};
static const lean_object* l_Lake_getUrl_x3f___closed__6 = (const lean_object*)&l_Lake_getUrl_x3f___closed__6_value;
static const lean_string_object l_Lake_getUrl_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "http_code: "};
static const lean_object* l_Lake_getUrl_x3f___closed__7 = (const lean_object*)&l_Lake_getUrl_x3f___closed__7_value;
static const lean_ctor_object l_Lake_getUrl_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_getUrl_x3f___closed__8 = (const lean_object*)&l_Lake_getUrl_x3f___closed__8_value;
static const lean_string_object l_Lake_getUrl_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "curl"};
static const lean_object* l_Lake_getUrl_x3f___closed__9 = (const lean_object*)&l_Lake_getUrl_x3f___closed__9_value;
static const lean_array_object l_Lake_getUrl_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_getUrl_x3f___closed__10 = (const lean_object*)&l_Lake_getUrl_x3f___closed__10_value;
static const lean_string_object l_Lake_getUrl_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "response_code"};
static const lean_object* l_Lake_getUrl_x3f___closed__11 = (const lean_object*)&l_Lake_getUrl_x3f___closed__11_value;
static const lean_string_object l_Lake_getUrl_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-s"};
static const lean_object* l_Lake_getUrl_x3f___closed__12 = (const lean_object*)&l_Lake_getUrl_x3f___closed__12_value;
static const lean_string_object l_Lake_getUrl_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-L"};
static const lean_object* l_Lake_getUrl_x3f___closed__13 = (const lean_object*)&l_Lake_getUrl_x3f___closed__13_value;
static const lean_string_object l_Lake_getUrl_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-w"};
static const lean_object* l_Lake_getUrl_x3f___closed__14 = (const lean_object*)&l_Lake_getUrl_x3f___closed__14_value;
static const lean_string_object l_Lake_getUrl_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "%{stderr}%{json}\n"};
static const lean_object* l_Lake_getUrl_x3f___closed__15 = (const lean_object*)&l_Lake_getUrl_x3f___closed__15_value;
static const lean_string_object l_Lake_getUrl_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "--retry"};
static const lean_object* l_Lake_getUrl_x3f___closed__16 = (const lean_object*)&l_Lake_getUrl_x3f___closed__16_value;
static const lean_string_object l_Lake_getUrl_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "3"};
static const lean_object* l_Lake_getUrl_x3f___closed__17 = (const lean_object*)&l_Lake_getUrl_x3f___closed__17_value;
static const lean_array_object l_Lake_getUrl_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l_Lake_getUrl_x3f___closed__12_value),((lean_object*)&l_Lake_getUrl_x3f___closed__13_value),((lean_object*)&l_Lake_getUrl_x3f___closed__14_value),((lean_object*)&l_Lake_getUrl_x3f___closed__15_value),((lean_object*)&l_Lake_getUrl_x3f___closed__16_value),((lean_object*)&l_Lake_getUrl_x3f___closed__17_value)}};
static const lean_object* l_Lake_getUrl_x3f___closed__18 = (const lean_object*)&l_Lake_getUrl_x3f___closed__18_value;
LEAN_EXPORT lean_object* l_Lake_getUrl_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getUrl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_getUrl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_Lake_getUrl_x3f___closed__12_value),((lean_object*)&l_Lake_getUrl_x3f___closed__13_value),((lean_object*)&l_Lake_getUrl_x3f___closed__16_value),((lean_object*)&l_Lake_getUrl_x3f___closed__17_value)}};
static const lean_object* l_Lake_getUrl___closed__0 = (const lean_object*)&l_Lake_getUrl___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getUrl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getUrl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lake_hexEncodeByte(uint8_t v_b_1_){
_start:
{
uint8_t v___x_2_; uint8_t v___x_3_; 
v___x_2_ = 0;
v___x_3_ = lean_uint8_dec_eq(v_b_1_, v___x_2_);
if (v___x_3_ == 0)
{
uint8_t v___x_4_; uint8_t v___x_5_; 
v___x_4_ = 1;
v___x_5_ = lean_uint8_dec_eq(v_b_1_, v___x_4_);
if (v___x_5_ == 0)
{
uint8_t v___x_6_; uint8_t v___x_7_; 
v___x_6_ = 2;
v___x_7_ = lean_uint8_dec_eq(v_b_1_, v___x_6_);
if (v___x_7_ == 0)
{
uint8_t v___x_8_; uint8_t v___x_9_; 
v___x_8_ = 3;
v___x_9_ = lean_uint8_dec_eq(v_b_1_, v___x_8_);
if (v___x_9_ == 0)
{
uint8_t v___x_10_; uint8_t v___x_11_; 
v___x_10_ = 4;
v___x_11_ = lean_uint8_dec_eq(v_b_1_, v___x_10_);
if (v___x_11_ == 0)
{
uint8_t v___x_12_; uint8_t v___x_13_; 
v___x_12_ = 5;
v___x_13_ = lean_uint8_dec_eq(v_b_1_, v___x_12_);
if (v___x_13_ == 0)
{
uint8_t v___x_14_; uint8_t v___x_15_; 
v___x_14_ = 6;
v___x_15_ = lean_uint8_dec_eq(v_b_1_, v___x_14_);
if (v___x_15_ == 0)
{
uint8_t v___x_16_; uint8_t v___x_17_; 
v___x_16_ = 7;
v___x_17_ = lean_uint8_dec_eq(v_b_1_, v___x_16_);
if (v___x_17_ == 0)
{
uint8_t v___x_18_; uint8_t v___x_19_; 
v___x_18_ = 8;
v___x_19_ = lean_uint8_dec_eq(v_b_1_, v___x_18_);
if (v___x_19_ == 0)
{
uint8_t v___x_20_; uint8_t v___x_21_; 
v___x_20_ = 9;
v___x_21_ = lean_uint8_dec_eq(v_b_1_, v___x_20_);
if (v___x_21_ == 0)
{
uint8_t v___x_22_; uint8_t v___x_23_; 
v___x_22_ = 10;
v___x_23_ = lean_uint8_dec_eq(v_b_1_, v___x_22_);
if (v___x_23_ == 0)
{
uint8_t v___x_24_; uint8_t v___x_25_; 
v___x_24_ = 11;
v___x_25_ = lean_uint8_dec_eq(v_b_1_, v___x_24_);
if (v___x_25_ == 0)
{
uint8_t v___x_26_; uint8_t v___x_27_; 
v___x_26_ = 12;
v___x_27_ = lean_uint8_dec_eq(v_b_1_, v___x_26_);
if (v___x_27_ == 0)
{
uint8_t v___x_28_; uint8_t v___x_29_; 
v___x_28_ = 13;
v___x_29_ = lean_uint8_dec_eq(v_b_1_, v___x_28_);
if (v___x_29_ == 0)
{
uint8_t v___x_30_; uint8_t v___x_31_; 
v___x_30_ = 14;
v___x_31_ = lean_uint8_dec_eq(v_b_1_, v___x_30_);
if (v___x_31_ == 0)
{
uint8_t v___x_32_; uint8_t v___x_33_; 
v___x_32_ = 15;
v___x_33_ = lean_uint8_dec_eq(v_b_1_, v___x_32_);
if (v___x_33_ == 0)
{
uint32_t v___x_34_; 
v___x_34_ = 42;
return v___x_34_;
}
else
{
uint32_t v___x_35_; 
v___x_35_ = 70;
return v___x_35_;
}
}
else
{
uint32_t v___x_36_; 
v___x_36_ = 69;
return v___x_36_;
}
}
else
{
uint32_t v___x_37_; 
v___x_37_ = 68;
return v___x_37_;
}
}
else
{
uint32_t v___x_38_; 
v___x_38_ = 67;
return v___x_38_;
}
}
else
{
uint32_t v___x_39_; 
v___x_39_ = 66;
return v___x_39_;
}
}
else
{
uint32_t v___x_40_; 
v___x_40_ = 65;
return v___x_40_;
}
}
else
{
uint32_t v___x_41_; 
v___x_41_ = 57;
return v___x_41_;
}
}
else
{
uint32_t v___x_42_; 
v___x_42_ = 56;
return v___x_42_;
}
}
else
{
uint32_t v___x_43_; 
v___x_43_ = 55;
return v___x_43_;
}
}
else
{
uint32_t v___x_44_; 
v___x_44_ = 54;
return v___x_44_;
}
}
else
{
uint32_t v___x_45_; 
v___x_45_ = 53;
return v___x_45_;
}
}
else
{
uint32_t v___x_46_; 
v___x_46_ = 52;
return v___x_46_;
}
}
else
{
uint32_t v___x_47_; 
v___x_47_ = 51;
return v___x_47_;
}
}
else
{
uint32_t v___x_48_; 
v___x_48_ = 50;
return v___x_48_;
}
}
else
{
uint32_t v___x_49_; 
v___x_49_ = 49;
return v___x_49_;
}
}
else
{
uint32_t v___x_50_; 
v___x_50_ = 48;
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_hexEncodeByte___boxed(lean_object* v_b_51_){
_start:
{
uint8_t v_b_boxed_52_; uint32_t v_res_53_; lean_object* v_r_54_; 
v_b_boxed_52_ = lean_unbox(v_b_51_);
v_res_53_ = l_Lake_hexEncodeByte(v_b_boxed_52_);
v_r_54_ = lean_box_uint32(v_res_53_);
return v_r_54_;
}
}
LEAN_EXPORT lean_object* l_Lake_uriEscapeByte(uint8_t v_b_55_, lean_object* v_s_56_){
_start:
{
uint32_t v___x_57_; lean_object* v___x_58_; uint8_t v___x_59_; uint8_t v___x_60_; uint32_t v___x_61_; lean_object* v___x_62_; uint8_t v___x_63_; uint8_t v___x_64_; uint32_t v___x_65_; lean_object* v___x_66_; 
v___x_57_ = 37;
v___x_58_ = lean_string_push(v_s_56_, v___x_57_);
v___x_59_ = 4;
v___x_60_ = lean_uint8_shift_right(v_b_55_, v___x_59_);
v___x_61_ = l_Lake_hexEncodeByte(v___x_60_);
v___x_62_ = lean_string_push(v___x_58_, v___x_61_);
v___x_63_ = 15;
v___x_64_ = lean_uint8_land(v_b_55_, v___x_63_);
v___x_65_ = l_Lake_hexEncodeByte(v___x_64_);
v___x_66_ = lean_string_push(v___x_62_, v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lake_uriEscapeByte___boxed(lean_object* v_b_67_, lean_object* v_s_68_){
_start:
{
uint8_t v_b_boxed_69_; lean_object* v_res_70_; 
v_b_boxed_69_ = lean_unbox(v_b_67_);
v_res_70_ = l_Lake_uriEscapeByte(v_b_boxed_69_, v_s_68_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__0(uint32_t v_c_71_, uint8_t v___x_72_, uint8_t v___x_73_, lean_object* v_f_74_, lean_object* v_s_75_){
_start:
{
uint8_t v___x_76_; uint8_t v___x_77_; uint8_t v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_76_ = lean_uint32_to_uint8(v_c_71_);
v___x_77_ = lean_uint8_land(v___x_76_, v___x_72_);
v___x_78_ = lean_uint8_lor(v___x_77_, v___x_73_);
v___x_79_ = lean_box(v___x_78_);
v___x_80_ = lean_apply_2(v_f_74_, v_s_75_, v___x_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__0___boxed(lean_object* v_c_81_, lean_object* v___x_82_, lean_object* v___x_83_, lean_object* v_f_84_, lean_object* v_s_85_){
_start:
{
uint32_t v_c_boxed_86_; uint8_t v___x_393__boxed_87_; uint8_t v___x_394__boxed_88_; lean_object* v_res_89_; 
v_c_boxed_86_ = lean_unbox_uint32(v_c_81_);
lean_dec(v_c_81_);
v___x_393__boxed_87_ = lean_unbox(v___x_82_);
v___x_394__boxed_88_ = lean_unbox(v___x_83_);
v_res_89_ = l_Lake_foldlUtf8M___redArg___lam__0(v_c_boxed_86_, v___x_393__boxed_87_, v___x_394__boxed_88_, v_f_84_, v_s_85_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__1(uint32_t v_c_90_, uint8_t v___x_91_, uint8_t v___x_92_, lean_object* v_f_93_, lean_object* v_toBind_94_, lean_object* v___f_95_, lean_object* v_s_96_){
_start:
{
uint32_t v___x_97_; uint32_t v___x_98_; uint8_t v___x_99_; uint8_t v___x_100_; uint8_t v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_97_ = 6;
v___x_98_ = lean_uint32_shift_right(v_c_90_, v___x_97_);
v___x_99_ = lean_uint32_to_uint8(v___x_98_);
v___x_100_ = lean_uint8_land(v___x_99_, v___x_91_);
v___x_101_ = lean_uint8_lor(v___x_100_, v___x_92_);
v___x_102_ = lean_box(v___x_101_);
v___x_103_ = lean_apply_2(v_f_93_, v_s_96_, v___x_102_);
v___x_104_ = lean_apply_4(v_toBind_94_, lean_box(0), lean_box(0), v___x_103_, v___f_95_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__1___boxed(lean_object* v_c_105_, lean_object* v___x_106_, lean_object* v___x_107_, lean_object* v_f_108_, lean_object* v_toBind_109_, lean_object* v___f_110_, lean_object* v_s_111_){
_start:
{
uint32_t v_c_boxed_112_; uint8_t v___x_409__boxed_113_; uint8_t v___x_410__boxed_114_; lean_object* v_res_115_; 
v_c_boxed_112_ = lean_unbox_uint32(v_c_105_);
lean_dec(v_c_105_);
v___x_409__boxed_113_ = lean_unbox(v___x_106_);
v___x_410__boxed_114_ = lean_unbox(v___x_107_);
v_res_115_ = l_Lake_foldlUtf8M___redArg___lam__1(v_c_boxed_112_, v___x_409__boxed_113_, v___x_410__boxed_114_, v_f_108_, v_toBind_109_, v___f_110_, v_s_111_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__2(uint32_t v_c_116_, lean_object* v_f_117_, lean_object* v_toBind_118_, lean_object* v_s_119_){
_start:
{
uint32_t v___x_120_; uint32_t v___x_121_; uint8_t v___x_122_; uint8_t v___x_123_; uint8_t v___x_124_; uint8_t v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___f_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___f_133_; uint8_t v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_120_ = 12;
v___x_121_ = lean_uint32_shift_right(v_c_116_, v___x_120_);
v___x_122_ = lean_uint32_to_uint8(v___x_121_);
v___x_123_ = 63;
v___x_124_ = lean_uint8_land(v___x_122_, v___x_123_);
v___x_125_ = 128;
v___x_126_ = lean_box_uint32(v_c_116_);
v___x_127_ = lean_box(v___x_123_);
v___x_128_ = lean_box(v___x_125_);
lean_inc_n(v_f_117_, 2);
v___f_129_ = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_129_, 0, v___x_126_);
lean_closure_set(v___f_129_, 1, v___x_127_);
lean_closure_set(v___f_129_, 2, v___x_128_);
lean_closure_set(v___f_129_, 3, v_f_117_);
v___x_130_ = lean_box_uint32(v_c_116_);
v___x_131_ = lean_box(v___x_123_);
v___x_132_ = lean_box(v___x_125_);
lean_inc(v_toBind_118_);
v___f_133_ = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_133_, 0, v___x_130_);
lean_closure_set(v___f_133_, 1, v___x_131_);
lean_closure_set(v___f_133_, 2, v___x_132_);
lean_closure_set(v___f_133_, 3, v_f_117_);
lean_closure_set(v___f_133_, 4, v_toBind_118_);
lean_closure_set(v___f_133_, 5, v___f_129_);
v___x_134_ = lean_uint8_lor(v___x_124_, v___x_125_);
v___x_135_ = lean_box(v___x_134_);
v___x_136_ = lean_apply_2(v_f_117_, v_s_119_, v___x_135_);
v___x_137_ = lean_apply_4(v_toBind_118_, lean_box(0), lean_box(0), v___x_136_, v___f_133_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__2___boxed(lean_object* v_c_138_, lean_object* v_f_139_, lean_object* v_toBind_140_, lean_object* v_s_141_){
_start:
{
uint32_t v_c_boxed_142_; lean_object* v_res_143_; 
v_c_boxed_142_ = lean_unbox_uint32(v_c_138_);
lean_dec(v_c_138_);
v_res_143_ = l_Lake_foldlUtf8M___redArg___lam__2(v_c_boxed_142_, v_f_139_, v_toBind_140_, v_s_141_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__4(uint32_t v_c_144_, lean_object* v_f_145_, lean_object* v_toBind_146_, lean_object* v_s_147_){
_start:
{
uint32_t v___x_148_; uint32_t v___x_149_; uint8_t v___x_150_; uint8_t v___x_151_; uint8_t v___x_152_; uint8_t v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___f_157_; uint8_t v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_148_ = 6;
v___x_149_ = lean_uint32_shift_right(v_c_144_, v___x_148_);
v___x_150_ = lean_uint32_to_uint8(v___x_149_);
v___x_151_ = 63;
v___x_152_ = lean_uint8_land(v___x_150_, v___x_151_);
v___x_153_ = 128;
v___x_154_ = lean_box_uint32(v_c_144_);
v___x_155_ = lean_box(v___x_151_);
v___x_156_ = lean_box(v___x_153_);
lean_inc(v_f_145_);
v___f_157_ = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_157_, 0, v___x_154_);
lean_closure_set(v___f_157_, 1, v___x_155_);
lean_closure_set(v___f_157_, 2, v___x_156_);
lean_closure_set(v___f_157_, 3, v_f_145_);
v___x_158_ = lean_uint8_lor(v___x_152_, v___x_153_);
v___x_159_ = lean_box(v___x_158_);
v___x_160_ = lean_apply_2(v_f_145_, v_s_147_, v___x_159_);
v___x_161_ = lean_apply_4(v_toBind_146_, lean_box(0), lean_box(0), v___x_160_, v___f_157_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__4___boxed(lean_object* v_c_162_, lean_object* v_f_163_, lean_object* v_toBind_164_, lean_object* v_s_165_){
_start:
{
uint32_t v_c_boxed_166_; lean_object* v_res_167_; 
v_c_boxed_166_ = lean_unbox_uint32(v_c_162_);
lean_dec(v_c_162_);
v_res_167_ = l_Lake_foldlUtf8M___redArg___lam__4(v_c_boxed_166_, v_f_163_, v_toBind_164_, v_s_165_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__3(uint32_t v_c_168_, lean_object* v_f_169_, lean_object* v_s_170_){
_start:
{
uint8_t v___x_171_; uint8_t v___x_172_; uint8_t v___x_173_; uint8_t v___x_174_; uint8_t v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_171_ = lean_uint32_to_uint8(v_c_168_);
v___x_172_ = 63;
v___x_173_ = lean_uint8_land(v___x_171_, v___x_172_);
v___x_174_ = 128;
v___x_175_ = lean_uint8_lor(v___x_173_, v___x_174_);
v___x_176_ = lean_box(v___x_175_);
v___x_177_ = lean_apply_2(v_f_169_, v_s_170_, v___x_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__3___boxed(lean_object* v_c_178_, lean_object* v_f_179_, lean_object* v_s_180_){
_start:
{
uint32_t v_c_boxed_181_; lean_object* v_res_182_; 
v_c_boxed_181_ = lean_unbox_uint32(v_c_178_);
lean_dec(v_c_178_);
v_res_182_ = l_Lake_foldlUtf8M___redArg___lam__3(v_c_boxed_181_, v_f_179_, v_s_180_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg(lean_object* v_inst_183_, uint32_t v_c_184_, lean_object* v_f_185_, lean_object* v_init_186_){
_start:
{
uint32_t v___x_187_; uint8_t v___x_188_; 
v___x_187_ = 127;
v___x_188_ = lean_uint32_dec_le(v_c_184_, v___x_187_);
if (v___x_188_ == 0)
{
uint32_t v___x_189_; uint8_t v___x_190_; 
v___x_189_ = 2047;
v___x_190_ = lean_uint32_dec_le(v_c_184_, v___x_189_);
if (v___x_190_ == 0)
{
uint32_t v___x_191_; uint8_t v___x_192_; 
v___x_191_ = 65535;
v___x_192_ = lean_uint32_dec_le(v_c_184_, v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v_toBind_193_; lean_object* v___x_194_; lean_object* v___f_195_; uint32_t v___x_196_; uint32_t v___x_197_; uint8_t v___x_198_; uint8_t v___x_199_; uint8_t v___x_200_; uint8_t v___x_201_; uint8_t v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v_toBind_193_ = lean_ctor_get(v_inst_183_, 1);
lean_inc_n(v_toBind_193_, 2);
lean_dec_ref(v_inst_183_);
v___x_194_ = lean_box_uint32(v_c_184_);
lean_inc(v_f_185_);
v___f_195_ = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_195_, 0, v___x_194_);
lean_closure_set(v___f_195_, 1, v_f_185_);
lean_closure_set(v___f_195_, 2, v_toBind_193_);
v___x_196_ = 18;
v___x_197_ = lean_uint32_shift_right(v_c_184_, v___x_196_);
v___x_198_ = lean_uint32_to_uint8(v___x_197_);
v___x_199_ = 7;
v___x_200_ = lean_uint8_land(v___x_198_, v___x_199_);
v___x_201_ = 240;
v___x_202_ = lean_uint8_lor(v___x_200_, v___x_201_);
v___x_203_ = lean_box(v___x_202_);
v___x_204_ = lean_apply_2(v_f_185_, v_init_186_, v___x_203_);
v___x_205_ = lean_apply_4(v_toBind_193_, lean_box(0), lean_box(0), v___x_204_, v___f_195_);
return v___x_205_;
}
else
{
lean_object* v_toBind_206_; lean_object* v___x_207_; lean_object* v___f_208_; uint32_t v___x_209_; uint32_t v___x_210_; uint8_t v___x_211_; uint8_t v___x_212_; uint8_t v___x_213_; uint8_t v___x_214_; uint8_t v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v_toBind_206_ = lean_ctor_get(v_inst_183_, 1);
lean_inc_n(v_toBind_206_, 2);
lean_dec_ref(v_inst_183_);
v___x_207_ = lean_box_uint32(v_c_184_);
lean_inc(v_f_185_);
v___f_208_ = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_208_, 0, v___x_207_);
lean_closure_set(v___f_208_, 1, v_f_185_);
lean_closure_set(v___f_208_, 2, v_toBind_206_);
v___x_209_ = 12;
v___x_210_ = lean_uint32_shift_right(v_c_184_, v___x_209_);
v___x_211_ = lean_uint32_to_uint8(v___x_210_);
v___x_212_ = 15;
v___x_213_ = lean_uint8_land(v___x_211_, v___x_212_);
v___x_214_ = 224;
v___x_215_ = lean_uint8_lor(v___x_213_, v___x_214_);
v___x_216_ = lean_box(v___x_215_);
v___x_217_ = lean_apply_2(v_f_185_, v_init_186_, v___x_216_);
v___x_218_ = lean_apply_4(v_toBind_206_, lean_box(0), lean_box(0), v___x_217_, v___f_208_);
return v___x_218_;
}
}
else
{
lean_object* v_toBind_219_; lean_object* v___x_220_; lean_object* v___f_221_; uint32_t v___x_222_; uint32_t v___x_223_; uint8_t v___x_224_; uint8_t v___x_225_; uint8_t v___x_226_; uint8_t v___x_227_; uint8_t v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v_toBind_219_ = lean_ctor_get(v_inst_183_, 1);
lean_inc(v_toBind_219_);
lean_dec_ref(v_inst_183_);
v___x_220_ = lean_box_uint32(v_c_184_);
lean_inc(v_f_185_);
v___f_221_ = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_221_, 0, v___x_220_);
lean_closure_set(v___f_221_, 1, v_f_185_);
v___x_222_ = 6;
v___x_223_ = lean_uint32_shift_right(v_c_184_, v___x_222_);
v___x_224_ = lean_uint32_to_uint8(v___x_223_);
v___x_225_ = 31;
v___x_226_ = lean_uint8_land(v___x_224_, v___x_225_);
v___x_227_ = 192;
v___x_228_ = lean_uint8_lor(v___x_226_, v___x_227_);
v___x_229_ = lean_box(v___x_228_);
v___x_230_ = lean_apply_2(v_f_185_, v_init_186_, v___x_229_);
v___x_231_ = lean_apply_4(v_toBind_219_, lean_box(0), lean_box(0), v___x_230_, v___f_221_);
return v___x_231_;
}
}
else
{
uint8_t v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
lean_dec_ref(v_inst_183_);
v___x_232_ = lean_uint32_to_uint8(v_c_184_);
v___x_233_ = lean_box(v___x_232_);
v___x_234_ = lean_apply_2(v_f_185_, v_init_186_, v___x_233_);
return v___x_234_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___boxed(lean_object* v_inst_235_, lean_object* v_c_236_, lean_object* v_f_237_, lean_object* v_init_238_){
_start:
{
uint32_t v_c_boxed_239_; lean_object* v_res_240_; 
v_c_boxed_239_ = lean_unbox_uint32(v_c_236_);
lean_dec(v_c_236_);
v_res_240_ = l_Lake_foldlUtf8M___redArg(v_inst_235_, v_c_boxed_239_, v_f_237_, v_init_238_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M(lean_object* v_m_241_, lean_object* v_00_u03c3_242_, lean_object* v_inst_243_, uint32_t v_c_244_, lean_object* v_f_245_, lean_object* v_init_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Lake_foldlUtf8M___redArg(v_inst_243_, v_c_244_, v_f_245_, v_init_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___boxed(lean_object* v_m_248_, lean_object* v_00_u03c3_249_, lean_object* v_inst_250_, lean_object* v_c_251_, lean_object* v_f_252_, lean_object* v_init_253_){
_start:
{
uint32_t v_c_boxed_254_; lean_object* v_res_255_; 
v_c_boxed_254_ = lean_unbox_uint32(v_c_251_);
lean_dec(v_c_251_);
v_res_255_ = l_Lake_foldlUtf8M(v_m_248_, v_00_u03c3_249_, v_inst_250_, v_c_boxed_254_, v_f_252_, v_init_253_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___redArg___lam__0(lean_object* v_f_256_, lean_object* v_x1_257_, uint8_t v_x2_258_){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_box(v_x2_258_);
v___x_260_ = lean_apply_2(v_f_256_, v_x1_257_, v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___redArg___lam__0___boxed(lean_object* v_f_261_, lean_object* v_x1_262_, lean_object* v_x2_263_){
_start:
{
uint8_t v_x2_83__boxed_264_; lean_object* v_res_265_; 
v_x2_83__boxed_264_ = lean_unbox(v_x2_263_);
v_res_265_ = l_Lake_foldlUtf8___redArg___lam__0(v_f_261_, v_x1_262_, v_x2_83__boxed_264_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___redArg(uint32_t v_c_285_, lean_object* v_f_286_, lean_object* v_init_287_){
_start:
{
lean_object* v___f_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___f_288_ = lean_alloc_closure((void*)(l_Lake_foldlUtf8___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_288_, 0, v_f_286_);
v___x_289_ = ((lean_object*)(l_Lake_foldlUtf8___redArg___closed__9));
v___x_290_ = l_Lake_foldlUtf8M___redArg(v___x_289_, v_c_285_, v___f_288_, v_init_287_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___redArg___boxed(lean_object* v_c_291_, lean_object* v_f_292_, lean_object* v_init_293_){
_start:
{
uint32_t v_c_boxed_294_; lean_object* v_res_295_; 
v_c_boxed_294_ = lean_unbox_uint32(v_c_291_);
lean_dec(v_c_291_);
v_res_295_ = l_Lake_foldlUtf8___redArg(v_c_boxed_294_, v_f_292_, v_init_293_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8(lean_object* v_00_u03c3_296_, uint32_t v_c_297_, lean_object* v_f_298_, lean_object* v_init_299_){
_start:
{
lean_object* v___f_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___f_300_ = lean_alloc_closure((void*)(l_Lake_foldlUtf8___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_300_, 0, v_f_298_);
v___x_301_ = ((lean_object*)(l_Lake_foldlUtf8___redArg___closed__9));
v___x_302_ = l_Lake_foldlUtf8M___redArg(v___x_301_, v_c_297_, v___f_300_, v_init_299_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___boxed(lean_object* v_00_u03c3_303_, lean_object* v_c_304_, lean_object* v_f_305_, lean_object* v_init_306_){
_start:
{
uint32_t v_c_boxed_307_; lean_object* v_res_308_; 
v_c_boxed_307_ = lean_unbox_uint32(v_c_304_);
lean_dec(v_c_304_);
v_res_308_ = l_Lake_foldlUtf8(v_00_u03c3_303_, v_c_boxed_307_, v_f_305_, v_init_306_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___at___00Lake_uriEscapeChar_spec__0(uint32_t v_c_309_, lean_object* v_init_310_){
_start:
{
uint32_t v___x_311_; uint8_t v___x_312_; 
v___x_311_ = 127;
v___x_312_ = lean_uint32_dec_le(v_c_309_, v___x_311_);
if (v___x_312_ == 0)
{
uint32_t v___x_313_; uint8_t v___x_314_; 
v___x_313_ = 2047;
v___x_314_ = lean_uint32_dec_le(v_c_309_, v___x_313_);
if (v___x_314_ == 0)
{
uint32_t v___x_315_; uint8_t v___x_316_; 
v___x_315_ = 65535;
v___x_316_ = lean_uint32_dec_le(v_c_309_, v___x_315_);
if (v___x_316_ == 0)
{
uint32_t v___x_317_; uint32_t v___x_318_; uint8_t v___x_319_; uint8_t v___x_320_; uint8_t v___x_321_; uint8_t v___x_322_; uint8_t v___x_323_; lean_object* v___x_324_; uint32_t v___x_325_; uint32_t v___x_326_; uint8_t v___x_327_; uint8_t v___x_328_; uint8_t v___x_329_; uint8_t v___x_330_; uint8_t v___x_331_; lean_object* v___x_332_; uint32_t v___x_333_; uint32_t v___x_334_; uint8_t v___x_335_; uint8_t v___x_336_; uint8_t v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; uint8_t v___x_340_; uint8_t v___x_341_; lean_object* v___x_342_; 
v___x_317_ = 18;
v___x_318_ = lean_uint32_shift_right(v_c_309_, v___x_317_);
v___x_319_ = lean_uint32_to_uint8(v___x_318_);
v___x_320_ = 7;
v___x_321_ = lean_uint8_land(v___x_319_, v___x_320_);
v___x_322_ = 240;
v___x_323_ = lean_uint8_lor(v___x_321_, v___x_322_);
v___x_324_ = l_Lake_uriEscapeByte(v___x_323_, v_init_310_);
v___x_325_ = 12;
v___x_326_ = lean_uint32_shift_right(v_c_309_, v___x_325_);
v___x_327_ = lean_uint32_to_uint8(v___x_326_);
v___x_328_ = 63;
v___x_329_ = lean_uint8_land(v___x_327_, v___x_328_);
v___x_330_ = 128;
v___x_331_ = lean_uint8_lor(v___x_329_, v___x_330_);
v___x_332_ = l_Lake_uriEscapeByte(v___x_331_, v___x_324_);
v___x_333_ = 6;
v___x_334_ = lean_uint32_shift_right(v_c_309_, v___x_333_);
v___x_335_ = lean_uint32_to_uint8(v___x_334_);
v___x_336_ = lean_uint8_land(v___x_335_, v___x_328_);
v___x_337_ = lean_uint8_lor(v___x_336_, v___x_330_);
v___x_338_ = l_Lake_uriEscapeByte(v___x_337_, v___x_332_);
v___x_339_ = lean_uint32_to_uint8(v_c_309_);
v___x_340_ = lean_uint8_land(v___x_339_, v___x_328_);
v___x_341_ = lean_uint8_lor(v___x_340_, v___x_330_);
v___x_342_ = l_Lake_uriEscapeByte(v___x_341_, v___x_338_);
return v___x_342_;
}
else
{
uint32_t v___x_343_; uint32_t v___x_344_; uint8_t v___x_345_; uint8_t v___x_346_; uint8_t v___x_347_; uint8_t v___x_348_; uint8_t v___x_349_; lean_object* v___x_350_; uint32_t v___x_351_; uint32_t v___x_352_; uint8_t v___x_353_; uint8_t v___x_354_; uint8_t v___x_355_; uint8_t v___x_356_; uint8_t v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; uint8_t v___x_360_; uint8_t v___x_361_; lean_object* v___x_362_; 
v___x_343_ = 12;
v___x_344_ = lean_uint32_shift_right(v_c_309_, v___x_343_);
v___x_345_ = lean_uint32_to_uint8(v___x_344_);
v___x_346_ = 15;
v___x_347_ = lean_uint8_land(v___x_345_, v___x_346_);
v___x_348_ = 224;
v___x_349_ = lean_uint8_lor(v___x_347_, v___x_348_);
v___x_350_ = l_Lake_uriEscapeByte(v___x_349_, v_init_310_);
v___x_351_ = 6;
v___x_352_ = lean_uint32_shift_right(v_c_309_, v___x_351_);
v___x_353_ = lean_uint32_to_uint8(v___x_352_);
v___x_354_ = 63;
v___x_355_ = lean_uint8_land(v___x_353_, v___x_354_);
v___x_356_ = 128;
v___x_357_ = lean_uint8_lor(v___x_355_, v___x_356_);
v___x_358_ = l_Lake_uriEscapeByte(v___x_357_, v___x_350_);
v___x_359_ = lean_uint32_to_uint8(v_c_309_);
v___x_360_ = lean_uint8_land(v___x_359_, v___x_354_);
v___x_361_ = lean_uint8_lor(v___x_360_, v___x_356_);
v___x_362_ = l_Lake_uriEscapeByte(v___x_361_, v___x_358_);
return v___x_362_;
}
}
else
{
uint32_t v___x_363_; uint32_t v___x_364_; uint8_t v___x_365_; uint8_t v___x_366_; uint8_t v___x_367_; uint8_t v___x_368_; uint8_t v___x_369_; lean_object* v___x_370_; uint8_t v___x_371_; uint8_t v___x_372_; uint8_t v___x_373_; uint8_t v___x_374_; uint8_t v___x_375_; lean_object* v___x_376_; 
v___x_363_ = 6;
v___x_364_ = lean_uint32_shift_right(v_c_309_, v___x_363_);
v___x_365_ = lean_uint32_to_uint8(v___x_364_);
v___x_366_ = 31;
v___x_367_ = lean_uint8_land(v___x_365_, v___x_366_);
v___x_368_ = 192;
v___x_369_ = lean_uint8_lor(v___x_367_, v___x_368_);
v___x_370_ = l_Lake_uriEscapeByte(v___x_369_, v_init_310_);
v___x_371_ = lean_uint32_to_uint8(v_c_309_);
v___x_372_ = 63;
v___x_373_ = lean_uint8_land(v___x_371_, v___x_372_);
v___x_374_ = 128;
v___x_375_ = lean_uint8_lor(v___x_373_, v___x_374_);
v___x_376_ = l_Lake_uriEscapeByte(v___x_375_, v___x_370_);
return v___x_376_;
}
}
else
{
uint8_t v___x_377_; lean_object* v___x_378_; 
v___x_377_ = lean_uint32_to_uint8(v_c_309_);
v___x_378_ = l_Lake_uriEscapeByte(v___x_377_, v_init_310_);
return v___x_378_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___at___00Lake_uriEscapeChar_spec__0___boxed(lean_object* v_c_379_, lean_object* v_init_380_){
_start:
{
uint32_t v_c_boxed_381_; lean_object* v_res_382_; 
v_c_boxed_381_ = lean_unbox_uint32(v_c_379_);
lean_dec(v_c_379_);
v_res_382_ = l_Lake_foldlUtf8M___at___00Lake_uriEscapeChar_spec__0(v_c_boxed_381_, v_init_380_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lake_uriEscapeChar(uint32_t v_c_383_, lean_object* v_s_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lake_foldlUtf8M___at___00Lake_uriEscapeChar_spec__0(v_c_383_, v_s_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lake_uriEscapeChar___boxed(lean_object* v_c_386_, lean_object* v_s_387_){
_start:
{
uint32_t v_c_boxed_388_; lean_object* v_res_389_; 
v_c_boxed_388_ = lean_unbox_uint32(v_c_386_);
lean_dec(v_c_386_);
v_res_389_ = l_Lake_uriEscapeChar(v_c_boxed_388_, v_s_387_);
return v_res_389_;
}
}
LEAN_EXPORT uint8_t l_Lake_isUriUnreservedMark(uint32_t v_c_390_){
_start:
{
uint32_t v___x_391_; uint8_t v___x_392_; 
v___x_391_ = 45;
v___x_392_ = lean_uint32_dec_eq(v_c_390_, v___x_391_);
if (v___x_392_ == 0)
{
uint32_t v___x_393_; uint8_t v___x_394_; 
v___x_393_ = 95;
v___x_394_ = lean_uint32_dec_eq(v_c_390_, v___x_393_);
if (v___x_394_ == 0)
{
uint32_t v___x_395_; uint8_t v___x_396_; 
v___x_395_ = 46;
v___x_396_ = lean_uint32_dec_eq(v_c_390_, v___x_395_);
if (v___x_396_ == 0)
{
uint32_t v___x_397_; uint8_t v___x_398_; 
v___x_397_ = 126;
v___x_398_ = lean_uint32_dec_eq(v_c_390_, v___x_397_);
return v___x_398_;
}
else
{
return v___x_396_;
}
}
else
{
return v___x_394_;
}
}
else
{
return v___x_392_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_isUriUnreservedMark___boxed(lean_object* v_c_399_){
_start:
{
uint32_t v_c_boxed_400_; uint8_t v_res_401_; lean_object* v_r_402_; 
v_c_boxed_400_ = lean_unbox_uint32(v_c_399_);
lean_dec(v_c_399_);
v_res_401_ = l_Lake_isUriUnreservedMark(v_c_boxed_400_);
v_r_402_ = lean_box(v_res_401_);
return v_r_402_;
}
}
LEAN_EXPORT lean_object* l_Lake_uriEncodeChar(uint32_t v_c_403_, lean_object* v_s_404_){
_start:
{
uint8_t v___y_406_; uint8_t v___y_412_; uint32_t v___x_423_; uint8_t v___x_424_; 
v___x_423_ = 65;
v___x_424_ = lean_uint32_dec_le(v___x_423_, v_c_403_);
if (v___x_424_ == 0)
{
goto v___jp_418_;
}
else
{
uint32_t v___x_425_; uint8_t v___x_426_; 
v___x_425_ = 90;
v___x_426_ = lean_uint32_dec_le(v_c_403_, v___x_425_);
if (v___x_426_ == 0)
{
goto v___jp_418_;
}
else
{
lean_object* v___x_427_; 
v___x_427_ = lean_string_push(v_s_404_, v_c_403_);
return v___x_427_;
}
}
v___jp_405_:
{
if (v___y_406_ == 0)
{
uint8_t v___x_407_; 
v___x_407_ = l_Lake_isUriUnreservedMark(v_c_403_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; 
v___x_408_ = l_Lake_foldlUtf8M___at___00Lake_uriEscapeChar_spec__0(v_c_403_, v_s_404_);
return v___x_408_;
}
else
{
lean_object* v___x_409_; 
v___x_409_ = lean_string_push(v_s_404_, v_c_403_);
return v___x_409_;
}
}
else
{
lean_object* v___x_410_; 
v___x_410_ = lean_string_push(v_s_404_, v_c_403_);
return v___x_410_;
}
}
v___jp_411_:
{
if (v___y_412_ == 0)
{
uint32_t v___x_413_; uint8_t v___x_414_; 
v___x_413_ = 48;
v___x_414_ = lean_uint32_dec_le(v___x_413_, v_c_403_);
if (v___x_414_ == 0)
{
v___y_406_ = v___x_414_;
goto v___jp_405_;
}
else
{
uint32_t v___x_415_; uint8_t v___x_416_; 
v___x_415_ = 57;
v___x_416_ = lean_uint32_dec_le(v_c_403_, v___x_415_);
v___y_406_ = v___x_416_;
goto v___jp_405_;
}
}
else
{
lean_object* v___x_417_; 
v___x_417_ = lean_string_push(v_s_404_, v_c_403_);
return v___x_417_;
}
}
v___jp_418_:
{
uint32_t v___x_419_; uint8_t v___x_420_; 
v___x_419_ = 97;
v___x_420_ = lean_uint32_dec_le(v___x_419_, v_c_403_);
if (v___x_420_ == 0)
{
v___y_412_ = v___x_420_;
goto v___jp_411_;
}
else
{
uint32_t v___x_421_; uint8_t v___x_422_; 
v___x_421_ = 122;
v___x_422_ = lean_uint32_dec_le(v_c_403_, v___x_421_);
v___y_412_ = v___x_422_;
goto v___jp_411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_uriEncodeChar___boxed(lean_object* v_c_428_, lean_object* v_s_429_){
_start:
{
uint32_t v_c_boxed_430_; lean_object* v_res_431_; 
v_c_boxed_430_ = lean_unbox_uint32(v_c_428_);
lean_dec(v_c_428_);
v_res_431_ = l_Lake_uriEncodeChar(v_c_boxed_430_, v_s_429_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___redArg(lean_object* v___x_432_, lean_object* v_s_433_, lean_object* v_a_434_, lean_object* v_b_435_){
_start:
{
lean_object* v_startInclusive_436_; lean_object* v_endExclusive_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
v_startInclusive_436_ = lean_ctor_get(v___x_432_, 1);
v_endExclusive_437_ = lean_ctor_get(v___x_432_, 2);
v___x_438_ = lean_nat_sub(v_endExclusive_437_, v_startInclusive_436_);
v___x_439_ = lean_nat_dec_eq(v_a_434_, v___x_438_);
lean_dec(v___x_438_);
if (v___x_439_ == 0)
{
uint32_t v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_440_ = lean_string_utf8_get_fast(v_s_433_, v_a_434_);
v___x_441_ = lean_string_utf8_next_fast(v_s_433_, v_a_434_);
lean_dec(v_a_434_);
v___x_442_ = l_Lake_uriEncodeChar(v___x_440_, v_b_435_);
v_a_434_ = v___x_441_;
v_b_435_ = v___x_442_;
goto _start;
}
else
{
lean_dec(v_a_434_);
return v_b_435_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___redArg___boxed(lean_object* v___x_444_, lean_object* v_s_445_, lean_object* v_a_446_, lean_object* v_b_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___redArg(v___x_444_, v_s_445_, v_a_446_, v_b_447_);
lean_dec_ref(v_s_445_);
lean_dec_ref(v___x_444_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lake_uriEncode(lean_object* v_s_449_, lean_object* v_init_450_){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_451_ = lean_unsigned_to_nat(0u);
v___x_452_ = lean_string_utf8_byte_size(v_s_449_);
lean_inc_ref(v_s_449_);
v___x_453_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_453_, 0, v_s_449_);
lean_ctor_set(v___x_453_, 1, v___x_451_);
lean_ctor_set(v___x_453_, 2, v___x_452_);
v___x_454_ = l_String_Slice_positions(v___x_453_);
v___x_455_ = l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___redArg(v___x_453_, v_s_449_, v___x_454_, v_init_450_);
lean_dec_ref(v_s_449_);
lean_dec_ref(v___x_453_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0(lean_object* v___x_456_, lean_object* v_s_457_, lean_object* v_inst_458_, lean_object* v_R_459_, lean_object* v_a_460_, lean_object* v_b_461_, lean_object* v_c_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___redArg(v___x_456_, v_s_457_, v_a_460_, v_b_461_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___boxed(lean_object* v___x_464_, lean_object* v_s_465_, lean_object* v_inst_466_, lean_object* v_R_467_, lean_object* v_a_468_, lean_object* v_b_469_, lean_object* v_c_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0(v___x_464_, v_s_465_, v_inst_466_, v_R_467_, v_a_468_, v_b_469_, v_c_470_);
lean_dec_ref(v_s_465_);
lean_dec_ref(v___x_464_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0(lean_object* v_x_474_){
_start:
{
if (lean_obj_tag(v_x_474_) == 0)
{
lean_object* v___x_475_; 
v___x_475_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0___closed__0));
return v___x_475_;
}
else
{
lean_object* v___x_476_; 
v___x_476_ = l_Lean_Json_getNat_x3f(v_x_474_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_484_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_484_ == 0)
{
v___x_479_ = v___x_476_;
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_480_ == 0)
{
v___x_482_ = v___x_479_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_a_477_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
else
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_493_; 
v_a_485_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_493_ == 0)
{
v___x_487_ = v___x_476_;
v_isShared_488_ = v_isSharedCheck_493_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_476_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_493_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_489_, 0, v_a_485_);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 0, v___x_489_);
v___x_491_ = v___x_487_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__1(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_495_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__0));
v___x_496_ = lean_unsigned_to_nat(2u);
v___x_497_ = lean_mk_empty_array_with_capacity(v___x_496_);
v___x_498_ = lean_array_push(v___x_497_, v___x_495_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1(lean_object* v_as_499_, size_t v_i_500_, size_t v_stop_501_, lean_object* v_b_502_){
_start:
{
uint8_t v___x_503_; 
v___x_503_ = lean_usize_dec_eq(v_i_500_, v_stop_501_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; size_t v___x_508_; size_t v___x_509_; 
v___x_504_ = lean_array_uget_borrowed(v_as_499_, v_i_500_);
v___x_505_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__1);
lean_inc(v___x_504_);
v___x_506_ = lean_array_push(v___x_505_, v___x_504_);
v___x_507_ = l_Array_append___redArg(v_b_502_, v___x_506_);
lean_dec_ref(v___x_506_);
v___x_508_ = ((size_t)1ULL);
v___x_509_ = lean_usize_add(v_i_500_, v___x_508_);
v_i_500_ = v___x_509_;
v_b_502_ = v___x_507_;
goto _start;
}
else
{
return v_b_502_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___boxed(lean_object* v_as_511_, lean_object* v_i_512_, lean_object* v_stop_513_, lean_object* v_b_514_){
_start:
{
size_t v_i_boxed_515_; size_t v_stop_boxed_516_; lean_object* v_res_517_; 
v_i_boxed_515_ = lean_unbox_usize(v_i_512_);
lean_dec(v_i_512_);
v_stop_boxed_516_ = lean_unbox_usize(v_stop_513_);
lean_dec(v_stop_513_);
v_res_517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1(v_as_511_, v_i_boxed_515_, v_stop_boxed_516_, v_b_514_);
lean_dec_ref(v_as_511_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lake_getUrl_x3f(lean_object* v_url_554_, lean_object* v_headers_555_, lean_object* v_a_556_){
_start:
{
lean_object* v___y_559_; lean_object* v_a_560_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v_a_565_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v_a_579_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v_a_590_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_640_; lean_object* v_args_667_; lean_object* v___x_668_; lean_object* v___x_669_; uint8_t v___x_670_; 
v_args_667_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__18));
v___x_668_ = lean_unsigned_to_nat(0u);
v___x_669_ = lean_array_get_size(v_headers_555_);
v___x_670_ = lean_nat_dec_lt(v___x_668_, v___x_669_);
if (v___x_670_ == 0)
{
v___y_640_ = v_args_667_;
goto v___jp_639_;
}
else
{
uint8_t v___x_671_; 
v___x_671_ = lean_nat_dec_le(v___x_669_, v___x_669_);
if (v___x_671_ == 0)
{
if (v___x_670_ == 0)
{
v___y_640_ = v_args_667_;
goto v___jp_639_;
}
else
{
size_t v___x_672_; size_t v___x_673_; lean_object* v___x_674_; 
v___x_672_ = ((size_t)0ULL);
v___x_673_ = lean_usize_of_nat(v___x_669_);
v___x_674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1(v_headers_555_, v___x_672_, v___x_673_, v_args_667_);
v___y_640_ = v___x_674_;
goto v___jp_639_;
}
}
else
{
size_t v___x_675_; size_t v___x_676_; lean_object* v___x_677_; 
v___x_675_ = ((size_t)0ULL);
v___x_676_ = lean_usize_of_nat(v___x_669_);
v___x_677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1(v_headers_555_, v___x_675_, v___x_676_, v_args_667_);
v___y_640_ = v___x_677_;
goto v___jp_639_;
}
}
v___jp_558_:
{
lean_object* v___x_561_; 
v___x_561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_561_, 0, v___y_559_);
lean_ctor_set(v___x_561_, 1, v_a_560_);
return v___x_561_;
}
v___jp_562_:
{
lean_object* v___x_566_; lean_object* v___x_567_; uint8_t v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_566_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__0));
v___x_567_ = lean_string_append(v___x_566_, v_a_565_);
lean_dec_ref(v_a_565_);
v___x_568_ = 3;
v___x_569_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_569_, 0, v___x_567_);
lean_ctor_set_uint8(v___x_569_, sizeof(void*)*1, v___x_568_);
v___x_570_ = lean_array_push(v___y_563_, v___x_569_);
v___y_559_ = v___y_564_;
v_a_560_ = v___x_570_;
goto v___jp_558_;
}
v___jp_571_:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__2));
v___x_575_ = lean_array_push(v___y_572_, v___x_574_);
v___y_559_ = v___y_573_;
v_a_560_ = v___x_575_;
goto v___jp_558_;
}
v___jp_576_:
{
lean_object* v___x_580_; lean_object* v___x_581_; uint8_t v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_580_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__3));
v___x_581_ = lean_string_append(v___x_580_, v_a_579_);
lean_dec_ref(v_a_579_);
v___x_582_ = 3;
v___x_583_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_583_, 0, v___x_581_);
lean_ctor_set_uint8(v___x_583_, sizeof(void*)*1, v___x_582_);
v___x_584_ = lean_array_push(v___y_577_, v___x_583_);
v___y_559_ = v___y_578_;
v_a_560_ = v___x_584_;
goto v___jp_558_;
}
v___jp_585_:
{
if (lean_obj_tag(v_a_590_) == 0)
{
lean_dec_ref(v___y_588_);
lean_dec(v___y_586_);
v___y_572_ = v___y_587_;
v___y_573_ = v___y_589_;
goto v___jp_571_;
}
else
{
lean_object* v_val_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_623_; 
v_val_591_ = lean_ctor_get(v_a_590_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v_a_590_);
if (v_isSharedCheck_623_ == 0)
{
v___x_593_ = v_a_590_;
v_isShared_594_ = v_isSharedCheck_623_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_val_591_);
lean_dec(v_a_590_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_623_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_595_ = lean_unsigned_to_nat(200u);
v___x_596_ = lean_nat_dec_eq(v_val_591_, v___x_595_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; uint8_t v___x_598_; 
lean_del_object(v___x_593_);
lean_dec(v___y_586_);
v___x_597_ = lean_unsigned_to_nat(404u);
v___x_598_ = lean_nat_dec_eq(v_val_591_, v___x_597_);
if (v___x_598_ == 0)
{
lean_object* v_stdout_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v_stdout_599_ = lean_ctor_get(v___y_588_, 0);
lean_inc_ref(v_stdout_599_);
lean_dec_ref(v___y_588_);
v___x_600_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__4));
v___x_601_ = l_Nat_reprFast(v_val_591_);
v___x_602_ = lean_string_append(v___x_600_, v___x_601_);
lean_dec_ref(v___x_601_);
v___x_603_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__5));
v___x_604_ = lean_string_append(v___x_602_, v___x_603_);
v___x_605_ = lean_string_append(v___x_604_, v_stdout_599_);
lean_dec_ref(v_stdout_599_);
v___x_606_ = 3;
v___x_607_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_607_, 0, v___x_605_);
lean_ctor_set_uint8(v___x_607_, sizeof(void*)*1, v___x_606_);
v___x_608_ = lean_array_push(v___y_587_, v___x_607_);
v___y_559_ = v___y_589_;
v_a_560_ = v___x_608_;
goto v___jp_558_;
}
else
{
lean_object* v___x_609_; lean_object* v___x_610_; 
lean_dec(v_val_591_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
v___x_609_ = lean_box(0);
v___x_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
lean_ctor_set(v___x_610_, 1, v___y_587_);
return v___x_610_;
}
}
else
{
lean_object* v_stdout_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v_str_615_; lean_object* v_startInclusive_616_; lean_object* v_endExclusive_617_; lean_object* v___x_618_; lean_object* v___x_620_; 
lean_dec(v_val_591_);
lean_dec(v___y_589_);
v_stdout_611_ = lean_ctor_get(v___y_588_, 0);
lean_inc_ref(v_stdout_611_);
lean_dec_ref(v___y_588_);
v___x_612_ = lean_string_utf8_byte_size(v_stdout_611_);
v___x_613_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_613_, 0, v_stdout_611_);
lean_ctor_set(v___x_613_, 1, v___y_586_);
lean_ctor_set(v___x_613_, 2, v___x_612_);
v___x_614_ = l_String_Slice_trimAscii(v___x_613_);
v_str_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc_ref(v_str_615_);
v_startInclusive_616_ = lean_ctor_get(v___x_614_, 1);
lean_inc(v_startInclusive_616_);
v_endExclusive_617_ = lean_ctor_get(v___x_614_, 2);
lean_inc(v_endExclusive_617_);
lean_dec_ref(v___x_614_);
v___x_618_ = lean_string_utf8_extract(v_str_615_, v_startInclusive_616_, v_endExclusive_617_);
lean_dec(v_endExclusive_617_);
lean_dec(v_startInclusive_616_);
lean_dec_ref(v_str_615_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_618_);
v___x_620_ = v___x_593_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_618_);
v___x_620_ = v_reuseFailAlloc_622_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_621_; 
v___x_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
lean_ctor_set(v___x_621_, 1, v___y_587_);
return v___x_621_;
}
}
}
}
}
v___jp_624_:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__6));
v___x_631_ = l_Lake_JsonObject_getJson_x3f(v___y_627_, v___x_630_);
lean_dec(v___y_627_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_dec_ref(v___y_628_);
lean_dec(v___y_625_);
v___y_572_ = v___y_626_;
v___y_573_ = v___y_629_;
goto v___jp_571_;
}
else
{
lean_object* v_val_632_; lean_object* v___x_633_; 
v_val_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_val_632_);
lean_dec_ref(v___x_631_);
v___x_633_ = l_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0(v_val_632_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
lean_dec_ref(v___y_628_);
lean_dec(v___y_625_);
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_634_);
lean_dec_ref(v___x_633_);
v___x_635_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__7));
v___x_636_ = lean_string_append(v___x_635_, v_a_634_);
lean_dec(v_a_634_);
v___y_563_ = v___y_626_;
v___y_564_ = v___y_629_;
v_a_565_ = v___x_636_;
goto v___jp_562_;
}
else
{
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_637_; 
lean_dec_ref(v___y_628_);
lean_dec(v___y_625_);
v_a_637_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_637_);
lean_dec_ref(v___x_633_);
v___y_563_ = v___y_626_;
v___y_564_ = v___y_629_;
v_a_565_ = v_a_637_;
goto v___jp_562_;
}
else
{
lean_object* v_a_638_; 
v_a_638_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_638_);
lean_dec_ref(v___x_633_);
v___y_586_ = v___y_625_;
v___y_587_ = v___y_626_;
v___y_588_ = v___y_628_;
v___y_589_ = v___y_629_;
v_a_590_ = v_a_638_;
goto v___jp_585_;
}
}
}
}
v___jp_639_:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; uint8_t v___x_647_; uint8_t v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_641_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__8));
v___x_642_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__9));
v___x_643_ = lean_array_push(v___y_640_, v_url_554_);
v___x_644_ = lean_box(0);
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_646_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__10));
v___x_647_ = 1;
v___x_648_ = 0;
v___x_649_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_649_, 0, v___x_641_);
lean_ctor_set(v___x_649_, 1, v___x_642_);
lean_ctor_set(v___x_649_, 2, v___x_643_);
lean_ctor_set(v___x_649_, 3, v___x_644_);
lean_ctor_set(v___x_649_, 4, v___x_646_);
lean_ctor_set_uint8(v___x_649_, sizeof(void*)*5, v___x_647_);
lean_ctor_set_uint8(v___x_649_, sizeof(void*)*5 + 1, v___x_648_);
lean_inc_ref(v_a_556_);
v___x_650_ = l_Lake_captureProc_x27(v___x_649_, v_a_556_);
v___x_651_ = lean_array_get_size(v_a_556_);
lean_dec_ref(v_a_556_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_652_; lean_object* v_a_653_; lean_object* v_stderr_654_; lean_object* v___x_655_; 
v_a_652_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_652_);
v_a_653_ = lean_ctor_get(v___x_650_, 1);
lean_inc(v_a_653_);
lean_dec_ref(v___x_650_);
v_stderr_654_ = lean_ctor_get(v_a_652_, 1);
lean_inc_ref(v_stderr_654_);
v___x_655_ = l_Lean_Json_parse(v_stderr_654_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; 
lean_dec(v_a_652_);
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_656_);
lean_dec_ref(v___x_655_);
v___y_577_ = v_a_653_;
v___y_578_ = v___x_651_;
v_a_579_ = v_a_656_;
goto v___jp_576_;
}
else
{
lean_object* v_a_657_; lean_object* v___x_658_; 
v_a_657_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_657_);
lean_dec_ref(v___x_655_);
v___x_658_ = l_Lean_Json_getObj_x3f(v_a_657_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; 
lean_dec(v_a_652_);
v_a_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_659_);
lean_dec_ref(v___x_658_);
v___y_577_ = v_a_653_;
v___y_578_ = v___x_651_;
v_a_579_ = v_a_659_;
goto v___jp_576_;
}
else
{
lean_object* v_a_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v_a_660_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_660_);
lean_dec_ref(v___x_658_);
v___x_661_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__11));
v___x_662_ = l_Lake_JsonObject_getJson_x3f(v_a_660_, v___x_661_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_dec(v_a_660_);
lean_dec(v_a_652_);
v___y_572_ = v_a_653_;
v___y_573_ = v___x_651_;
goto v___jp_571_;
}
else
{
lean_object* v_val_663_; lean_object* v___x_664_; 
v_val_663_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_val_663_);
lean_dec_ref(v___x_662_);
v___x_664_ = l_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0(v_val_663_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_dec_ref(v___x_664_);
v___y_625_ = v___x_645_;
v___y_626_ = v_a_653_;
v___y_627_ = v_a_660_;
v___y_628_ = v_a_652_;
v___y_629_ = v___x_651_;
goto v___jp_624_;
}
else
{
if (lean_obj_tag(v___x_664_) == 0)
{
lean_dec_ref(v___x_664_);
v___y_625_ = v___x_645_;
v___y_626_ = v_a_653_;
v___y_627_ = v_a_660_;
v___y_628_ = v_a_652_;
v___y_629_ = v___x_651_;
goto v___jp_624_;
}
else
{
lean_object* v_a_665_; 
lean_dec(v_a_660_);
v_a_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_a_665_);
lean_dec_ref(v___x_664_);
v___y_586_ = v___x_645_;
v___y_587_ = v_a_653_;
v___y_588_ = v_a_652_;
v___y_589_ = v___x_651_;
v_a_590_ = v_a_665_;
goto v___jp_585_;
}
}
}
}
}
}
else
{
lean_object* v_a_666_; 
v_a_666_ = lean_ctor_get(v___x_650_, 1);
lean_inc(v_a_666_);
lean_dec_ref(v___x_650_);
v___y_559_ = v___x_651_;
v_a_560_ = v_a_666_;
goto v___jp_558_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getUrl_x3f___boxed(lean_object* v_url_678_, lean_object* v_headers_679_, lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lake_getUrl_x3f(v_url_678_, v_headers_679_, v_a_680_);
lean_dec_ref(v_headers_679_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lake_getUrl(lean_object* v_url_693_, lean_object* v_headers_694_, lean_object* v_a_695_){
_start:
{
lean_object* v___y_698_; lean_object* v_args_735_; lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; 
v_args_735_ = ((lean_object*)(l_Lake_getUrl___closed__0));
v___x_736_ = lean_unsigned_to_nat(0u);
v___x_737_ = lean_array_get_size(v_headers_694_);
v___x_738_ = lean_nat_dec_lt(v___x_736_, v___x_737_);
if (v___x_738_ == 0)
{
v___y_698_ = v_args_735_;
goto v___jp_697_;
}
else
{
uint8_t v___x_739_; 
v___x_739_ = lean_nat_dec_le(v___x_737_, v___x_737_);
if (v___x_739_ == 0)
{
if (v___x_738_ == 0)
{
v___y_698_ = v_args_735_;
goto v___jp_697_;
}
else
{
size_t v___x_740_; size_t v___x_741_; lean_object* v___x_742_; 
v___x_740_ = ((size_t)0ULL);
v___x_741_ = lean_usize_of_nat(v___x_737_);
v___x_742_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1(v_headers_694_, v___x_740_, v___x_741_, v_args_735_);
v___y_698_ = v___x_742_;
goto v___jp_697_;
}
}
else
{
size_t v___x_743_; size_t v___x_744_; lean_object* v___x_745_; 
v___x_743_ = ((size_t)0ULL);
v___x_744_ = lean_usize_of_nat(v___x_737_);
v___x_745_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1(v_headers_694_, v___x_743_, v___x_744_, v_args_735_);
v___y_698_ = v___x_745_;
goto v___jp_697_;
}
}
v___jp_697_:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; uint8_t v___x_705_; uint8_t v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_699_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__8));
v___x_700_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__9));
v___x_701_ = lean_array_push(v___y_698_, v_url_693_);
v___x_702_ = lean_box(0);
v___x_703_ = lean_unsigned_to_nat(0u);
v___x_704_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__10));
v___x_705_ = 1;
v___x_706_ = 0;
v___x_707_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_707_, 0, v___x_699_);
lean_ctor_set(v___x_707_, 1, v___x_700_);
lean_ctor_set(v___x_707_, 2, v___x_701_);
lean_ctor_set(v___x_707_, 3, v___x_702_);
lean_ctor_set(v___x_707_, 4, v___x_704_);
lean_ctor_set_uint8(v___x_707_, sizeof(void*)*5, v___x_705_);
lean_ctor_set_uint8(v___x_707_, sizeof(void*)*5 + 1, v___x_706_);
v___x_708_ = l_Lake_captureProc_x27(v___x_707_, v_a_695_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_725_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
v_a_710_ = lean_ctor_get(v___x_708_, 1);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_725_ == 0)
{
v___x_712_ = v___x_708_;
v_isShared_713_ = v_isSharedCheck_725_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_inc(v_a_709_);
lean_dec(v___x_708_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_725_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v_stdout_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v_str_718_; lean_object* v_startInclusive_719_; lean_object* v_endExclusive_720_; lean_object* v___x_721_; lean_object* v___x_723_; 
v_stdout_714_ = lean_ctor_get(v_a_709_, 0);
lean_inc_ref(v_stdout_714_);
lean_dec(v_a_709_);
v___x_715_ = lean_string_utf8_byte_size(v_stdout_714_);
v___x_716_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_716_, 0, v_stdout_714_);
lean_ctor_set(v___x_716_, 1, v___x_703_);
lean_ctor_set(v___x_716_, 2, v___x_715_);
v___x_717_ = l_String_Slice_trimAscii(v___x_716_);
v_str_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc_ref(v_str_718_);
v_startInclusive_719_ = lean_ctor_get(v___x_717_, 1);
lean_inc(v_startInclusive_719_);
v_endExclusive_720_ = lean_ctor_get(v___x_717_, 2);
lean_inc(v_endExclusive_720_);
lean_dec_ref(v___x_717_);
v___x_721_ = lean_string_utf8_extract(v_str_718_, v_startInclusive_719_, v_endExclusive_720_);
lean_dec(v_endExclusive_720_);
lean_dec(v_startInclusive_719_);
lean_dec_ref(v_str_718_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v___x_721_);
v___x_723_ = v___x_712_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_a_710_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
else
{
lean_object* v_a_726_; lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
v_a_726_ = lean_ctor_get(v___x_708_, 0);
v_a_727_ = lean_ctor_get(v___x_708_, 1);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_708_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_inc(v_a_726_);
lean_dec(v___x_708_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_726_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getUrl___boxed(lean_object* v_url_746_, lean_object* v_headers_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lake_getUrl(v_url_746_, v_headers_747_, v_a_748_);
lean_dec_ref(v_headers_747_);
return v_res_750_;
}
}
lean_object* runtime_initialize_Lake_Util_Log(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_JsonObject(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Proc(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Url(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Util_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_JsonObject(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Proc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_Url(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Util_Log(uint8_t builtin);
lean_object* initialize_Lake_Util_JsonObject(uint8_t builtin);
lean_object* initialize_Lake_Util_Proc(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Url(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_JsonObject(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Proc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Url(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_Url(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_Url(builtin);
}
#ifdef __cplusplus
}
#endif

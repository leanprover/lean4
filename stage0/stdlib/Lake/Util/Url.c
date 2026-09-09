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
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JsonObject_getJson_x3f(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_captureProc_x27(lean_object*, lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
lean_object* lean_io_getenv(lean_object*);
lean_object* lean_array_get_size(lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Internal_getCurl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "CURL"};
static const lean_object* l_Lake_Internal_getCurl___closed__0 = (const lean_object*)&l_Lake_Internal_getCurl___closed__0_value;
static const lean_string_object l_Lake_Internal_getCurl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "curl"};
static const lean_object* l_Lake_Internal_getCurl___closed__1 = (const lean_object*)&l_Lake_Internal_getCurl___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Internal_getCurl();
LEAN_EXPORT lean_object* l_Lake_Internal_getCurl___boxed(lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0(lean_object*);
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
static const lean_array_object l_Lake_getUrl_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_getUrl_x3f___closed__9 = (const lean_object*)&l_Lake_getUrl_x3f___closed__9_value;
static const lean_string_object l_Lake_getUrl_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "response_code"};
static const lean_object* l_Lake_getUrl_x3f___closed__10 = (const lean_object*)&l_Lake_getUrl_x3f___closed__10_value;
static const lean_string_object l_Lake_getUrl_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-s"};
static const lean_object* l_Lake_getUrl_x3f___closed__11 = (const lean_object*)&l_Lake_getUrl_x3f___closed__11_value;
static const lean_string_object l_Lake_getUrl_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-L"};
static const lean_object* l_Lake_getUrl_x3f___closed__12 = (const lean_object*)&l_Lake_getUrl_x3f___closed__12_value;
static const lean_string_object l_Lake_getUrl_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-w"};
static const lean_object* l_Lake_getUrl_x3f___closed__13 = (const lean_object*)&l_Lake_getUrl_x3f___closed__13_value;
static const lean_string_object l_Lake_getUrl_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "%{stderr}%{json}\n"};
static const lean_object* l_Lake_getUrl_x3f___closed__14 = (const lean_object*)&l_Lake_getUrl_x3f___closed__14_value;
static const lean_string_object l_Lake_getUrl_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "--retry"};
static const lean_object* l_Lake_getUrl_x3f___closed__15 = (const lean_object*)&l_Lake_getUrl_x3f___closed__15_value;
static const lean_string_object l_Lake_getUrl_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "3"};
static const lean_object* l_Lake_getUrl_x3f___closed__16 = (const lean_object*)&l_Lake_getUrl_x3f___closed__16_value;
static const lean_array_object l_Lake_getUrl_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l_Lake_getUrl_x3f___closed__11_value),((lean_object*)&l_Lake_getUrl_x3f___closed__12_value),((lean_object*)&l_Lake_getUrl_x3f___closed__13_value),((lean_object*)&l_Lake_getUrl_x3f___closed__14_value),((lean_object*)&l_Lake_getUrl_x3f___closed__15_value),((lean_object*)&l_Lake_getUrl_x3f___closed__16_value)}};
static const lean_object* l_Lake_getUrl_x3f___closed__17 = (const lean_object*)&l_Lake_getUrl_x3f___closed__17_value;
LEAN_EXPORT lean_object* l_Lake_getUrl_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getUrl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_getUrl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_Lake_getUrl_x3f___closed__11_value),((lean_object*)&l_Lake_getUrl_x3f___closed__12_value),((lean_object*)&l_Lake_getUrl_x3f___closed__15_value),((lean_object*)&l_Lake_getUrl_x3f___closed__16_value)}};
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
uint32_t v_c_boxed_86_; uint8_t v___x_390__boxed_87_; uint8_t v___x_391__boxed_88_; lean_object* v_res_89_; 
v_c_boxed_86_ = lean_unbox_uint32(v_c_81_);
lean_dec(v_c_81_);
v___x_390__boxed_87_ = lean_unbox(v___x_82_);
v___x_391__boxed_88_ = lean_unbox(v___x_83_);
v_res_89_ = l_Lake_foldlUtf8M___redArg___lam__0(v_c_boxed_86_, v___x_390__boxed_87_, v___x_391__boxed_88_, v_f_84_, v_s_85_);
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
uint32_t v_c_boxed_112_; uint8_t v___x_406__boxed_113_; uint8_t v___x_407__boxed_114_; lean_object* v_res_115_; 
v_c_boxed_112_ = lean_unbox_uint32(v_c_105_);
lean_dec(v_c_105_);
v___x_406__boxed_113_ = lean_unbox(v___x_106_);
v___x_407__boxed_114_ = lean_unbox(v___x_107_);
v_res_115_ = l_Lake_foldlUtf8M___redArg___lam__1(v_c_boxed_112_, v___x_406__boxed_113_, v___x_407__boxed_114_, v_f_108_, v_toBind_109_, v___f_110_, v_s_111_);
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
lean_object* v_toBind_187_; uint32_t v___x_188_; uint8_t v___x_189_; 
v_toBind_187_ = lean_ctor_get(v_inst_183_, 1);
lean_inc(v_toBind_187_);
lean_dec_ref(v_inst_183_);
v___x_188_ = 127;
v___x_189_ = lean_uint32_dec_le(v_c_184_, v___x_188_);
if (v___x_189_ == 0)
{
uint32_t v___x_190_; uint8_t v___x_191_; 
v___x_190_ = 2047;
v___x_191_ = lean_uint32_dec_le(v_c_184_, v___x_190_);
if (v___x_191_ == 0)
{
uint32_t v___x_192_; uint8_t v___x_193_; 
v___x_192_ = 65535;
v___x_193_ = lean_uint32_dec_le(v_c_184_, v___x_192_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; lean_object* v___f_195_; uint32_t v___x_196_; uint32_t v___x_197_; uint8_t v___x_198_; uint8_t v___x_199_; uint8_t v___x_200_; uint8_t v___x_201_; uint8_t v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_194_ = lean_box_uint32(v_c_184_);
lean_inc(v_toBind_187_);
lean_inc(v_f_185_);
v___f_195_ = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_195_, 0, v___x_194_);
lean_closure_set(v___f_195_, 1, v_f_185_);
lean_closure_set(v___f_195_, 2, v_toBind_187_);
v___x_196_ = 18;
v___x_197_ = lean_uint32_shift_right(v_c_184_, v___x_196_);
v___x_198_ = lean_uint32_to_uint8(v___x_197_);
v___x_199_ = 7;
v___x_200_ = lean_uint8_land(v___x_198_, v___x_199_);
v___x_201_ = 240;
v___x_202_ = lean_uint8_lor(v___x_200_, v___x_201_);
v___x_203_ = lean_box(v___x_202_);
v___x_204_ = lean_apply_2(v_f_185_, v_init_186_, v___x_203_);
v___x_205_ = lean_apply_4(v_toBind_187_, lean_box(0), lean_box(0), v___x_204_, v___f_195_);
return v___x_205_;
}
else
{
lean_object* v___x_206_; lean_object* v___f_207_; uint32_t v___x_208_; uint32_t v___x_209_; uint8_t v___x_210_; uint8_t v___x_211_; uint8_t v___x_212_; uint8_t v___x_213_; uint8_t v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_206_ = lean_box_uint32(v_c_184_);
lean_inc(v_toBind_187_);
lean_inc(v_f_185_);
v___f_207_ = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_207_, 0, v___x_206_);
lean_closure_set(v___f_207_, 1, v_f_185_);
lean_closure_set(v___f_207_, 2, v_toBind_187_);
v___x_208_ = 12;
v___x_209_ = lean_uint32_shift_right(v_c_184_, v___x_208_);
v___x_210_ = lean_uint32_to_uint8(v___x_209_);
v___x_211_ = 15;
v___x_212_ = lean_uint8_land(v___x_210_, v___x_211_);
v___x_213_ = 224;
v___x_214_ = lean_uint8_lor(v___x_212_, v___x_213_);
v___x_215_ = lean_box(v___x_214_);
v___x_216_ = lean_apply_2(v_f_185_, v_init_186_, v___x_215_);
v___x_217_ = lean_apply_4(v_toBind_187_, lean_box(0), lean_box(0), v___x_216_, v___f_207_);
return v___x_217_;
}
}
else
{
lean_object* v___x_218_; lean_object* v___f_219_; uint32_t v___x_220_; uint32_t v___x_221_; uint8_t v___x_222_; uint8_t v___x_223_; uint8_t v___x_224_; uint8_t v___x_225_; uint8_t v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_218_ = lean_box_uint32(v_c_184_);
lean_inc(v_f_185_);
v___f_219_ = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_219_, 0, v___x_218_);
lean_closure_set(v___f_219_, 1, v_f_185_);
v___x_220_ = 6;
v___x_221_ = lean_uint32_shift_right(v_c_184_, v___x_220_);
v___x_222_ = lean_uint32_to_uint8(v___x_221_);
v___x_223_ = 31;
v___x_224_ = lean_uint8_land(v___x_222_, v___x_223_);
v___x_225_ = 192;
v___x_226_ = lean_uint8_lor(v___x_224_, v___x_225_);
v___x_227_ = lean_box(v___x_226_);
v___x_228_ = lean_apply_2(v_f_185_, v_init_186_, v___x_227_);
v___x_229_ = lean_apply_4(v_toBind_187_, lean_box(0), lean_box(0), v___x_228_, v___f_219_);
return v___x_229_;
}
}
else
{
uint8_t v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
lean_dec(v_toBind_187_);
v___x_230_ = lean_uint32_to_uint8(v_c_184_);
v___x_231_ = lean_box(v___x_230_);
v___x_232_ = lean_apply_2(v_f_185_, v_init_186_, v___x_231_);
return v___x_232_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___boxed(lean_object* v_inst_233_, lean_object* v_c_234_, lean_object* v_f_235_, lean_object* v_init_236_){
_start:
{
uint32_t v_c_boxed_237_; lean_object* v_res_238_; 
v_c_boxed_237_ = lean_unbox_uint32(v_c_234_);
lean_dec(v_c_234_);
v_res_238_ = l_Lake_foldlUtf8M___redArg(v_inst_233_, v_c_boxed_237_, v_f_235_, v_init_236_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M(lean_object* v_m_239_, lean_object* v_00_u03c3_240_, lean_object* v_inst_241_, uint32_t v_c_242_, lean_object* v_f_243_, lean_object* v_init_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Lake_foldlUtf8M___redArg(v_inst_241_, v_c_242_, v_f_243_, v_init_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___boxed(lean_object* v_m_246_, lean_object* v_00_u03c3_247_, lean_object* v_inst_248_, lean_object* v_c_249_, lean_object* v_f_250_, lean_object* v_init_251_){
_start:
{
uint32_t v_c_boxed_252_; lean_object* v_res_253_; 
v_c_boxed_252_ = lean_unbox_uint32(v_c_249_);
lean_dec(v_c_249_);
v_res_253_ = l_Lake_foldlUtf8M(v_m_246_, v_00_u03c3_247_, v_inst_248_, v_c_boxed_252_, v_f_250_, v_init_251_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___redArg___lam__0(lean_object* v_f_254_, lean_object* v_x1_255_, uint8_t v_x2_256_){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_box(v_x2_256_);
v___x_258_ = lean_apply_2(v_f_254_, v_x1_255_, v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___redArg___lam__0___boxed(lean_object* v_f_259_, lean_object* v_x1_260_, lean_object* v_x2_261_){
_start:
{
uint8_t v_x2_83__boxed_262_; lean_object* v_res_263_; 
v_x2_83__boxed_262_ = lean_unbox(v_x2_261_);
v_res_263_ = l_Lake_foldlUtf8___redArg___lam__0(v_f_259_, v_x1_260_, v_x2_83__boxed_262_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___redArg(uint32_t v_c_283_, lean_object* v_f_284_, lean_object* v_init_285_){
_start:
{
lean_object* v___f_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___f_286_ = lean_alloc_closure((void*)(l_Lake_foldlUtf8___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_286_, 0, v_f_284_);
v___x_287_ = ((lean_object*)(l_Lake_foldlUtf8___redArg___closed__9));
v___x_288_ = l_Lake_foldlUtf8M___redArg(v___x_287_, v_c_283_, v___f_286_, v_init_285_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___redArg___boxed(lean_object* v_c_289_, lean_object* v_f_290_, lean_object* v_init_291_){
_start:
{
uint32_t v_c_boxed_292_; lean_object* v_res_293_; 
v_c_boxed_292_ = lean_unbox_uint32(v_c_289_);
lean_dec(v_c_289_);
v_res_293_ = l_Lake_foldlUtf8___redArg(v_c_boxed_292_, v_f_290_, v_init_291_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8(lean_object* v_00_u03c3_294_, uint32_t v_c_295_, lean_object* v_f_296_, lean_object* v_init_297_){
_start:
{
lean_object* v___f_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___f_298_ = lean_alloc_closure((void*)(l_Lake_foldlUtf8___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_298_, 0, v_f_296_);
v___x_299_ = ((lean_object*)(l_Lake_foldlUtf8___redArg___closed__9));
v___x_300_ = l_Lake_foldlUtf8M___redArg(v___x_299_, v_c_295_, v___f_298_, v_init_297_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___boxed(lean_object* v_00_u03c3_301_, lean_object* v_c_302_, lean_object* v_f_303_, lean_object* v_init_304_){
_start:
{
uint32_t v_c_boxed_305_; lean_object* v_res_306_; 
v_c_boxed_305_ = lean_unbox_uint32(v_c_302_);
lean_dec(v_c_302_);
v_res_306_ = l_Lake_foldlUtf8(v_00_u03c3_301_, v_c_boxed_305_, v_f_303_, v_init_304_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___at___00Lake_uriEscapeChar_spec__0(uint32_t v_c_307_, lean_object* v_init_308_){
_start:
{
uint32_t v___x_309_; uint8_t v___x_310_; 
v___x_309_ = 127;
v___x_310_ = lean_uint32_dec_le(v_c_307_, v___x_309_);
if (v___x_310_ == 0)
{
uint32_t v___x_311_; uint8_t v___x_312_; 
v___x_311_ = 2047;
v___x_312_ = lean_uint32_dec_le(v_c_307_, v___x_311_);
if (v___x_312_ == 0)
{
uint32_t v___x_313_; uint8_t v___x_314_; 
v___x_313_ = 65535;
v___x_314_ = lean_uint32_dec_le(v_c_307_, v___x_313_);
if (v___x_314_ == 0)
{
uint32_t v___x_315_; uint32_t v___x_316_; uint8_t v___x_317_; uint8_t v___x_318_; uint8_t v___x_319_; uint8_t v___x_320_; uint8_t v___x_321_; lean_object* v___x_322_; uint32_t v___x_323_; uint32_t v___x_324_; uint8_t v___x_325_; uint8_t v___x_326_; uint8_t v___x_327_; uint8_t v___x_328_; uint8_t v___x_329_; lean_object* v___x_330_; uint32_t v___x_331_; uint32_t v___x_332_; uint8_t v___x_333_; uint8_t v___x_334_; uint8_t v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; uint8_t v___x_338_; uint8_t v___x_339_; lean_object* v___x_340_; 
v___x_315_ = 18;
v___x_316_ = lean_uint32_shift_right(v_c_307_, v___x_315_);
v___x_317_ = lean_uint32_to_uint8(v___x_316_);
v___x_318_ = 7;
v___x_319_ = lean_uint8_land(v___x_317_, v___x_318_);
v___x_320_ = 240;
v___x_321_ = lean_uint8_lor(v___x_319_, v___x_320_);
v___x_322_ = l_Lake_uriEscapeByte(v___x_321_, v_init_308_);
v___x_323_ = 12;
v___x_324_ = lean_uint32_shift_right(v_c_307_, v___x_323_);
v___x_325_ = lean_uint32_to_uint8(v___x_324_);
v___x_326_ = 63;
v___x_327_ = lean_uint8_land(v___x_325_, v___x_326_);
v___x_328_ = 128;
v___x_329_ = lean_uint8_lor(v___x_327_, v___x_328_);
v___x_330_ = l_Lake_uriEscapeByte(v___x_329_, v___x_322_);
v___x_331_ = 6;
v___x_332_ = lean_uint32_shift_right(v_c_307_, v___x_331_);
v___x_333_ = lean_uint32_to_uint8(v___x_332_);
v___x_334_ = lean_uint8_land(v___x_333_, v___x_326_);
v___x_335_ = lean_uint8_lor(v___x_334_, v___x_328_);
v___x_336_ = l_Lake_uriEscapeByte(v___x_335_, v___x_330_);
v___x_337_ = lean_uint32_to_uint8(v_c_307_);
v___x_338_ = lean_uint8_land(v___x_337_, v___x_326_);
v___x_339_ = lean_uint8_lor(v___x_338_, v___x_328_);
v___x_340_ = l_Lake_uriEscapeByte(v___x_339_, v___x_336_);
return v___x_340_;
}
else
{
uint32_t v___x_341_; uint32_t v___x_342_; uint8_t v___x_343_; uint8_t v___x_344_; uint8_t v___x_345_; uint8_t v___x_346_; uint8_t v___x_347_; lean_object* v___x_348_; uint32_t v___x_349_; uint32_t v___x_350_; uint8_t v___x_351_; uint8_t v___x_352_; uint8_t v___x_353_; uint8_t v___x_354_; uint8_t v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; uint8_t v___x_358_; uint8_t v___x_359_; lean_object* v___x_360_; 
v___x_341_ = 12;
v___x_342_ = lean_uint32_shift_right(v_c_307_, v___x_341_);
v___x_343_ = lean_uint32_to_uint8(v___x_342_);
v___x_344_ = 15;
v___x_345_ = lean_uint8_land(v___x_343_, v___x_344_);
v___x_346_ = 224;
v___x_347_ = lean_uint8_lor(v___x_345_, v___x_346_);
v___x_348_ = l_Lake_uriEscapeByte(v___x_347_, v_init_308_);
v___x_349_ = 6;
v___x_350_ = lean_uint32_shift_right(v_c_307_, v___x_349_);
v___x_351_ = lean_uint32_to_uint8(v___x_350_);
v___x_352_ = 63;
v___x_353_ = lean_uint8_land(v___x_351_, v___x_352_);
v___x_354_ = 128;
v___x_355_ = lean_uint8_lor(v___x_353_, v___x_354_);
v___x_356_ = l_Lake_uriEscapeByte(v___x_355_, v___x_348_);
v___x_357_ = lean_uint32_to_uint8(v_c_307_);
v___x_358_ = lean_uint8_land(v___x_357_, v___x_352_);
v___x_359_ = lean_uint8_lor(v___x_358_, v___x_354_);
v___x_360_ = l_Lake_uriEscapeByte(v___x_359_, v___x_356_);
return v___x_360_;
}
}
else
{
uint32_t v___x_361_; uint32_t v___x_362_; uint8_t v___x_363_; uint8_t v___x_364_; uint8_t v___x_365_; uint8_t v___x_366_; uint8_t v___x_367_; lean_object* v___x_368_; uint8_t v___x_369_; uint8_t v___x_370_; uint8_t v___x_371_; uint8_t v___x_372_; uint8_t v___x_373_; lean_object* v___x_374_; 
v___x_361_ = 6;
v___x_362_ = lean_uint32_shift_right(v_c_307_, v___x_361_);
v___x_363_ = lean_uint32_to_uint8(v___x_362_);
v___x_364_ = 31;
v___x_365_ = lean_uint8_land(v___x_363_, v___x_364_);
v___x_366_ = 192;
v___x_367_ = lean_uint8_lor(v___x_365_, v___x_366_);
v___x_368_ = l_Lake_uriEscapeByte(v___x_367_, v_init_308_);
v___x_369_ = lean_uint32_to_uint8(v_c_307_);
v___x_370_ = 63;
v___x_371_ = lean_uint8_land(v___x_369_, v___x_370_);
v___x_372_ = 128;
v___x_373_ = lean_uint8_lor(v___x_371_, v___x_372_);
v___x_374_ = l_Lake_uriEscapeByte(v___x_373_, v___x_368_);
return v___x_374_;
}
}
else
{
uint8_t v___x_375_; lean_object* v___x_376_; 
v___x_375_ = lean_uint32_to_uint8(v_c_307_);
v___x_376_ = l_Lake_uriEscapeByte(v___x_375_, v_init_308_);
return v___x_376_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___at___00Lake_uriEscapeChar_spec__0___boxed(lean_object* v_c_377_, lean_object* v_init_378_){
_start:
{
uint32_t v_c_boxed_379_; lean_object* v_res_380_; 
v_c_boxed_379_ = lean_unbox_uint32(v_c_377_);
lean_dec(v_c_377_);
v_res_380_ = l_Lake_foldlUtf8M___at___00Lake_uriEscapeChar_spec__0(v_c_boxed_379_, v_init_378_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lake_uriEscapeChar(uint32_t v_c_381_, lean_object* v_s_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Lake_foldlUtf8M___at___00Lake_uriEscapeChar_spec__0(v_c_381_, v_s_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lake_uriEscapeChar___boxed(lean_object* v_c_384_, lean_object* v_s_385_){
_start:
{
uint32_t v_c_boxed_386_; lean_object* v_res_387_; 
v_c_boxed_386_ = lean_unbox_uint32(v_c_384_);
lean_dec(v_c_384_);
v_res_387_ = l_Lake_uriEscapeChar(v_c_boxed_386_, v_s_385_);
return v_res_387_;
}
}
LEAN_EXPORT uint8_t l_Lake_isUriUnreservedMark(uint32_t v_c_388_){
_start:
{
uint32_t v___x_389_; uint8_t v___x_390_; 
v___x_389_ = 45;
v___x_390_ = lean_uint32_dec_eq(v_c_388_, v___x_389_);
if (v___x_390_ == 0)
{
uint32_t v___x_391_; uint8_t v___x_392_; 
v___x_391_ = 95;
v___x_392_ = lean_uint32_dec_eq(v_c_388_, v___x_391_);
if (v___x_392_ == 0)
{
uint32_t v___x_393_; uint8_t v___x_394_; 
v___x_393_ = 46;
v___x_394_ = lean_uint32_dec_eq(v_c_388_, v___x_393_);
if (v___x_394_ == 0)
{
uint32_t v___x_395_; uint8_t v___x_396_; 
v___x_395_ = 126;
v___x_396_ = lean_uint32_dec_eq(v_c_388_, v___x_395_);
return v___x_396_;
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
else
{
return v___x_390_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_isUriUnreservedMark___boxed(lean_object* v_c_397_){
_start:
{
uint32_t v_c_boxed_398_; uint8_t v_res_399_; lean_object* v_r_400_; 
v_c_boxed_398_ = lean_unbox_uint32(v_c_397_);
lean_dec(v_c_397_);
v_res_399_ = l_Lake_isUriUnreservedMark(v_c_boxed_398_);
v_r_400_ = lean_box(v_res_399_);
return v_r_400_;
}
}
LEAN_EXPORT lean_object* l_Lake_uriEncodeChar(uint32_t v_c_401_, lean_object* v_s_402_){
_start:
{
uint8_t v___y_414_; uint32_t v___x_421_; uint8_t v___x_422_; 
v___x_421_ = 65;
v___x_422_ = lean_uint32_dec_le(v___x_421_, v_c_401_);
if (v___x_422_ == 0)
{
v___y_414_ = v___x_422_;
goto v___jp_413_;
}
else
{
uint32_t v___x_423_; uint8_t v___x_424_; 
v___x_423_ = 90;
v___x_424_ = lean_uint32_dec_le(v_c_401_, v___x_423_);
v___y_414_ = v___x_424_;
goto v___jp_413_;
}
v___jp_403_:
{
uint8_t v___x_404_; 
v___x_404_ = l_Lake_isUriUnreservedMark(v_c_401_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; 
v___x_405_ = l_Lake_foldlUtf8M___at___00Lake_uriEscapeChar_spec__0(v_c_401_, v_s_402_);
return v___x_405_;
}
else
{
lean_object* v___x_406_; 
v___x_406_ = lean_string_push(v_s_402_, v_c_401_);
return v___x_406_;
}
}
v___jp_407_:
{
uint32_t v___x_408_; uint8_t v___x_409_; 
v___x_408_ = 48;
v___x_409_ = lean_uint32_dec_le(v___x_408_, v_c_401_);
if (v___x_409_ == 0)
{
goto v___jp_403_;
}
else
{
uint32_t v___x_410_; uint8_t v___x_411_; 
v___x_410_ = 57;
v___x_411_ = lean_uint32_dec_le(v_c_401_, v___x_410_);
if (v___x_411_ == 0)
{
goto v___jp_403_;
}
else
{
lean_object* v___x_412_; 
v___x_412_ = lean_string_push(v_s_402_, v_c_401_);
return v___x_412_;
}
}
}
v___jp_413_:
{
if (v___y_414_ == 0)
{
uint32_t v___x_415_; uint8_t v___x_416_; 
v___x_415_ = 97;
v___x_416_ = lean_uint32_dec_le(v___x_415_, v_c_401_);
if (v___x_416_ == 0)
{
goto v___jp_407_;
}
else
{
uint32_t v___x_417_; uint8_t v___x_418_; 
v___x_417_ = 122;
v___x_418_ = lean_uint32_dec_le(v_c_401_, v___x_417_);
if (v___x_418_ == 0)
{
goto v___jp_407_;
}
else
{
lean_object* v___x_419_; 
v___x_419_ = lean_string_push(v_s_402_, v_c_401_);
return v___x_419_;
}
}
}
else
{
lean_object* v___x_420_; 
v___x_420_ = lean_string_push(v_s_402_, v_c_401_);
return v___x_420_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_uriEncodeChar___boxed(lean_object* v_c_425_, lean_object* v_s_426_){
_start:
{
uint32_t v_c_boxed_427_; lean_object* v_res_428_; 
v_c_boxed_427_ = lean_unbox_uint32(v_c_425_);
lean_dec(v_c_425_);
v_res_428_ = l_Lake_uriEncodeChar(v_c_boxed_427_, v_s_426_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___redArg(lean_object* v___x_429_, lean_object* v_s_430_, lean_object* v_a_431_, lean_object* v_b_432_){
_start:
{
uint8_t v_decide_433_; 
v_decide_433_ = lean_nat_dec_eq(v_a_431_, v___x_429_);
if (v_decide_433_ == 0)
{
uint32_t v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_434_ = lean_string_utf8_get_fast(v_s_430_, v_a_431_);
v___x_435_ = lean_string_utf8_next_fast(v_s_430_, v_a_431_);
lean_dec(v_a_431_);
v___x_436_ = l_Lake_uriEncodeChar(v___x_434_, v_b_432_);
v_a_431_ = v___x_435_;
v_b_432_ = v___x_436_;
goto _start;
}
else
{
lean_dec(v_a_431_);
return v_b_432_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___redArg___boxed(lean_object* v___x_438_, lean_object* v_s_439_, lean_object* v_a_440_, lean_object* v_b_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___redArg(v___x_438_, v_s_439_, v_a_440_, v_b_441_);
lean_dec_ref(v_s_439_);
lean_dec(v___x_438_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lake_uriEncode(lean_object* v_s_443_, lean_object* v_init_444_){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_445_ = lean_unsigned_to_nat(0u);
v___x_446_ = lean_string_utf8_byte_size(v_s_443_);
lean_inc_ref(v_s_443_);
v___x_447_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_447_, 0, v_s_443_);
lean_ctor_set(v___x_447_, 1, v___x_445_);
lean_ctor_set(v___x_447_, 2, v___x_446_);
v___x_448_ = l_String_Slice_positions(v___x_447_);
lean_dec_ref_known(v___x_447_, 3);
v___x_449_ = l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___redArg(v___x_446_, v_s_443_, v___x_448_, v_init_444_);
lean_dec_ref(v_s_443_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0(lean_object* v___x_450_, lean_object* v___x_451_, lean_object* v_s_452_, lean_object* v_inst_453_, lean_object* v_R_454_, lean_object* v_a_455_, lean_object* v_b_456_, lean_object* v_c_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___redArg(v___x_451_, v_s_452_, v_a_455_, v_b_456_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___boxed(lean_object* v___x_459_, lean_object* v___x_460_, lean_object* v_s_461_, lean_object* v_inst_462_, lean_object* v_R_463_, lean_object* v_a_464_, lean_object* v_b_465_, lean_object* v_c_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0(v___x_459_, v___x_460_, v_s_461_, v_inst_462_, v_R_463_, v_a_464_, v_b_465_, v_c_466_);
lean_dec_ref(v_s_461_);
lean_dec(v___x_460_);
lean_dec_ref(v___x_459_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lake_Internal_getCurl(){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = ((lean_object*)(l_Lake_Internal_getCurl___closed__0));
v___x_472_ = lean_io_getenv(v___x_471_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v___x_473_; 
v___x_473_ = ((lean_object*)(l_Lake_Internal_getCurl___closed__1));
return v___x_473_;
}
else
{
lean_object* v_val_474_; 
v_val_474_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_val_474_);
lean_dec_ref_known(v___x_472_, 1);
return v_val_474_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Internal_getCurl___boxed(lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lake_Internal_getCurl();
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0(lean_object* v_x_479_){
_start:
{
if (lean_obj_tag(v_x_479_) == 0)
{
lean_object* v___x_480_; 
v___x_480_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0___closed__0));
return v___x_480_;
}
else
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_Json_getNat_x3f(v_x_479_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_489_; 
v_a_482_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_489_ == 0)
{
v___x_484_ = v___x_481_;
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_481_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_482_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
else
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_498_; 
v_a_490_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_498_ == 0)
{
v___x_492_ = v___x_481_;
v_isShared_493_ = v_isSharedCheck_498_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_481_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_498_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_494_; lean_object* v___x_496_; 
v___x_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_494_, 0, v_a_490_);
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 0, v___x_494_);
v___x_496_ = v___x_492_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_494_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__1(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_500_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__0));
v___x_501_ = lean_unsigned_to_nat(2u);
v___x_502_ = lean_mk_empty_array_with_capacity(v___x_501_);
v___x_503_ = lean_array_push(v___x_502_, v___x_500_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1(lean_object* v_as_504_, size_t v_i_505_, size_t v_stop_506_, lean_object* v_b_507_){
_start:
{
uint8_t v___x_508_; 
v___x_508_ = lean_usize_dec_eq(v_i_505_, v_stop_506_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; size_t v___x_513_; size_t v___x_514_; 
v___x_509_ = lean_array_uget_borrowed(v_as_504_, v_i_505_);
v___x_510_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__1);
lean_inc(v___x_509_);
v___x_511_ = lean_array_push(v___x_510_, v___x_509_);
v___x_512_ = l_Array_append___redArg(v_b_507_, v___x_511_);
lean_dec_ref(v___x_511_);
v___x_513_ = ((size_t)1ULL);
v___x_514_ = lean_usize_add(v_i_505_, v___x_513_);
v_i_505_ = v___x_514_;
v_b_507_ = v___x_512_;
goto _start;
}
else
{
return v_b_507_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___boxed(lean_object* v_as_516_, lean_object* v_i_517_, lean_object* v_stop_518_, lean_object* v_b_519_){
_start:
{
size_t v_i_boxed_520_; size_t v_stop_boxed_521_; lean_object* v_res_522_; 
v_i_boxed_520_ = lean_unbox_usize(v_i_517_);
lean_dec(v_i_517_);
v_stop_boxed_521_ = lean_unbox_usize(v_stop_518_);
lean_dec(v_stop_518_);
v_res_522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1(v_as_516_, v_i_boxed_520_, v_stop_boxed_521_, v_b_519_);
lean_dec_ref(v_as_516_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lake_getUrl_x3f(lean_object* v_url_558_, lean_object* v_headers_559_, lean_object* v_a_560_){
_start:
{
lean_object* v___y_563_; lean_object* v_a_564_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v_a_569_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v_a_583_; lean_object* v___y_590_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v_a_594_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v_val_646_; lean_object* v___y_672_; lean_object* v_args_678_; lean_object* v___x_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
v_args_678_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__17));
v___x_679_ = lean_unsigned_to_nat(0u);
v___x_680_ = lean_array_get_size(v_headers_559_);
v___x_681_ = lean_nat_dec_lt(v___x_679_, v___x_680_);
if (v___x_681_ == 0)
{
v___y_672_ = v_args_678_;
goto v___jp_671_;
}
else
{
uint8_t v___x_682_; 
v___x_682_ = lean_nat_dec_le(v___x_680_, v___x_680_);
if (v___x_682_ == 0)
{
if (v___x_681_ == 0)
{
v___y_672_ = v_args_678_;
goto v___jp_671_;
}
else
{
size_t v___x_683_; size_t v___x_684_; lean_object* v___x_685_; 
v___x_683_ = ((size_t)0ULL);
v___x_684_ = lean_usize_of_nat(v___x_680_);
v___x_685_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1(v_headers_559_, v___x_683_, v___x_684_, v_args_678_);
v___y_672_ = v___x_685_;
goto v___jp_671_;
}
}
else
{
size_t v___x_686_; size_t v___x_687_; lean_object* v___x_688_; 
v___x_686_ = ((size_t)0ULL);
v___x_687_ = lean_usize_of_nat(v___x_680_);
v___x_688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1(v_headers_559_, v___x_686_, v___x_687_, v_args_678_);
v___y_672_ = v___x_688_;
goto v___jp_671_;
}
}
v___jp_562_:
{
lean_object* v___x_565_; 
v___x_565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_565_, 0, v___y_563_);
lean_ctor_set(v___x_565_, 1, v_a_564_);
return v___x_565_;
}
v___jp_566_:
{
lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_570_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__0));
v___x_571_ = lean_string_append(v___x_570_, v_a_569_);
lean_dec_ref(v_a_569_);
v___x_572_ = 3;
v___x_573_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_573_, 0, v___x_571_);
lean_ctor_set_uint8(v___x_573_, sizeof(void*)*1, v___x_572_);
v___x_574_ = lean_array_push(v___y_568_, v___x_573_);
v___y_563_ = v___y_567_;
v_a_564_ = v___x_574_;
goto v___jp_562_;
}
v___jp_575_:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__2));
v___x_579_ = lean_array_push(v___y_577_, v___x_578_);
v___y_563_ = v___y_576_;
v_a_564_ = v___x_579_;
goto v___jp_562_;
}
v___jp_580_:
{
lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_584_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__3));
v___x_585_ = lean_string_append(v___x_584_, v_a_583_);
lean_dec_ref(v_a_583_);
v___x_586_ = 3;
v___x_587_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_587_, 0, v___x_585_);
lean_ctor_set_uint8(v___x_587_, sizeof(void*)*1, v___x_586_);
v___x_588_ = lean_array_push(v___y_582_, v___x_587_);
v___y_563_ = v___y_581_;
v_a_564_ = v___x_588_;
goto v___jp_562_;
}
v___jp_589_:
{
if (lean_obj_tag(v_a_594_) == 0)
{
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
v___y_576_ = v___y_590_;
v___y_577_ = v___y_593_;
goto v___jp_575_;
}
else
{
lean_object* v_val_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_627_; 
v_val_595_ = lean_ctor_get(v_a_594_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v_a_594_);
if (v_isSharedCheck_627_ == 0)
{
v___x_597_ = v_a_594_;
v_isShared_598_ = v_isSharedCheck_627_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_val_595_);
lean_dec(v_a_594_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_627_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_599_; uint8_t v___x_600_; 
v___x_599_ = lean_unsigned_to_nat(200u);
v___x_600_ = lean_nat_dec_eq(v_val_595_, v___x_599_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; uint8_t v___x_602_; 
lean_del_object(v___x_597_);
lean_dec(v___y_591_);
v___x_601_ = lean_unsigned_to_nat(404u);
v___x_602_ = lean_nat_dec_eq(v_val_595_, v___x_601_);
if (v___x_602_ == 0)
{
lean_object* v_stdout_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; uint8_t v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v_stdout_603_ = lean_ctor_get(v___y_592_, 0);
lean_inc_ref(v_stdout_603_);
lean_dec_ref(v___y_592_);
v___x_604_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__4));
v___x_605_ = l_Nat_reprFast(v_val_595_);
v___x_606_ = lean_string_append(v___x_604_, v___x_605_);
lean_dec_ref(v___x_605_);
v___x_607_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__5));
v___x_608_ = lean_string_append(v___x_606_, v___x_607_);
v___x_609_ = lean_string_append(v___x_608_, v_stdout_603_);
lean_dec_ref(v_stdout_603_);
v___x_610_ = 3;
v___x_611_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_611_, 0, v___x_609_);
lean_ctor_set_uint8(v___x_611_, sizeof(void*)*1, v___x_610_);
v___x_612_ = lean_array_push(v___y_593_, v___x_611_);
v___y_563_ = v___y_590_;
v_a_564_ = v___x_612_;
goto v___jp_562_;
}
else
{
lean_object* v___x_613_; lean_object* v___x_614_; 
lean_dec(v_val_595_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_590_);
v___x_613_ = lean_box(0);
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v___y_593_);
return v___x_614_;
}
}
else
{
lean_object* v_stdout_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v_str_619_; lean_object* v_startInclusive_620_; lean_object* v_endExclusive_621_; lean_object* v___x_622_; lean_object* v___x_624_; 
lean_dec(v_val_595_);
lean_dec(v___y_590_);
v_stdout_615_ = lean_ctor_get(v___y_592_, 0);
lean_inc_ref(v_stdout_615_);
lean_dec_ref(v___y_592_);
v___x_616_ = lean_string_utf8_byte_size(v_stdout_615_);
v___x_617_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_617_, 0, v_stdout_615_);
lean_ctor_set(v___x_617_, 1, v___y_591_);
lean_ctor_set(v___x_617_, 2, v___x_616_);
v___x_618_ = l_String_Slice_trimAscii(v___x_617_);
v_str_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc_ref(v_str_619_);
v_startInclusive_620_ = lean_ctor_get(v___x_618_, 1);
lean_inc(v_startInclusive_620_);
v_endExclusive_621_ = lean_ctor_get(v___x_618_, 2);
lean_inc(v_endExclusive_621_);
lean_dec_ref(v___x_618_);
v___x_622_ = lean_string_utf8_extract_fast(v_str_619_, v_startInclusive_620_, v_endExclusive_621_);
lean_dec(v_endExclusive_621_);
lean_dec(v_startInclusive_620_);
lean_dec_ref(v_str_619_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v___x_622_);
v___x_624_ = v___x_597_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_622_);
v___x_624_ = v_reuseFailAlloc_626_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_625_; 
v___x_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
lean_ctor_set(v___x_625_, 1, v___y_593_);
return v___x_625_;
}
}
}
}
}
v___jp_628_:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__6));
v___x_635_ = l_Lake_JsonObject_getJson_x3f(v___y_629_, v___x_634_);
lean_dec(v___y_629_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
v___y_576_ = v___y_630_;
v___y_577_ = v___y_633_;
goto v___jp_575_;
}
else
{
lean_object* v_val_636_; lean_object* v___x_637_; 
v_val_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_val_636_);
lean_dec_ref_known(v___x_635_, 1);
v___x_637_ = l_Lean_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0(v_val_636_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
v_a_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_a_638_);
lean_dec_ref_known(v___x_637_, 1);
v___x_639_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__7));
v___x_640_ = lean_string_append(v___x_639_, v_a_638_);
lean_dec(v_a_638_);
v___y_567_ = v___y_630_;
v___y_568_ = v___y_633_;
v_a_569_ = v___x_640_;
goto v___jp_566_;
}
else
{
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_641_; 
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
v_a_641_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_a_641_);
lean_dec_ref_known(v___x_637_, 1);
v___y_567_ = v___y_630_;
v___y_568_ = v___y_633_;
v_a_569_ = v_a_641_;
goto v___jp_566_;
}
else
{
lean_object* v_a_642_; 
v_a_642_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_a_642_);
lean_dec_ref_known(v___x_637_, 1);
v___y_590_ = v___y_630_;
v___y_591_ = v___y_631_;
v___y_592_ = v___y_632_;
v___y_593_ = v___y_633_;
v_a_594_ = v_a_642_;
goto v___jp_589_;
}
}
}
}
v___jp_643_:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; uint8_t v___x_652_; uint8_t v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_647_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__8));
v___x_648_ = lean_array_push(v___y_645_, v_url_558_);
v___x_649_ = lean_box(0);
v___x_650_ = lean_unsigned_to_nat(0u);
v___x_651_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__9));
v___x_652_ = 1;
v___x_653_ = 0;
v___x_654_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_654_, 0, v___x_647_);
lean_ctor_set(v___x_654_, 1, v_val_646_);
lean_ctor_set(v___x_654_, 2, v___x_648_);
lean_ctor_set(v___x_654_, 3, v___x_649_);
lean_ctor_set(v___x_654_, 4, v___x_651_);
lean_ctor_set_uint8(v___x_654_, sizeof(void*)*5, v___x_652_);
lean_ctor_set_uint8(v___x_654_, sizeof(void*)*5 + 1, v___x_653_);
v___x_655_ = l_Lake_captureProc_x27(v___x_654_, v_a_560_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v_a_657_; lean_object* v_stderr_658_; lean_object* v___x_659_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_656_);
v_a_657_ = lean_ctor_get(v___x_655_, 1);
lean_inc(v_a_657_);
lean_dec_ref_known(v___x_655_, 2);
v_stderr_658_ = lean_ctor_get(v_a_656_, 1);
lean_inc_ref(v_stderr_658_);
v___x_659_ = l_Lean_Json_parse(v_stderr_658_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; 
lean_dec(v_a_656_);
v_a_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_a_660_);
lean_dec_ref_known(v___x_659_, 1);
v___y_581_ = v___y_644_;
v___y_582_ = v_a_657_;
v_a_583_ = v_a_660_;
goto v___jp_580_;
}
else
{
lean_object* v_a_661_; lean_object* v___x_662_; 
v_a_661_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_a_661_);
lean_dec_ref_known(v___x_659_, 1);
v___x_662_ = l_Lean_Json_getObj_x3f(v_a_661_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v_a_663_; 
lean_dec(v_a_656_);
v_a_663_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_a_663_);
lean_dec_ref_known(v___x_662_, 1);
v___y_581_ = v___y_644_;
v___y_582_ = v_a_657_;
v_a_583_ = v_a_663_;
goto v___jp_580_;
}
else
{
lean_object* v_a_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v_a_664_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_a_664_);
lean_dec_ref_known(v___x_662_, 1);
v___x_665_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__10));
v___x_666_ = l_Lake_JsonObject_getJson_x3f(v_a_664_, v___x_665_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_dec(v_a_664_);
lean_dec(v_a_656_);
v___y_576_ = v___y_644_;
v___y_577_ = v_a_657_;
goto v___jp_575_;
}
else
{
lean_object* v_val_667_; lean_object* v___x_668_; 
v_val_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_val_667_);
lean_dec_ref_known(v___x_666_, 1);
v___x_668_ = l_Lean_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0(v_val_667_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_dec_ref_known(v___x_668_, 1);
v___y_629_ = v_a_664_;
v___y_630_ = v___y_644_;
v___y_631_ = v___x_650_;
v___y_632_ = v_a_656_;
v___y_633_ = v_a_657_;
goto v___jp_628_;
}
else
{
if (lean_obj_tag(v___x_668_) == 0)
{
lean_dec_ref_known(v___x_668_, 1);
v___y_629_ = v_a_664_;
v___y_630_ = v___y_644_;
v___y_631_ = v___x_650_;
v___y_632_ = v_a_656_;
v___y_633_ = v_a_657_;
goto v___jp_628_;
}
else
{
lean_object* v_a_669_; 
lean_dec(v_a_664_);
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
lean_dec_ref_known(v___x_668_, 1);
v___y_590_ = v___y_644_;
v___y_591_ = v___x_650_;
v___y_592_ = v_a_656_;
v___y_593_ = v_a_657_;
v_a_594_ = v_a_669_;
goto v___jp_589_;
}
}
}
}
}
}
else
{
lean_object* v_a_670_; 
v_a_670_ = lean_ctor_get(v___x_655_, 1);
lean_inc(v_a_670_);
lean_dec_ref_known(v___x_655_, 2);
v___y_563_ = v___y_644_;
v_a_564_ = v_a_670_;
goto v___jp_562_;
}
}
v___jp_671_:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_673_ = ((lean_object*)(l_Lake_Internal_getCurl___closed__0));
v___x_674_ = lean_io_getenv(v___x_673_);
v___x_675_ = lean_array_get_size(v_a_560_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v___x_676_; 
v___x_676_ = ((lean_object*)(l_Lake_Internal_getCurl___closed__1));
v___y_644_ = v___x_675_;
v___y_645_ = v___y_672_;
v_val_646_ = v___x_676_;
goto v___jp_643_;
}
else
{
lean_object* v_val_677_; 
v_val_677_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_val_677_);
lean_dec_ref_known(v___x_674_, 1);
v___y_644_ = v___x_675_;
v___y_645_ = v___y_672_;
v_val_646_ = v_val_677_;
goto v___jp_643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getUrl_x3f___boxed(lean_object* v_url_689_, lean_object* v_headers_690_, lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lake_getUrl_x3f(v_url_689_, v_headers_690_, v_a_691_);
lean_dec_ref(v_headers_690_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lake_getUrl(lean_object* v_url_704_, lean_object* v_headers_705_, lean_object* v_a_706_){
_start:
{
lean_object* v___y_709_; lean_object* v_a_710_; lean_object* v_a_711_; lean_object* v___y_748_; lean_object* v_args_753_; lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; 
v_args_753_ = ((lean_object*)(l_Lake_getUrl___closed__0));
v___x_754_ = lean_unsigned_to_nat(0u);
v___x_755_ = lean_array_get_size(v_headers_705_);
v___x_756_ = lean_nat_dec_lt(v___x_754_, v___x_755_);
if (v___x_756_ == 0)
{
v___y_748_ = v_args_753_;
goto v___jp_747_;
}
else
{
uint8_t v___x_757_; 
v___x_757_ = lean_nat_dec_le(v___x_755_, v___x_755_);
if (v___x_757_ == 0)
{
if (v___x_756_ == 0)
{
v___y_748_ = v_args_753_;
goto v___jp_747_;
}
else
{
size_t v___x_758_; size_t v___x_759_; lean_object* v___x_760_; 
v___x_758_ = ((size_t)0ULL);
v___x_759_ = lean_usize_of_nat(v___x_755_);
v___x_760_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1(v_headers_705_, v___x_758_, v___x_759_, v_args_753_);
v___y_748_ = v___x_760_;
goto v___jp_747_;
}
}
else
{
size_t v___x_761_; size_t v___x_762_; lean_object* v___x_763_; 
v___x_761_ = ((size_t)0ULL);
v___x_762_ = lean_usize_of_nat(v___x_755_);
v___x_763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1(v_headers_705_, v___x_761_, v___x_762_, v_args_753_);
v___y_748_ = v___x_763_;
goto v___jp_747_;
}
}
v___jp_708_:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; uint8_t v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_712_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__8));
v___x_713_ = lean_array_push(v___y_709_, v_url_704_);
v___x_714_ = lean_box(0);
v___x_715_ = lean_unsigned_to_nat(0u);
v___x_716_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__9));
v___x_717_ = 1;
v___x_718_ = 0;
v___x_719_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_719_, 0, v___x_712_);
lean_ctor_set(v___x_719_, 1, v_a_710_);
lean_ctor_set(v___x_719_, 2, v___x_713_);
lean_ctor_set(v___x_719_, 3, v___x_714_);
lean_ctor_set(v___x_719_, 4, v___x_716_);
lean_ctor_set_uint8(v___x_719_, sizeof(void*)*5, v___x_717_);
lean_ctor_set_uint8(v___x_719_, sizeof(void*)*5 + 1, v___x_718_);
v___x_720_ = l_Lake_captureProc_x27(v___x_719_, v_a_711_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_737_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
v_a_722_ = lean_ctor_get(v___x_720_, 1);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_737_ == 0)
{
v___x_724_ = v___x_720_;
v_isShared_725_ = v_isSharedCheck_737_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_inc(v_a_721_);
lean_dec(v___x_720_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_737_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v_stdout_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v_str_730_; lean_object* v_startInclusive_731_; lean_object* v_endExclusive_732_; lean_object* v___x_733_; lean_object* v___x_735_; 
v_stdout_726_ = lean_ctor_get(v_a_721_, 0);
lean_inc_ref(v_stdout_726_);
lean_dec(v_a_721_);
v___x_727_ = lean_string_utf8_byte_size(v_stdout_726_);
v___x_728_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_728_, 0, v_stdout_726_);
lean_ctor_set(v___x_728_, 1, v___x_715_);
lean_ctor_set(v___x_728_, 2, v___x_727_);
v___x_729_ = l_String_Slice_trimAscii(v___x_728_);
v_str_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc_ref(v_str_730_);
v_startInclusive_731_ = lean_ctor_get(v___x_729_, 1);
lean_inc(v_startInclusive_731_);
v_endExclusive_732_ = lean_ctor_get(v___x_729_, 2);
lean_inc(v_endExclusive_732_);
lean_dec_ref(v___x_729_);
v___x_733_ = lean_string_utf8_extract_fast(v_str_730_, v_startInclusive_731_, v_endExclusive_732_);
lean_dec(v_endExclusive_732_);
lean_dec(v_startInclusive_731_);
lean_dec_ref(v_str_730_);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 0, v___x_733_);
v___x_735_ = v___x_724_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v_a_722_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
else
{
lean_object* v_a_738_; lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
v_a_738_ = lean_ctor_get(v___x_720_, 0);
v_a_739_ = lean_ctor_get(v___x_720_, 1);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_720_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_inc(v_a_738_);
lean_dec(v___x_720_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_738_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_a_739_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
v___jp_747_:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = ((lean_object*)(l_Lake_Internal_getCurl___closed__0));
v___x_750_ = lean_io_getenv(v___x_749_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v___x_751_; 
v___x_751_ = ((lean_object*)(l_Lake_Internal_getCurl___closed__1));
v___y_709_ = v___y_748_;
v_a_710_ = v___x_751_;
v_a_711_ = v_a_706_;
goto v___jp_708_;
}
else
{
lean_object* v_val_752_; 
v_val_752_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_val_752_);
lean_dec_ref_known(v___x_750_, 1);
v___y_709_ = v___y_748_;
v_a_710_ = v_val_752_;
v_a_711_ = v_a_706_;
goto v___jp_708_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getUrl___boxed(lean_object* v_url_764_, lean_object* v_headers_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lake_getUrl(v_url_764_, v_headers_765_, v_a_766_);
lean_dec_ref(v_headers_765_);
return v_res_768_;
}
}
lean_object* runtime_initialize_Lake_Util_Log(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_JsonObject(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Proc(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Url(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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

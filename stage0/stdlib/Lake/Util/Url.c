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
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_io_getenv(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_uriEncode___boxed(lean_object*, lean_object*);
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
uint32_t l_Lake_hexEncodeByte(uint8_t v_b_1_){
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
LEAN_EXPORT void l_Lake_hexEncodeByte_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_1_ = stack[0].m_num;
uint32_t v_res_51_;
v_res_51_ = l_Lake_hexEncodeByte(v_b_1_);
stack->m_num = v_res_51_;
}
LEAN_EXPORT lean_object* l_Lake_hexEncodeByte___boxed(lean_object* v_b_52_){
_start:
{
uint8_t v_b_boxed_53_; uint32_t v_res_54_; lean_object* v_r_55_; 
v_b_boxed_53_ = lean_unbox(v_b_52_);
v_res_54_ = l_Lake_hexEncodeByte(v_b_boxed_53_);
v_r_55_ = lean_box_uint32(v_res_54_);
return v_r_55_;
}
}
lean_object* l_Lake_uriEscapeByte(uint8_t v_b_56_, lean_object* v_s_57_){
_start:
{
uint32_t v___x_58_; lean_object* v___x_59_; uint8_t v___x_60_; uint8_t v___x_61_; uint32_t v___x_62_; lean_object* v___x_63_; uint8_t v___x_64_; uint8_t v___x_65_; uint32_t v___x_66_; lean_object* v___x_67_; 
v___x_58_ = 37;
v___x_59_ = lean_string_push(v_s_57_, v___x_58_);
v___x_60_ = 4;
v___x_61_ = lean_uint8_shift_right(v_b_56_, v___x_60_);
v___x_62_ = l_Lake_hexEncodeByte(v___x_61_);
v___x_63_ = lean_string_push(v___x_59_, v___x_62_);
v___x_64_ = 15;
v___x_65_ = lean_uint8_land(v_b_56_, v___x_64_);
v___x_66_ = l_Lake_hexEncodeByte(v___x_65_);
v___x_67_ = lean_string_push(v___x_63_, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT void l_Lake_uriEscapeByte_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_56_ = stack[0].m_num;
lean_object* v_s_57_ = stack[1].m_obj;
lean_object* v_res_68_;
v_res_68_ = l_Lake_uriEscapeByte(v_b_56_, v_s_57_);
stack->m_obj
 = v_res_68_;
}
LEAN_EXPORT lean_object* l_Lake_uriEscapeByte___boxed(lean_object* v_b_69_, lean_object* v_s_70_){
_start:
{
uint8_t v_b_boxed_71_; lean_object* v_res_72_; 
v_b_boxed_71_ = lean_unbox(v_b_69_);
v_res_72_ = l_Lake_uriEscapeByte(v_b_boxed_71_, v_s_70_);
return v_res_72_;
}
}
lean_object* l_Lake_foldlUtf8M___redArg___lam__0(uint32_t v_c_73_, uint8_t v___x_74_, uint8_t v___x_75_, lean_object* v_f_76_, lean_object* v_s_77_){
_start:
{
uint8_t v___x_78_; uint8_t v___x_79_; uint8_t v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_78_ = lean_uint32_to_uint8(v_c_73_);
v___x_79_ = lean_uint8_land(v___x_78_, v___x_74_);
v___x_80_ = lean_uint8_lor(v___x_79_, v___x_75_);
v___x_81_ = lean_box(v___x_80_);
v___x_82_ = lean_apply_2(v_f_76_, v_s_77_, v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT void l_Lake_foldlUtf8M___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_73_ = stack[0].m_num;
uint8_t v___x_74_ = stack[1].m_num;
uint8_t v___x_75_ = stack[2].m_num;
lean_object* v_f_76_ = stack[3].m_obj;
lean_object* v_s_77_ = stack[4].m_obj;
lean_object* v_res_83_;
v_res_83_ = l_Lake_foldlUtf8M___redArg___lam__0(v_c_73_, v___x_74_, v___x_75_, v_f_76_, v_s_77_);
stack->m_obj
 = v_res_83_;
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__0___boxed(lean_object* v_c_84_, lean_object* v___x_85_, lean_object* v___x_86_, lean_object* v_f_87_, lean_object* v_s_88_){
_start:
{
uint32_t v_c_boxed_89_; uint8_t v___x_390__boxed_90_; uint8_t v___x_391__boxed_91_; lean_object* v_res_92_; 
v_c_boxed_89_ = lean_unbox_uint32(v_c_84_);
lean_dec(v_c_84_);
v___x_390__boxed_90_ = lean_unbox(v___x_85_);
v___x_391__boxed_91_ = lean_unbox(v___x_86_);
v_res_92_ = l_Lake_foldlUtf8M___redArg___lam__0(v_c_boxed_89_, v___x_390__boxed_90_, v___x_391__boxed_91_, v_f_87_, v_s_88_);
return v_res_92_;
}
}
lean_object* l_Lake_foldlUtf8M___redArg___lam__1(uint32_t v_c_93_, uint8_t v___x_94_, uint8_t v___x_95_, lean_object* v_f_96_, lean_object* v_toBind_97_, lean_object* v___f_98_, lean_object* v_s_99_){
_start:
{
uint32_t v___x_100_; uint32_t v___x_101_; uint8_t v___x_102_; uint8_t v___x_103_; uint8_t v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_100_ = 6;
v___x_101_ = lean_uint32_shift_right(v_c_93_, v___x_100_);
v___x_102_ = lean_uint32_to_uint8(v___x_101_);
v___x_103_ = lean_uint8_land(v___x_102_, v___x_94_);
v___x_104_ = lean_uint8_lor(v___x_103_, v___x_95_);
v___x_105_ = lean_box(v___x_104_);
v___x_106_ = lean_apply_2(v_f_96_, v_s_99_, v___x_105_);
v___x_107_ = lean_apply_4(v_toBind_97_, lean_box(0), lean_box(0), v___x_106_, v___f_98_);
return v___x_107_;
}
}
LEAN_EXPORT void l_Lake_foldlUtf8M___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_93_ = stack[0].m_num;
uint8_t v___x_94_ = stack[1].m_num;
uint8_t v___x_95_ = stack[2].m_num;
lean_object* v_f_96_ = stack[3].m_obj;
lean_object* v_toBind_97_ = stack[4].m_obj;
lean_object* v___f_98_ = stack[5].m_obj;
lean_object* v_s_99_ = stack[6].m_obj;
lean_object* v_res_108_;
v_res_108_ = l_Lake_foldlUtf8M___redArg___lam__1(v_c_93_, v___x_94_, v___x_95_, v_f_96_, v_toBind_97_, v___f_98_, v_s_99_);
stack->m_obj
 = v_res_108_;
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__1___boxed(lean_object* v_c_109_, lean_object* v___x_110_, lean_object* v___x_111_, lean_object* v_f_112_, lean_object* v_toBind_113_, lean_object* v___f_114_, lean_object* v_s_115_){
_start:
{
uint32_t v_c_boxed_116_; uint8_t v___x_415__boxed_117_; uint8_t v___x_416__boxed_118_; lean_object* v_res_119_; 
v_c_boxed_116_ = lean_unbox_uint32(v_c_109_);
lean_dec(v_c_109_);
v___x_415__boxed_117_ = lean_unbox(v___x_110_);
v___x_416__boxed_118_ = lean_unbox(v___x_111_);
v_res_119_ = l_Lake_foldlUtf8M___redArg___lam__1(v_c_boxed_116_, v___x_415__boxed_117_, v___x_416__boxed_118_, v_f_112_, v_toBind_113_, v___f_114_, v_s_115_);
return v_res_119_;
}
}
lean_object* l_Lake_foldlUtf8M___redArg___lam__2(uint32_t v_c_120_, lean_object* v_f_121_, lean_object* v_toBind_122_, lean_object* v_s_123_){
_start:
{
uint32_t v___x_124_; uint32_t v___x_125_; uint8_t v___x_126_; uint8_t v___x_127_; uint8_t v___x_128_; uint8_t v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___f_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___f_137_; uint8_t v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_124_ = 12;
v___x_125_ = lean_uint32_shift_right(v_c_120_, v___x_124_);
v___x_126_ = lean_uint32_to_uint8(v___x_125_);
v___x_127_ = 63;
v___x_128_ = lean_uint8_land(v___x_126_, v___x_127_);
v___x_129_ = 128;
v___x_130_ = lean_box_uint32(v_c_120_);
v___x_131_ = lean_box(v___x_127_);
v___x_132_ = lean_box(v___x_129_);
lean_inc_n(v_f_121_, 2);
v___f_133_ = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_133_, 0, v___x_130_);
lean_closure_set(v___f_133_, 1, v___x_131_);
lean_closure_set(v___f_133_, 2, v___x_132_);
lean_closure_set(v___f_133_, 3, v_f_121_);
v___x_134_ = lean_box_uint32(v_c_120_);
v___x_135_ = lean_box(v___x_127_);
v___x_136_ = lean_box(v___x_129_);
lean_inc(v_toBind_122_);
v___f_137_ = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_137_, 0, v___x_134_);
lean_closure_set(v___f_137_, 1, v___x_135_);
lean_closure_set(v___f_137_, 2, v___x_136_);
lean_closure_set(v___f_137_, 3, v_f_121_);
lean_closure_set(v___f_137_, 4, v_toBind_122_);
lean_closure_set(v___f_137_, 5, v___f_133_);
v___x_138_ = lean_uint8_lor(v___x_128_, v___x_129_);
v___x_139_ = lean_box(v___x_138_);
v___x_140_ = lean_apply_2(v_f_121_, v_s_123_, v___x_139_);
v___x_141_ = lean_apply_4(v_toBind_122_, lean_box(0), lean_box(0), v___x_140_, v___f_137_);
return v___x_141_;
}
}
LEAN_EXPORT void l_Lake_foldlUtf8M___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_120_ = stack[0].m_num;
lean_object* v_f_121_ = stack[1].m_obj;
lean_object* v_toBind_122_ = stack[2].m_obj;
lean_object* v_s_123_ = stack[3].m_obj;
lean_object* v_res_142_;
v_res_142_ = l_Lake_foldlUtf8M___redArg___lam__2(v_c_120_, v_f_121_, v_toBind_122_, v_s_123_);
stack->m_obj
 = v_res_142_;
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__2___boxed(lean_object* v_c_143_, lean_object* v_f_144_, lean_object* v_toBind_145_, lean_object* v_s_146_){
_start:
{
uint32_t v_c_boxed_147_; lean_object* v_res_148_; 
v_c_boxed_147_ = lean_unbox_uint32(v_c_143_);
lean_dec(v_c_143_);
v_res_148_ = l_Lake_foldlUtf8M___redArg___lam__2(v_c_boxed_147_, v_f_144_, v_toBind_145_, v_s_146_);
return v_res_148_;
}
}
lean_object* l_Lake_foldlUtf8M___redArg___lam__4(uint32_t v_c_149_, lean_object* v_f_150_, lean_object* v_toBind_151_, lean_object* v_s_152_){
_start:
{
uint32_t v___x_153_; uint32_t v___x_154_; uint8_t v___x_155_; uint8_t v___x_156_; uint8_t v___x_157_; uint8_t v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___f_162_; uint8_t v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_153_ = 6;
v___x_154_ = lean_uint32_shift_right(v_c_149_, v___x_153_);
v___x_155_ = lean_uint32_to_uint8(v___x_154_);
v___x_156_ = 63;
v___x_157_ = lean_uint8_land(v___x_155_, v___x_156_);
v___x_158_ = 128;
v___x_159_ = lean_box_uint32(v_c_149_);
v___x_160_ = lean_box(v___x_156_);
v___x_161_ = lean_box(v___x_158_);
lean_inc(v_f_150_);
v___f_162_ = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_162_, 0, v___x_159_);
lean_closure_set(v___f_162_, 1, v___x_160_);
lean_closure_set(v___f_162_, 2, v___x_161_);
lean_closure_set(v___f_162_, 3, v_f_150_);
v___x_163_ = lean_uint8_lor(v___x_157_, v___x_158_);
v___x_164_ = lean_box(v___x_163_);
v___x_165_ = lean_apply_2(v_f_150_, v_s_152_, v___x_164_);
v___x_166_ = lean_apply_4(v_toBind_151_, lean_box(0), lean_box(0), v___x_165_, v___f_162_);
return v___x_166_;
}
}
LEAN_EXPORT void l_Lake_foldlUtf8M___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_149_ = stack[0].m_num;
lean_object* v_f_150_ = stack[1].m_obj;
lean_object* v_toBind_151_ = stack[2].m_obj;
lean_object* v_s_152_ = stack[3].m_obj;
lean_object* v_res_167_;
v_res_167_ = l_Lake_foldlUtf8M___redArg___lam__4(v_c_149_, v_f_150_, v_toBind_151_, v_s_152_);
stack->m_obj
 = v_res_167_;
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__4___boxed(lean_object* v_c_168_, lean_object* v_f_169_, lean_object* v_toBind_170_, lean_object* v_s_171_){
_start:
{
uint32_t v_c_boxed_172_; lean_object* v_res_173_; 
v_c_boxed_172_ = lean_unbox_uint32(v_c_168_);
lean_dec(v_c_168_);
v_res_173_ = l_Lake_foldlUtf8M___redArg___lam__4(v_c_boxed_172_, v_f_169_, v_toBind_170_, v_s_171_);
return v_res_173_;
}
}
lean_object* l_Lake_foldlUtf8M___redArg___lam__3(uint32_t v_c_174_, lean_object* v_f_175_, lean_object* v_s_176_){
_start:
{
uint8_t v___x_177_; uint8_t v___x_178_; uint8_t v___x_179_; uint8_t v___x_180_; uint8_t v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_177_ = lean_uint32_to_uint8(v_c_174_);
v___x_178_ = 63;
v___x_179_ = lean_uint8_land(v___x_177_, v___x_178_);
v___x_180_ = 128;
v___x_181_ = lean_uint8_lor(v___x_179_, v___x_180_);
v___x_182_ = lean_box(v___x_181_);
v___x_183_ = lean_apply_2(v_f_175_, v_s_176_, v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT void l_Lake_foldlUtf8M___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_174_ = stack[0].m_num;
lean_object* v_f_175_ = stack[1].m_obj;
lean_object* v_s_176_ = stack[2].m_obj;
lean_object* v_res_184_;
v_res_184_ = l_Lake_foldlUtf8M___redArg___lam__3(v_c_174_, v_f_175_, v_s_176_);
stack->m_obj
 = v_res_184_;
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__3___boxed(lean_object* v_c_185_, lean_object* v_f_186_, lean_object* v_s_187_){
_start:
{
uint32_t v_c_boxed_188_; lean_object* v_res_189_; 
v_c_boxed_188_ = lean_unbox_uint32(v_c_185_);
lean_dec(v_c_185_);
v_res_189_ = l_Lake_foldlUtf8M___redArg___lam__3(v_c_boxed_188_, v_f_186_, v_s_187_);
return v_res_189_;
}
}
lean_object* l_Lake_foldlUtf8M___redArg(lean_object* v_inst_190_, uint32_t v_c_191_, lean_object* v_f_192_, lean_object* v_init_193_){
_start:
{
lean_object* v_toBind_194_; uint32_t v___x_195_; uint8_t v___x_196_; 
v_toBind_194_ = lean_ctor_get(v_inst_190_, 1);
lean_inc(v_toBind_194_);
lean_dec_ref(v_inst_190_);
v___x_195_ = 127;
v___x_196_ = lean_uint32_dec_le(v_c_191_, v___x_195_);
if (v___x_196_ == 0)
{
uint32_t v___x_197_; uint8_t v___x_198_; 
v___x_197_ = 2047;
v___x_198_ = lean_uint32_dec_le(v_c_191_, v___x_197_);
if (v___x_198_ == 0)
{
uint32_t v___x_199_; uint8_t v___x_200_; 
v___x_199_ = 65535;
v___x_200_ = lean_uint32_dec_le(v_c_191_, v___x_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; lean_object* v___f_202_; uint32_t v___x_203_; uint32_t v___x_204_; uint8_t v___x_205_; uint8_t v___x_206_; uint8_t v___x_207_; uint8_t v___x_208_; uint8_t v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_201_ = lean_box_uint32(v_c_191_);
lean_inc(v_toBind_194_);
lean_inc(v_f_192_);
v___f_202_ = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_202_, 0, v___x_201_);
lean_closure_set(v___f_202_, 1, v_f_192_);
lean_closure_set(v___f_202_, 2, v_toBind_194_);
v___x_203_ = 18;
v___x_204_ = lean_uint32_shift_right(v_c_191_, v___x_203_);
v___x_205_ = lean_uint32_to_uint8(v___x_204_);
v___x_206_ = 7;
v___x_207_ = lean_uint8_land(v___x_205_, v___x_206_);
v___x_208_ = 240;
v___x_209_ = lean_uint8_lor(v___x_207_, v___x_208_);
v___x_210_ = lean_box(v___x_209_);
v___x_211_ = lean_apply_2(v_f_192_, v_init_193_, v___x_210_);
v___x_212_ = lean_apply_4(v_toBind_194_, lean_box(0), lean_box(0), v___x_211_, v___f_202_);
return v___x_212_;
}
else
{
lean_object* v___x_213_; lean_object* v___f_214_; uint32_t v___x_215_; uint32_t v___x_216_; uint8_t v___x_217_; uint8_t v___x_218_; uint8_t v___x_219_; uint8_t v___x_220_; uint8_t v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_213_ = lean_box_uint32(v_c_191_);
lean_inc(v_toBind_194_);
lean_inc(v_f_192_);
v___f_214_ = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_214_, 0, v___x_213_);
lean_closure_set(v___f_214_, 1, v_f_192_);
lean_closure_set(v___f_214_, 2, v_toBind_194_);
v___x_215_ = 12;
v___x_216_ = lean_uint32_shift_right(v_c_191_, v___x_215_);
v___x_217_ = lean_uint32_to_uint8(v___x_216_);
v___x_218_ = 15;
v___x_219_ = lean_uint8_land(v___x_217_, v___x_218_);
v___x_220_ = 224;
v___x_221_ = lean_uint8_lor(v___x_219_, v___x_220_);
v___x_222_ = lean_box(v___x_221_);
v___x_223_ = lean_apply_2(v_f_192_, v_init_193_, v___x_222_);
v___x_224_ = lean_apply_4(v_toBind_194_, lean_box(0), lean_box(0), v___x_223_, v___f_214_);
return v___x_224_;
}
}
else
{
lean_object* v___x_225_; lean_object* v___f_226_; uint32_t v___x_227_; uint32_t v___x_228_; uint8_t v___x_229_; uint8_t v___x_230_; uint8_t v___x_231_; uint8_t v___x_232_; uint8_t v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_225_ = lean_box_uint32(v_c_191_);
lean_inc(v_f_192_);
v___f_226_ = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_226_, 0, v___x_225_);
lean_closure_set(v___f_226_, 1, v_f_192_);
v___x_227_ = 6;
v___x_228_ = lean_uint32_shift_right(v_c_191_, v___x_227_);
v___x_229_ = lean_uint32_to_uint8(v___x_228_);
v___x_230_ = 31;
v___x_231_ = lean_uint8_land(v___x_229_, v___x_230_);
v___x_232_ = 192;
v___x_233_ = lean_uint8_lor(v___x_231_, v___x_232_);
v___x_234_ = lean_box(v___x_233_);
v___x_235_ = lean_apply_2(v_f_192_, v_init_193_, v___x_234_);
v___x_236_ = lean_apply_4(v_toBind_194_, lean_box(0), lean_box(0), v___x_235_, v___f_226_);
return v___x_236_;
}
}
else
{
uint8_t v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
lean_dec(v_toBind_194_);
v___x_237_ = lean_uint32_to_uint8(v_c_191_);
v___x_238_ = lean_box(v___x_237_);
v___x_239_ = lean_apply_2(v_f_192_, v_init_193_, v___x_238_);
return v___x_239_;
}
}
}
LEAN_EXPORT void l_Lake_foldlUtf8M___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_190_ = stack[0].m_obj;
uint32_t v_c_191_ = stack[1].m_num;
lean_object* v_f_192_ = stack[2].m_obj;
lean_object* v_init_193_ = stack[3].m_obj;
lean_object* v_res_240_;
v_res_240_ = l_Lake_foldlUtf8M___redArg(v_inst_190_, v_c_191_, v_f_192_, v_init_193_);
stack->m_obj
 = v_res_240_;
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___boxed(lean_object* v_inst_241_, lean_object* v_c_242_, lean_object* v_f_243_, lean_object* v_init_244_){
_start:
{
uint32_t v_c_boxed_245_; lean_object* v_res_246_; 
v_c_boxed_245_ = lean_unbox_uint32(v_c_242_);
lean_dec(v_c_242_);
v_res_246_ = l_Lake_foldlUtf8M___redArg(v_inst_241_, v_c_boxed_245_, v_f_243_, v_init_244_);
return v_res_246_;
}
}
lean_object* l_Lake_foldlUtf8M(lean_object* v_m_247_, lean_object* v_00_u03c3_248_, lean_object* v_inst_249_, uint32_t v_c_250_, lean_object* v_f_251_, lean_object* v_init_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_Lake_foldlUtf8M___redArg(v_inst_249_, v_c_250_, v_f_251_, v_init_252_);
return v___x_253_;
}
}
LEAN_EXPORT void l_Lake_foldlUtf8M_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_249_ = stack[2].m_obj;
uint32_t v_c_250_ = stack[3].m_num;
lean_object* v_f_251_ = stack[4].m_obj;
lean_object* v_init_252_ = stack[5].m_obj;
lean_object* v_res_254_;
v_res_254_ = l_Lake_foldlUtf8M(lean_box(0), lean_box(0), v_inst_249_, v_c_250_, v_f_251_, v_init_252_);
stack->m_obj
 = v_res_254_;
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___boxed(lean_object* v_m_255_, lean_object* v_00_u03c3_256_, lean_object* v_inst_257_, lean_object* v_c_258_, lean_object* v_f_259_, lean_object* v_init_260_){
_start:
{
uint32_t v_c_boxed_261_; lean_object* v_res_262_; 
v_c_boxed_261_ = lean_unbox_uint32(v_c_258_);
lean_dec(v_c_258_);
v_res_262_ = l_Lake_foldlUtf8M(v_m_255_, v_00_u03c3_256_, v_inst_257_, v_c_boxed_261_, v_f_259_, v_init_260_);
return v_res_262_;
}
}
lean_object* l_Lake_foldlUtf8___redArg___lam__0(lean_object* v_f_263_, lean_object* v_x1_264_, uint8_t v_x2_265_){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = lean_box(v_x2_265_);
v___x_267_ = lean_apply_2(v_f_263_, v_x1_264_, v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT void l_Lake_foldlUtf8___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_263_ = stack[0].m_obj;
lean_object* v_x1_264_ = stack[1].m_obj;
uint8_t v_x2_265_ = stack[2].m_num;
lean_object* v_res_268_;
v_res_268_ = l_Lake_foldlUtf8___redArg___lam__0(v_f_263_, v_x1_264_, v_x2_265_);
stack->m_obj
 = v_res_268_;
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___redArg___lam__0___boxed(lean_object* v_f_269_, lean_object* v_x1_270_, lean_object* v_x2_271_){
_start:
{
uint8_t v_x2_84__boxed_272_; lean_object* v_res_273_; 
v_x2_84__boxed_272_ = lean_unbox(v_x2_271_);
v_res_273_ = l_Lake_foldlUtf8___redArg___lam__0(v_f_269_, v_x1_270_, v_x2_84__boxed_272_);
return v_res_273_;
}
}
lean_object* l_Lake_foldlUtf8___redArg(uint32_t v_c_293_, lean_object* v_f_294_, lean_object* v_init_295_){
_start:
{
lean_object* v___f_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___f_296_ = lean_alloc_closure((void*)(l_Lake_foldlUtf8___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_296_, 0, v_f_294_);
v___x_297_ = ((lean_object*)(l_Lake_foldlUtf8___redArg___closed__9));
v___x_298_ = l_Lake_foldlUtf8M___redArg(v___x_297_, v_c_293_, v___f_296_, v_init_295_);
return v___x_298_;
}
}
LEAN_EXPORT void l_Lake_foldlUtf8___redArg_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_293_ = stack[0].m_num;
lean_object* v_f_294_ = stack[1].m_obj;
lean_object* v_init_295_ = stack[2].m_obj;
lean_object* v_res_299_;
v_res_299_ = l_Lake_foldlUtf8___redArg(v_c_293_, v_f_294_, v_init_295_);
stack->m_obj
 = v_res_299_;
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___redArg___boxed(lean_object* v_c_300_, lean_object* v_f_301_, lean_object* v_init_302_){
_start:
{
uint32_t v_c_boxed_303_; lean_object* v_res_304_; 
v_c_boxed_303_ = lean_unbox_uint32(v_c_300_);
lean_dec(v_c_300_);
v_res_304_ = l_Lake_foldlUtf8___redArg(v_c_boxed_303_, v_f_301_, v_init_302_);
return v_res_304_;
}
}
lean_object* l_Lake_foldlUtf8(lean_object* v_00_u03c3_305_, uint32_t v_c_306_, lean_object* v_f_307_, lean_object* v_init_308_){
_start:
{
lean_object* v___f_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___f_309_ = lean_alloc_closure((void*)(l_Lake_foldlUtf8___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_309_, 0, v_f_307_);
v___x_310_ = ((lean_object*)(l_Lake_foldlUtf8___redArg___closed__9));
v___x_311_ = l_Lake_foldlUtf8M___redArg(v___x_310_, v_c_306_, v___f_309_, v_init_308_);
return v___x_311_;
}
}
LEAN_EXPORT void l_Lake_foldlUtf8_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_306_ = stack[1].m_num;
lean_object* v_f_307_ = stack[2].m_obj;
lean_object* v_init_308_ = stack[3].m_obj;
lean_object* v_res_312_;
v_res_312_ = l_Lake_foldlUtf8(lean_box(0), v_c_306_, v_f_307_, v_init_308_);
stack->m_obj
 = v_res_312_;
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___boxed(lean_object* v_00_u03c3_313_, lean_object* v_c_314_, lean_object* v_f_315_, lean_object* v_init_316_){
_start:
{
uint32_t v_c_boxed_317_; lean_object* v_res_318_; 
v_c_boxed_317_ = lean_unbox_uint32(v_c_314_);
lean_dec(v_c_314_);
v_res_318_ = l_Lake_foldlUtf8(v_00_u03c3_313_, v_c_boxed_317_, v_f_315_, v_init_316_);
return v_res_318_;
}
}
lean_object* l_Lake_foldlUtf8M___at___00Lake_uriEscapeChar_spec__0(uint32_t v_c_319_, lean_object* v_init_320_){
_start:
{
uint32_t v___x_321_; uint8_t v___x_322_; 
v___x_321_ = 127;
v___x_322_ = lean_uint32_dec_le(v_c_319_, v___x_321_);
if (v___x_322_ == 0)
{
uint32_t v___x_323_; uint8_t v___x_324_; 
v___x_323_ = 2047;
v___x_324_ = lean_uint32_dec_le(v_c_319_, v___x_323_);
if (v___x_324_ == 0)
{
uint32_t v___x_325_; uint8_t v___x_326_; 
v___x_325_ = 65535;
v___x_326_ = lean_uint32_dec_le(v_c_319_, v___x_325_);
if (v___x_326_ == 0)
{
uint32_t v___x_327_; uint32_t v___x_328_; uint8_t v___x_329_; uint8_t v___x_330_; uint8_t v___x_331_; uint8_t v___x_332_; uint8_t v___x_333_; lean_object* v___x_334_; uint32_t v___x_335_; uint32_t v___x_336_; uint8_t v___x_337_; uint8_t v___x_338_; uint8_t v___x_339_; uint8_t v___x_340_; uint8_t v___x_341_; lean_object* v___x_342_; uint32_t v___x_343_; uint32_t v___x_344_; uint8_t v___x_345_; uint8_t v___x_346_; uint8_t v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; uint8_t v___x_350_; uint8_t v___x_351_; lean_object* v___x_352_; 
v___x_327_ = 18;
v___x_328_ = lean_uint32_shift_right(v_c_319_, v___x_327_);
v___x_329_ = lean_uint32_to_uint8(v___x_328_);
v___x_330_ = 7;
v___x_331_ = lean_uint8_land(v___x_329_, v___x_330_);
v___x_332_ = 240;
v___x_333_ = lean_uint8_lor(v___x_331_, v___x_332_);
v___x_334_ = l_Lake_uriEscapeByte(v___x_333_, v_init_320_);
v___x_335_ = 12;
v___x_336_ = lean_uint32_shift_right(v_c_319_, v___x_335_);
v___x_337_ = lean_uint32_to_uint8(v___x_336_);
v___x_338_ = 63;
v___x_339_ = lean_uint8_land(v___x_337_, v___x_338_);
v___x_340_ = 128;
v___x_341_ = lean_uint8_lor(v___x_339_, v___x_340_);
v___x_342_ = l_Lake_uriEscapeByte(v___x_341_, v___x_334_);
v___x_343_ = 6;
v___x_344_ = lean_uint32_shift_right(v_c_319_, v___x_343_);
v___x_345_ = lean_uint32_to_uint8(v___x_344_);
v___x_346_ = lean_uint8_land(v___x_345_, v___x_338_);
v___x_347_ = lean_uint8_lor(v___x_346_, v___x_340_);
v___x_348_ = l_Lake_uriEscapeByte(v___x_347_, v___x_342_);
v___x_349_ = lean_uint32_to_uint8(v_c_319_);
v___x_350_ = lean_uint8_land(v___x_349_, v___x_338_);
v___x_351_ = lean_uint8_lor(v___x_350_, v___x_340_);
v___x_352_ = l_Lake_uriEscapeByte(v___x_351_, v___x_348_);
return v___x_352_;
}
else
{
uint32_t v___x_353_; uint32_t v___x_354_; uint8_t v___x_355_; uint8_t v___x_356_; uint8_t v___x_357_; uint8_t v___x_358_; uint8_t v___x_359_; lean_object* v___x_360_; uint32_t v___x_361_; uint32_t v___x_362_; uint8_t v___x_363_; uint8_t v___x_364_; uint8_t v___x_365_; uint8_t v___x_366_; uint8_t v___x_367_; lean_object* v___x_368_; uint8_t v___x_369_; uint8_t v___x_370_; uint8_t v___x_371_; lean_object* v___x_372_; 
v___x_353_ = 12;
v___x_354_ = lean_uint32_shift_right(v_c_319_, v___x_353_);
v___x_355_ = lean_uint32_to_uint8(v___x_354_);
v___x_356_ = 15;
v___x_357_ = lean_uint8_land(v___x_355_, v___x_356_);
v___x_358_ = 224;
v___x_359_ = lean_uint8_lor(v___x_357_, v___x_358_);
v___x_360_ = l_Lake_uriEscapeByte(v___x_359_, v_init_320_);
v___x_361_ = 6;
v___x_362_ = lean_uint32_shift_right(v_c_319_, v___x_361_);
v___x_363_ = lean_uint32_to_uint8(v___x_362_);
v___x_364_ = 63;
v___x_365_ = lean_uint8_land(v___x_363_, v___x_364_);
v___x_366_ = 128;
v___x_367_ = lean_uint8_lor(v___x_365_, v___x_366_);
v___x_368_ = l_Lake_uriEscapeByte(v___x_367_, v___x_360_);
v___x_369_ = lean_uint32_to_uint8(v_c_319_);
v___x_370_ = lean_uint8_land(v___x_369_, v___x_364_);
v___x_371_ = lean_uint8_lor(v___x_370_, v___x_366_);
v___x_372_ = l_Lake_uriEscapeByte(v___x_371_, v___x_368_);
return v___x_372_;
}
}
else
{
uint32_t v___x_373_; uint32_t v___x_374_; uint8_t v___x_375_; uint8_t v___x_376_; uint8_t v___x_377_; uint8_t v___x_378_; uint8_t v___x_379_; lean_object* v___x_380_; uint8_t v___x_381_; uint8_t v___x_382_; uint8_t v___x_383_; uint8_t v___x_384_; uint8_t v___x_385_; lean_object* v___x_386_; 
v___x_373_ = 6;
v___x_374_ = lean_uint32_shift_right(v_c_319_, v___x_373_);
v___x_375_ = lean_uint32_to_uint8(v___x_374_);
v___x_376_ = 31;
v___x_377_ = lean_uint8_land(v___x_375_, v___x_376_);
v___x_378_ = 192;
v___x_379_ = lean_uint8_lor(v___x_377_, v___x_378_);
v___x_380_ = l_Lake_uriEscapeByte(v___x_379_, v_init_320_);
v___x_381_ = lean_uint32_to_uint8(v_c_319_);
v___x_382_ = 63;
v___x_383_ = lean_uint8_land(v___x_381_, v___x_382_);
v___x_384_ = 128;
v___x_385_ = lean_uint8_lor(v___x_383_, v___x_384_);
v___x_386_ = l_Lake_uriEscapeByte(v___x_385_, v___x_380_);
return v___x_386_;
}
}
else
{
uint8_t v___x_387_; lean_object* v___x_388_; 
v___x_387_ = lean_uint32_to_uint8(v_c_319_);
v___x_388_ = l_Lake_uriEscapeByte(v___x_387_, v_init_320_);
return v___x_388_;
}
}
}
LEAN_EXPORT void l_Lake_foldlUtf8M___at___00Lake_uriEscapeChar_spec__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_319_ = stack[0].m_num;
lean_object* v_init_320_ = stack[1].m_obj;
lean_object* v_res_389_;
v_res_389_ = l_Lake_foldlUtf8M___at___00Lake_uriEscapeChar_spec__0(v_c_319_, v_init_320_);
stack->m_obj
 = v_res_389_;
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___at___00Lake_uriEscapeChar_spec__0___boxed(lean_object* v_c_390_, lean_object* v_init_391_){
_start:
{
uint32_t v_c_boxed_392_; lean_object* v_res_393_; 
v_c_boxed_392_ = lean_unbox_uint32(v_c_390_);
lean_dec(v_c_390_);
v_res_393_ = l_Lake_foldlUtf8M___at___00Lake_uriEscapeChar_spec__0(v_c_boxed_392_, v_init_391_);
return v_res_393_;
}
}
lean_object* l_Lake_uriEscapeChar(uint32_t v_c_394_, lean_object* v_s_395_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l_Lake_foldlUtf8M___at___00Lake_uriEscapeChar_spec__0(v_c_394_, v_s_395_);
return v___x_396_;
}
}
LEAN_EXPORT void l_Lake_uriEscapeChar_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_394_ = stack[0].m_num;
lean_object* v_s_395_ = stack[1].m_obj;
lean_object* v_res_397_;
v_res_397_ = l_Lake_uriEscapeChar(v_c_394_, v_s_395_);
stack->m_obj
 = v_res_397_;
}
LEAN_EXPORT lean_object* l_Lake_uriEscapeChar___boxed(lean_object* v_c_398_, lean_object* v_s_399_){
_start:
{
uint32_t v_c_boxed_400_; lean_object* v_res_401_; 
v_c_boxed_400_ = lean_unbox_uint32(v_c_398_);
lean_dec(v_c_398_);
v_res_401_ = l_Lake_uriEscapeChar(v_c_boxed_400_, v_s_399_);
return v_res_401_;
}
}
uint8_t l_Lake_isUriUnreservedMark(uint32_t v_c_402_){
_start:
{
uint32_t v___x_403_; uint8_t v___x_404_; 
v___x_403_ = 45;
v___x_404_ = lean_uint32_dec_eq(v_c_402_, v___x_403_);
if (v___x_404_ == 0)
{
uint32_t v___x_405_; uint8_t v___x_406_; 
v___x_405_ = 95;
v___x_406_ = lean_uint32_dec_eq(v_c_402_, v___x_405_);
if (v___x_406_ == 0)
{
uint32_t v___x_407_; uint8_t v___x_408_; 
v___x_407_ = 46;
v___x_408_ = lean_uint32_dec_eq(v_c_402_, v___x_407_);
if (v___x_408_ == 0)
{
uint32_t v___x_409_; uint8_t v___x_410_; 
v___x_409_ = 126;
v___x_410_ = lean_uint32_dec_eq(v_c_402_, v___x_409_);
return v___x_410_;
}
else
{
return v___x_408_;
}
}
else
{
return v___x_406_;
}
}
else
{
return v___x_404_;
}
}
}
LEAN_EXPORT void l_Lake_isUriUnreservedMark_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_402_ = stack[0].m_num;
uint8_t v_res_411_;
v_res_411_ = l_Lake_isUriUnreservedMark(v_c_402_);
stack->m_num = v_res_411_;
}
LEAN_EXPORT lean_object* l_Lake_isUriUnreservedMark___boxed(lean_object* v_c_412_){
_start:
{
uint32_t v_c_boxed_413_; uint8_t v_res_414_; lean_object* v_r_415_; 
v_c_boxed_413_ = lean_unbox_uint32(v_c_412_);
lean_dec(v_c_412_);
v_res_414_ = l_Lake_isUriUnreservedMark(v_c_boxed_413_);
v_r_415_ = lean_box(v_res_414_);
return v_r_415_;
}
}
lean_object* l_Lake_uriEncodeChar(uint32_t v_c_416_, lean_object* v_s_417_){
_start:
{
uint32_t v___x_434_; uint8_t v___x_435_; 
v___x_434_ = 65;
v___x_435_ = lean_uint32_dec_le(v___x_434_, v_c_416_);
if (v___x_435_ == 0)
{
goto v___jp_428_;
}
else
{
uint32_t v___x_436_; uint8_t v___x_437_; 
v___x_436_ = 90;
v___x_437_ = lean_uint32_dec_le(v_c_416_, v___x_436_);
if (v___x_437_ == 0)
{
goto v___jp_428_;
}
else
{
lean_object* v___x_438_; 
v___x_438_ = lean_string_push(v_s_417_, v_c_416_);
return v___x_438_;
}
}
v___jp_418_:
{
uint8_t v___x_419_; 
v___x_419_ = l_Lake_isUriUnreservedMark(v_c_416_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; 
v___x_420_ = l_Lake_foldlUtf8M___at___00Lake_uriEscapeChar_spec__0(v_c_416_, v_s_417_);
return v___x_420_;
}
else
{
lean_object* v___x_421_; 
v___x_421_ = lean_string_push(v_s_417_, v_c_416_);
return v___x_421_;
}
}
v___jp_422_:
{
uint32_t v___x_423_; uint8_t v___x_424_; 
v___x_423_ = 48;
v___x_424_ = lean_uint32_dec_le(v___x_423_, v_c_416_);
if (v___x_424_ == 0)
{
goto v___jp_418_;
}
else
{
uint32_t v___x_425_; uint8_t v___x_426_; 
v___x_425_ = 57;
v___x_426_ = lean_uint32_dec_le(v_c_416_, v___x_425_);
if (v___x_426_ == 0)
{
goto v___jp_418_;
}
else
{
lean_object* v___x_427_; 
v___x_427_ = lean_string_push(v_s_417_, v_c_416_);
return v___x_427_;
}
}
}
v___jp_428_:
{
uint32_t v___x_429_; uint8_t v___x_430_; 
v___x_429_ = 97;
v___x_430_ = lean_uint32_dec_le(v___x_429_, v_c_416_);
if (v___x_430_ == 0)
{
goto v___jp_422_;
}
else
{
uint32_t v___x_431_; uint8_t v___x_432_; 
v___x_431_ = 122;
v___x_432_ = lean_uint32_dec_le(v_c_416_, v___x_431_);
if (v___x_432_ == 0)
{
goto v___jp_422_;
}
else
{
lean_object* v___x_433_; 
v___x_433_ = lean_string_push(v_s_417_, v_c_416_);
return v___x_433_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_uriEncodeChar_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_416_ = stack[0].m_num;
lean_object* v_s_417_ = stack[1].m_obj;
lean_object* v_res_439_;
v_res_439_ = l_Lake_uriEncodeChar(v_c_416_, v_s_417_);
stack->m_obj
 = v_res_439_;
}
LEAN_EXPORT lean_object* l_Lake_uriEncodeChar___boxed(lean_object* v_c_440_, lean_object* v_s_441_){
_start:
{
uint32_t v_c_boxed_442_; lean_object* v_res_443_; 
v_c_boxed_442_ = lean_unbox_uint32(v_c_440_);
lean_dec(v_c_440_);
v_res_443_ = l_Lake_uriEncodeChar(v_c_boxed_442_, v_s_441_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___redArg(lean_object* v___x_444_, lean_object* v_s_445_, lean_object* v_a_446_, lean_object* v_b_447_){
_start:
{
uint8_t v_decide_448_; 
v_decide_448_ = lean_nat_dec_eq(v_a_446_, v___x_444_);
if (v_decide_448_ == 0)
{
uint32_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_449_ = lean_string_utf8_get_fast(v_s_445_, v_a_446_);
v___x_450_ = lean_string_utf8_next_fast(v_s_445_, v_a_446_);
lean_dec(v_a_446_);
v___x_451_ = l_Lake_uriEncodeChar(v___x_449_, v_b_447_);
v_a_446_ = v___x_450_;
v_b_447_ = v___x_451_;
goto _start;
}
else
{
lean_dec(v_a_446_);
return v_b_447_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___redArg___boxed(lean_object* v___x_453_, lean_object* v_s_454_, lean_object* v_a_455_, lean_object* v_b_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___redArg(v___x_453_, v_s_454_, v_a_455_, v_b_456_);
lean_dec_ref(v_s_454_);
lean_dec(v___x_453_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Lake_uriEncode(lean_object* v_s_458_, lean_object* v_init_459_){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_460_ = lean_string_utf8_byte_size(v_s_458_);
v___x_461_ = lean_unsigned_to_nat(0u);
v___x_462_ = l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___redArg(v___x_460_, v_s_458_, v___x_461_, v_init_459_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lake_uriEncode___boxed(lean_object* v_s_463_, lean_object* v_init_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lake_uriEncode(v_s_463_, v_init_464_);
lean_dec_ref(v_s_463_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0(lean_object* v___x_466_, lean_object* v___x_467_, lean_object* v_s_468_, lean_object* v_inst_469_, lean_object* v_R_470_, lean_object* v_a_471_, lean_object* v_b_472_, lean_object* v_c_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___redArg(v___x_467_, v_s_468_, v_a_471_, v_b_472_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___boxed(lean_object* v___x_475_, lean_object* v___x_476_, lean_object* v_s_477_, lean_object* v_inst_478_, lean_object* v_R_479_, lean_object* v_a_480_, lean_object* v_b_481_, lean_object* v_c_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0(v___x_475_, v___x_476_, v_s_477_, v_inst_478_, v_R_479_, v_a_480_, v_b_481_, v_c_482_);
lean_dec_ref(v_s_477_);
lean_dec(v___x_476_);
lean_dec_ref(v___x_475_);
return v_res_483_;
}
}
lean_object* l_Lake_Internal_getCurl(){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = ((lean_object*)(l_Lake_Internal_getCurl___closed__0));
v___x_488_ = lean_io_getenv(v___x_487_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v___x_489_; 
v___x_489_ = ((lean_object*)(l_Lake_Internal_getCurl___closed__1));
return v___x_489_;
}
else
{
lean_object* v_val_490_; 
v_val_490_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_val_490_);
lean_dec_ref_known(v___x_488_, 1);
return v_val_490_;
}
}
}
LEAN_EXPORT void l_Lake_Internal_getCurl_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_491_;
v_res_491_ = l_Lake_Internal_getCurl();
stack->m_obj
 = v_res_491_;
}
LEAN_EXPORT lean_object* l_Lake_Internal_getCurl___boxed(lean_object* v_a_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lake_Internal_getCurl();
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0(lean_object* v_x_496_){
_start:
{
if (lean_obj_tag(v_x_496_) == 0)
{
lean_object* v___x_497_; 
v___x_497_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0___closed__0));
return v___x_497_;
}
else
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_Json_getNat_x3f(v_x_496_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v___x_498_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_498_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
else
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_515_; 
v_a_507_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_515_ == 0)
{
v___x_509_ = v___x_498_;
v_isShared_510_ = v_isSharedCheck_515_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_498_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_515_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_511_, 0, v_a_507_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 0, v___x_511_);
v___x_513_ = v___x_509_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__1(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_517_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__0));
v___x_518_ = lean_unsigned_to_nat(2u);
v___x_519_ = lean_mk_empty_array_with_capacity(v___x_518_);
v___x_520_ = lean_array_push(v___x_519_, v___x_517_);
return v___x_520_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1(lean_object* v_as_521_, size_t v_i_522_, size_t v_stop_523_, lean_object* v_b_524_){
_start:
{
uint8_t v___x_525_; 
v___x_525_ = lean_usize_dec_eq(v_i_522_, v_stop_523_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; size_t v___x_530_; size_t v___x_531_; 
v___x_526_ = lean_array_uget_borrowed(v_as_521_, v_i_522_);
v___x_527_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__1);
lean_inc(v___x_526_);
v___x_528_ = lean_array_push(v___x_527_, v___x_526_);
v___x_529_ = l_Array_append___redArg(v_b_524_, v___x_528_);
lean_dec_ref(v___x_528_);
v___x_530_ = ((size_t)1ULL);
v___x_531_ = lean_usize_add(v_i_522_, v___x_530_);
v_i_522_ = v___x_531_;
v_b_524_ = v___x_529_;
goto _start;
}
else
{
return v_b_524_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_521_ = stack[0].m_obj;
size_t v_i_522_ = stack[1].m_num;
size_t v_stop_523_ = stack[2].m_num;
lean_object* v_b_524_ = stack[3].m_obj;
lean_object* v_res_533_;
v_res_533_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1(v_as_521_, v_i_522_, v_stop_523_, v_b_524_);
stack->m_obj
 = v_res_533_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___boxed(lean_object* v_as_534_, lean_object* v_i_535_, lean_object* v_stop_536_, lean_object* v_b_537_){
_start:
{
size_t v_i_boxed_538_; size_t v_stop_boxed_539_; lean_object* v_res_540_; 
v_i_boxed_538_ = lean_unbox_usize(v_i_535_);
lean_dec(v_i_535_);
v_stop_boxed_539_ = lean_unbox_usize(v_stop_536_);
lean_dec(v_stop_536_);
v_res_540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1(v_as_534_, v_i_boxed_538_, v_stop_boxed_539_, v_b_537_);
lean_dec_ref(v_as_534_);
return v_res_540_;
}
}
lean_object* l_Lake_getUrl_x3f(lean_object* v_url_576_, lean_object* v_headers_577_, lean_object* v_a_578_){
_start:
{
lean_object* v___y_581_; lean_object* v_a_582_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v_a_587_; lean_object* v___y_594_; lean_object* v___y_595_; lean_object* v___y_599_; lean_object* v___y_600_; lean_object* v_a_601_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v_a_612_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v_val_664_; lean_object* v___y_690_; lean_object* v_args_696_; lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v_args_696_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__17));
v___x_697_ = lean_unsigned_to_nat(0u);
v___x_698_ = lean_array_get_size(v_headers_577_);
v___x_699_ = lean_nat_dec_lt(v___x_697_, v___x_698_);
if (v___x_699_ == 0)
{
v___y_690_ = v_args_696_;
goto v___jp_689_;
}
else
{
uint8_t v___x_700_; 
v___x_700_ = lean_nat_dec_le(v___x_698_, v___x_698_);
if (v___x_700_ == 0)
{
if (v___x_699_ == 0)
{
v___y_690_ = v_args_696_;
goto v___jp_689_;
}
else
{
size_t v___x_701_; size_t v___x_702_; lean_object* v___x_703_; 
v___x_701_ = ((size_t)0ULL);
v___x_702_ = lean_usize_of_nat(v___x_698_);
v___x_703_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1(v_headers_577_, v___x_701_, v___x_702_, v_args_696_);
v___y_690_ = v___x_703_;
goto v___jp_689_;
}
}
else
{
size_t v___x_704_; size_t v___x_705_; lean_object* v___x_706_; 
v___x_704_ = ((size_t)0ULL);
v___x_705_ = lean_usize_of_nat(v___x_698_);
v___x_706_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1(v_headers_577_, v___x_704_, v___x_705_, v_args_696_);
v___y_690_ = v___x_706_;
goto v___jp_689_;
}
}
v___jp_580_:
{
lean_object* v___x_583_; 
v___x_583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_583_, 0, v___y_581_);
lean_ctor_set(v___x_583_, 1, v_a_582_);
return v___x_583_;
}
v___jp_584_:
{
lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_588_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__0));
v___x_589_ = lean_string_append(v___x_588_, v_a_587_);
lean_dec_ref(v_a_587_);
v___x_590_ = 3;
v___x_591_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_591_, 0, v___x_589_);
lean_ctor_set_uint8(v___x_591_, sizeof(void*)*1, v___x_590_);
v___x_592_ = lean_array_push(v___y_586_, v___x_591_);
v___y_581_ = v___y_585_;
v_a_582_ = v___x_592_;
goto v___jp_580_;
}
v___jp_593_:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__2));
v___x_597_ = lean_array_push(v___y_595_, v___x_596_);
v___y_581_ = v___y_594_;
v_a_582_ = v___x_597_;
goto v___jp_580_;
}
v___jp_598_:
{
lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_602_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__3));
v___x_603_ = lean_string_append(v___x_602_, v_a_601_);
lean_dec_ref(v_a_601_);
v___x_604_ = 3;
v___x_605_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_605_, 0, v___x_603_);
lean_ctor_set_uint8(v___x_605_, sizeof(void*)*1, v___x_604_);
v___x_606_ = lean_array_push(v___y_600_, v___x_605_);
v___y_581_ = v___y_599_;
v_a_582_ = v___x_606_;
goto v___jp_580_;
}
v___jp_607_:
{
if (lean_obj_tag(v_a_612_) == 0)
{
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
v___y_594_ = v___y_611_;
v___y_595_ = v___y_610_;
goto v___jp_593_;
}
else
{
lean_object* v_val_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_645_; 
v_val_613_ = lean_ctor_get(v_a_612_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v_a_612_);
if (v_isSharedCheck_645_ == 0)
{
v___x_615_ = v_a_612_;
v_isShared_616_ = v_isSharedCheck_645_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_val_613_);
lean_dec(v_a_612_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_645_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_617_ = lean_unsigned_to_nat(200u);
v___x_618_ = lean_nat_dec_eq(v_val_613_, v___x_617_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; uint8_t v___x_620_; 
lean_del_object(v___x_615_);
lean_dec(v___y_608_);
v___x_619_ = lean_unsigned_to_nat(404u);
v___x_620_ = lean_nat_dec_eq(v_val_613_, v___x_619_);
if (v___x_620_ == 0)
{
lean_object* v_stdout_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; uint8_t v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v_stdout_621_ = lean_ctor_get(v___y_609_, 0);
lean_inc_ref(v_stdout_621_);
lean_dec_ref(v___y_609_);
v___x_622_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__4));
v___x_623_ = l_Nat_reprFast(v_val_613_);
v___x_624_ = lean_string_append(v___x_622_, v___x_623_);
lean_dec_ref(v___x_623_);
v___x_625_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__5));
v___x_626_ = lean_string_append(v___x_624_, v___x_625_);
v___x_627_ = lean_string_append(v___x_626_, v_stdout_621_);
lean_dec_ref(v_stdout_621_);
v___x_628_ = 3;
v___x_629_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_629_, 0, v___x_627_);
lean_ctor_set_uint8(v___x_629_, sizeof(void*)*1, v___x_628_);
v___x_630_ = lean_array_push(v___y_610_, v___x_629_);
v___y_581_ = v___y_611_;
v_a_582_ = v___x_630_;
goto v___jp_580_;
}
else
{
lean_object* v___x_631_; lean_object* v___x_632_; 
lean_dec(v_val_613_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_609_);
v___x_631_ = lean_box(0);
v___x_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
lean_ctor_set(v___x_632_, 1, v___y_610_);
return v___x_632_;
}
}
else
{
lean_object* v_stdout_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v_str_637_; lean_object* v_startInclusive_638_; lean_object* v_endExclusive_639_; lean_object* v___x_640_; lean_object* v___x_642_; 
lean_dec(v_val_613_);
lean_dec(v___y_611_);
v_stdout_633_ = lean_ctor_get(v___y_609_, 0);
lean_inc_ref(v_stdout_633_);
lean_dec_ref(v___y_609_);
v___x_634_ = lean_string_utf8_byte_size(v_stdout_633_);
v___x_635_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_635_, 0, v_stdout_633_);
lean_ctor_set(v___x_635_, 1, v___y_608_);
lean_ctor_set(v___x_635_, 2, v___x_634_);
v___x_636_ = l_String_Slice_trimAscii(v___x_635_);
v_str_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc_ref(v_str_637_);
v_startInclusive_638_ = lean_ctor_get(v___x_636_, 1);
lean_inc(v_startInclusive_638_);
v_endExclusive_639_ = lean_ctor_get(v___x_636_, 2);
lean_inc(v_endExclusive_639_);
lean_dec_ref(v___x_636_);
v___x_640_ = lean_string_utf8_extract_fast(v_str_637_, v_startInclusive_638_, v_endExclusive_639_);
lean_dec(v_endExclusive_639_);
lean_dec(v_startInclusive_638_);
lean_dec_ref(v_str_637_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 0, v___x_640_);
v___x_642_ = v___x_615_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_640_);
v___x_642_ = v_reuseFailAlloc_644_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
lean_object* v___x_643_; 
v___x_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
lean_ctor_set(v___x_643_, 1, v___y_610_);
return v___x_643_;
}
}
}
}
}
v___jp_646_:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__6));
v___x_653_ = l_Lake_JsonObject_getJson_x3f(v___y_647_, v___x_652_);
lean_dec(v___y_647_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
v___y_594_ = v___y_651_;
v___y_595_ = v___y_650_;
goto v___jp_593_;
}
else
{
lean_object* v_val_654_; lean_object* v___x_655_; 
v_val_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_val_654_);
lean_dec_ref_known(v___x_653_, 1);
v___x_655_ = l_Lean_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0(v_val_654_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_656_);
lean_dec_ref_known(v___x_655_, 1);
v___x_657_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__7));
v___x_658_ = lean_string_append(v___x_657_, v_a_656_);
lean_dec(v_a_656_);
v___y_585_ = v___y_651_;
v___y_586_ = v___y_650_;
v_a_587_ = v___x_658_;
goto v___jp_584_;
}
else
{
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_659_; 
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
v_a_659_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_659_);
lean_dec_ref_known(v___x_655_, 1);
v___y_585_ = v___y_651_;
v___y_586_ = v___y_650_;
v_a_587_ = v_a_659_;
goto v___jp_584_;
}
else
{
lean_object* v_a_660_; 
v_a_660_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_660_);
lean_dec_ref_known(v___x_655_, 1);
v___y_608_ = v___y_648_;
v___y_609_ = v___y_649_;
v___y_610_ = v___y_650_;
v___y_611_ = v___y_651_;
v_a_612_ = v_a_660_;
goto v___jp_607_;
}
}
}
}
v___jp_661_:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; uint8_t v___x_670_; uint8_t v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_665_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__8));
v___x_666_ = lean_array_push(v___y_662_, v_url_576_);
v___x_667_ = lean_box(0);
v___x_668_ = lean_unsigned_to_nat(0u);
v___x_669_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__9));
v___x_670_ = 1;
v___x_671_ = 0;
v___x_672_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_672_, 0, v___x_665_);
lean_ctor_set(v___x_672_, 1, v_val_664_);
lean_ctor_set(v___x_672_, 2, v___x_666_);
lean_ctor_set(v___x_672_, 3, v___x_667_);
lean_ctor_set(v___x_672_, 4, v___x_669_);
lean_ctor_set_uint8(v___x_672_, sizeof(void*)*5, v___x_670_);
lean_ctor_set_uint8(v___x_672_, sizeof(void*)*5 + 1, v___x_671_);
v___x_673_ = l_Lake_captureProc_x27(v___x_672_, v_a_578_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v_a_675_; lean_object* v_stderr_676_; lean_object* v___x_677_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_a_674_);
v_a_675_ = lean_ctor_get(v___x_673_, 1);
lean_inc(v_a_675_);
lean_dec_ref_known(v___x_673_, 2);
v_stderr_676_ = lean_ctor_get(v_a_674_, 1);
lean_inc_ref(v_stderr_676_);
v___x_677_ = l_Lean_Json_parse(v_stderr_676_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; 
lean_dec(v_a_674_);
v_a_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_a_678_);
lean_dec_ref_known(v___x_677_, 1);
v___y_599_ = v___y_663_;
v___y_600_ = v_a_675_;
v_a_601_ = v_a_678_;
goto v___jp_598_;
}
else
{
lean_object* v_a_679_; lean_object* v___x_680_; 
v_a_679_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_a_679_);
lean_dec_ref_known(v___x_677_, 1);
v___x_680_ = l_Lean_Json_getObj_x3f(v_a_679_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v_a_681_; 
lean_dec(v_a_674_);
v_a_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_a_681_);
lean_dec_ref_known(v___x_680_, 1);
v___y_599_ = v___y_663_;
v___y_600_ = v_a_675_;
v_a_601_ = v_a_681_;
goto v___jp_598_;
}
else
{
lean_object* v_a_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v_a_682_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_a_682_);
lean_dec_ref_known(v___x_680_, 1);
v___x_683_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__10));
v___x_684_ = l_Lake_JsonObject_getJson_x3f(v_a_682_, v___x_683_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_dec(v_a_682_);
lean_dec(v_a_674_);
v___y_594_ = v___y_663_;
v___y_595_ = v_a_675_;
goto v___jp_593_;
}
else
{
lean_object* v_val_685_; lean_object* v___x_686_; 
v_val_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_val_685_);
lean_dec_ref_known(v___x_684_, 1);
v___x_686_ = l_Lean_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0(v_val_685_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_dec_ref_known(v___x_686_, 1);
v___y_647_ = v_a_682_;
v___y_648_ = v___x_668_;
v___y_649_ = v_a_674_;
v___y_650_ = v_a_675_;
v___y_651_ = v___y_663_;
goto v___jp_646_;
}
else
{
if (lean_obj_tag(v___x_686_) == 0)
{
lean_dec_ref_known(v___x_686_, 1);
v___y_647_ = v_a_682_;
v___y_648_ = v___x_668_;
v___y_649_ = v_a_674_;
v___y_650_ = v_a_675_;
v___y_651_ = v___y_663_;
goto v___jp_646_;
}
else
{
lean_object* v_a_687_; 
lean_dec(v_a_682_);
v_a_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_a_687_);
lean_dec_ref_known(v___x_686_, 1);
v___y_608_ = v___x_668_;
v___y_609_ = v_a_674_;
v___y_610_ = v_a_675_;
v___y_611_ = v___y_663_;
v_a_612_ = v_a_687_;
goto v___jp_607_;
}
}
}
}
}
}
else
{
lean_object* v_a_688_; 
v_a_688_ = lean_ctor_get(v___x_673_, 1);
lean_inc(v_a_688_);
lean_dec_ref_known(v___x_673_, 2);
v___y_581_ = v___y_663_;
v_a_582_ = v_a_688_;
goto v___jp_580_;
}
}
v___jp_689_:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_691_ = lean_array_get_size(v_a_578_);
v___x_692_ = ((lean_object*)(l_Lake_Internal_getCurl___closed__0));
v___x_693_ = lean_io_getenv(v___x_692_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v___x_694_; 
v___x_694_ = ((lean_object*)(l_Lake_Internal_getCurl___closed__1));
v___y_662_ = v___y_690_;
v___y_663_ = v___x_691_;
v_val_664_ = v___x_694_;
goto v___jp_661_;
}
else
{
lean_object* v_val_695_; 
v_val_695_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_val_695_);
lean_dec_ref_known(v___x_693_, 1);
v___y_662_ = v___y_690_;
v___y_663_ = v___x_691_;
v_val_664_ = v_val_695_;
goto v___jp_661_;
}
}
}
}
LEAN_EXPORT void l_Lake_getUrl_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_url_576_ = stack[0].m_obj;
lean_object* v_headers_577_ = stack[1].m_obj;
lean_object* v_a_578_ = stack[2].m_obj;
lean_object* v_res_707_;
v_res_707_ = l_Lake_getUrl_x3f(v_url_576_, v_headers_577_, v_a_578_);
stack->m_obj
 = v_res_707_;
}
LEAN_EXPORT lean_object* l_Lake_getUrl_x3f___boxed(lean_object* v_url_708_, lean_object* v_headers_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lake_getUrl_x3f(v_url_708_, v_headers_709_, v_a_710_);
lean_dec_ref(v_headers_709_);
return v_res_712_;
}
}
lean_object* l_Lake_getUrl(lean_object* v_url_723_, lean_object* v_headers_724_, lean_object* v_a_725_){
_start:
{
lean_object* v___y_728_; lean_object* v_a_729_; lean_object* v_a_730_; lean_object* v___y_767_; lean_object* v_args_772_; lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; 
v_args_772_ = ((lean_object*)(l_Lake_getUrl___closed__0));
v___x_773_ = lean_unsigned_to_nat(0u);
v___x_774_ = lean_array_get_size(v_headers_724_);
v___x_775_ = lean_nat_dec_lt(v___x_773_, v___x_774_);
if (v___x_775_ == 0)
{
v___y_767_ = v_args_772_;
goto v___jp_766_;
}
else
{
uint8_t v___x_776_; 
v___x_776_ = lean_nat_dec_le(v___x_774_, v___x_774_);
if (v___x_776_ == 0)
{
if (v___x_775_ == 0)
{
v___y_767_ = v_args_772_;
goto v___jp_766_;
}
else
{
size_t v___x_777_; size_t v___x_778_; lean_object* v___x_779_; 
v___x_777_ = ((size_t)0ULL);
v___x_778_ = lean_usize_of_nat(v___x_774_);
v___x_779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1(v_headers_724_, v___x_777_, v___x_778_, v_args_772_);
v___y_767_ = v___x_779_;
goto v___jp_766_;
}
}
else
{
size_t v___x_780_; size_t v___x_781_; lean_object* v___x_782_; 
v___x_780_ = ((size_t)0ULL);
v___x_781_ = lean_usize_of_nat(v___x_774_);
v___x_782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1(v_headers_724_, v___x_780_, v___x_781_, v_args_772_);
v___y_767_ = v___x_782_;
goto v___jp_766_;
}
}
v___jp_727_:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; uint8_t v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_731_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__8));
v___x_732_ = lean_array_push(v___y_728_, v_url_723_);
v___x_733_ = lean_box(0);
v___x_734_ = lean_unsigned_to_nat(0u);
v___x_735_ = ((lean_object*)(l_Lake_getUrl_x3f___closed__9));
v___x_736_ = 1;
v___x_737_ = 0;
v___x_738_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_738_, 0, v___x_731_);
lean_ctor_set(v___x_738_, 1, v_a_729_);
lean_ctor_set(v___x_738_, 2, v___x_732_);
lean_ctor_set(v___x_738_, 3, v___x_733_);
lean_ctor_set(v___x_738_, 4, v___x_735_);
lean_ctor_set_uint8(v___x_738_, sizeof(void*)*5, v___x_736_);
lean_ctor_set_uint8(v___x_738_, sizeof(void*)*5 + 1, v___x_737_);
v___x_739_ = l_Lake_captureProc_x27(v___x_738_, v_a_730_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_756_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
v_a_741_ = lean_ctor_get(v___x_739_, 1);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_756_ == 0)
{
v___x_743_ = v___x_739_;
v_isShared_744_ = v_isSharedCheck_756_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_inc(v_a_740_);
lean_dec(v___x_739_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_756_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v_stdout_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v_str_749_; lean_object* v_startInclusive_750_; lean_object* v_endExclusive_751_; lean_object* v___x_752_; lean_object* v___x_754_; 
v_stdout_745_ = lean_ctor_get(v_a_740_, 0);
lean_inc_ref(v_stdout_745_);
lean_dec(v_a_740_);
v___x_746_ = lean_string_utf8_byte_size(v_stdout_745_);
v___x_747_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_747_, 0, v_stdout_745_);
lean_ctor_set(v___x_747_, 1, v___x_734_);
lean_ctor_set(v___x_747_, 2, v___x_746_);
v___x_748_ = l_String_Slice_trimAscii(v___x_747_);
v_str_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc_ref(v_str_749_);
v_startInclusive_750_ = lean_ctor_get(v___x_748_, 1);
lean_inc(v_startInclusive_750_);
v_endExclusive_751_ = lean_ctor_get(v___x_748_, 2);
lean_inc(v_endExclusive_751_);
lean_dec_ref(v___x_748_);
v___x_752_ = lean_string_utf8_extract_fast(v_str_749_, v_startInclusive_750_, v_endExclusive_751_);
lean_dec(v_endExclusive_751_);
lean_dec(v_startInclusive_750_);
lean_dec_ref(v_str_749_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_752_);
v___x_754_ = v___x_743_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v_a_741_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
else
{
lean_object* v_a_757_; lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
v_a_757_ = lean_ctor_get(v___x_739_, 0);
v_a_758_ = lean_ctor_get(v___x_739_, 1);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_739_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_inc(v_a_757_);
lean_dec(v___x_739_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_757_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
v___jp_766_:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = ((lean_object*)(l_Lake_Internal_getCurl___closed__0));
v___x_769_ = lean_io_getenv(v___x_768_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v___x_770_; 
v___x_770_ = ((lean_object*)(l_Lake_Internal_getCurl___closed__1));
v___y_728_ = v___y_767_;
v_a_729_ = v___x_770_;
v_a_730_ = v_a_725_;
goto v___jp_727_;
}
else
{
lean_object* v_val_771_; 
v_val_771_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_val_771_);
lean_dec_ref_known(v___x_769_, 1);
v___y_728_ = v___y_767_;
v_a_729_ = v_val_771_;
v_a_730_ = v_a_725_;
goto v___jp_727_;
}
}
}
}
LEAN_EXPORT void l_Lake_getUrl_0interp(lean_interpreter_value* stack)
{
lean_object* v_url_723_ = stack[0].m_obj;
lean_object* v_headers_724_ = stack[1].m_obj;
lean_object* v_a_725_ = stack[2].m_obj;
lean_object* v_res_783_;
v_res_783_ = l_Lake_getUrl(v_url_723_, v_headers_724_, v_a_725_);
stack->m_obj
 = v_res_783_;
}
LEAN_EXPORT lean_object* l_Lake_getUrl___boxed(lean_object* v_url_784_, lean_object* v_headers_785_, lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lake_getUrl(v_url_784_, v_headers_785_, v_a_786_);
lean_dec_ref(v_headers_785_);
return v_res_788_;
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

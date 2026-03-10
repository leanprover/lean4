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
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
LEAN_EXPORT uint32_t l_Lake_hexEncodeByte(uint8_t);
LEAN_EXPORT lean_object* l_Lake_hexEncodeByte___boxed(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
uint8_t lean_uint8_shift_right(uint8_t, uint8_t);
uint8_t lean_uint8_land(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_uriEscapeByte(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_uriEscapeByte___boxed(lean_object*, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
uint8_t lean_uint8_lor(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__0(uint32_t, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_shift_right(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__1(uint32_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__2(uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__4(uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__3(uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg(lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M(lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___redArg___lam__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_foldlUtf8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_foldlUtf8___redArg___closed__0 = (const lean_object*)&l_Lake_foldlUtf8___redArg___closed__0_value;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_foldlUtf8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_foldlUtf8___redArg___closed__1 = (const lean_object*)&l_Lake_foldlUtf8___redArg___closed__1_value;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_foldlUtf8___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_foldlUtf8___redArg___closed__2 = (const lean_object*)&l_Lake_foldlUtf8___redArg___closed__2_value;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_foldlUtf8___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_foldlUtf8___redArg___closed__3 = (const lean_object*)&l_Lake_foldlUtf8___redArg___closed__3_value;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_foldlUtf8___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_foldlUtf8___redArg___closed__4 = (const lean_object*)&l_Lake_foldlUtf8___redArg___closed__4_value;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_foldlUtf8___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_foldlUtf8___redArg___closed__5 = (const lean_object*)&l_Lake_foldlUtf8___redArg___closed__5_value;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT uint8_t l_Lake_isUriUnreservedMark(uint32_t);
LEAN_EXPORT lean_object* l_Lake_isUriUnreservedMark___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_uriEncodeChar(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_uriEncodeChar___boxed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_positions(lean_object*);
LEAN_EXPORT lean_object* l_Lake_uriEncode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0___closed__0_value;
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-H"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__0_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__1;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
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
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JsonObject_getJson_x3f(lean_object*, lean_object*);
lean_object* l_Lake_captureProc_x27(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getUrl_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getUrl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_getUrl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_Lake_getUrl_x3f___closed__12_value),((lean_object*)&l_Lake_getUrl_x3f___closed__13_value),((lean_object*)&l_Lake_getUrl_x3f___closed__16_value),((lean_object*)&l_Lake_getUrl_x3f___closed__17_value)}};
static const lean_object* l_Lake_getUrl___closed__0 = (const lean_object*)&l_Lake_getUrl___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getUrl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getUrl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lake_hexEncodeByte(uint8_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; 
x_2 = 0;
x_3 = lean_uint8_dec_eq(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; uint8_t x_5; 
x_4 = 1;
x_5 = lean_uint8_dec_eq(x_1, x_4);
if (x_5 == 0)
{
uint8_t x_6; uint8_t x_7; 
x_6 = 2;
x_7 = lean_uint8_dec_eq(x_1, x_6);
if (x_7 == 0)
{
uint8_t x_8; uint8_t x_9; 
x_8 = 3;
x_9 = lean_uint8_dec_eq(x_1, x_8);
if (x_9 == 0)
{
uint8_t x_10; uint8_t x_11; 
x_10 = 4;
x_11 = lean_uint8_dec_eq(x_1, x_10);
if (x_11 == 0)
{
uint8_t x_12; uint8_t x_13; 
x_12 = 5;
x_13 = lean_uint8_dec_eq(x_1, x_12);
if (x_13 == 0)
{
uint8_t x_14; uint8_t x_15; 
x_14 = 6;
x_15 = lean_uint8_dec_eq(x_1, x_14);
if (x_15 == 0)
{
uint8_t x_16; uint8_t x_17; 
x_16 = 7;
x_17 = lean_uint8_dec_eq(x_1, x_16);
if (x_17 == 0)
{
uint8_t x_18; uint8_t x_19; 
x_18 = 8;
x_19 = lean_uint8_dec_eq(x_1, x_18);
if (x_19 == 0)
{
uint8_t x_20; uint8_t x_21; 
x_20 = 9;
x_21 = lean_uint8_dec_eq(x_1, x_20);
if (x_21 == 0)
{
uint8_t x_22; uint8_t x_23; 
x_22 = 10;
x_23 = lean_uint8_dec_eq(x_1, x_22);
if (x_23 == 0)
{
uint8_t x_24; uint8_t x_25; 
x_24 = 11;
x_25 = lean_uint8_dec_eq(x_1, x_24);
if (x_25 == 0)
{
uint8_t x_26; uint8_t x_27; 
x_26 = 12;
x_27 = lean_uint8_dec_eq(x_1, x_26);
if (x_27 == 0)
{
uint8_t x_28; uint8_t x_29; 
x_28 = 13;
x_29 = lean_uint8_dec_eq(x_1, x_28);
if (x_29 == 0)
{
uint8_t x_30; uint8_t x_31; 
x_30 = 14;
x_31 = lean_uint8_dec_eq(x_1, x_30);
if (x_31 == 0)
{
uint8_t x_32; uint8_t x_33; 
x_32 = 15;
x_33 = lean_uint8_dec_eq(x_1, x_32);
if (x_33 == 0)
{
uint32_t x_34; 
x_34 = 42;
return x_34;
}
else
{
uint32_t x_35; 
x_35 = 70;
return x_35;
}
}
else
{
uint32_t x_36; 
x_36 = 69;
return x_36;
}
}
else
{
uint32_t x_37; 
x_37 = 68;
return x_37;
}
}
else
{
uint32_t x_38; 
x_38 = 67;
return x_38;
}
}
else
{
uint32_t x_39; 
x_39 = 66;
return x_39;
}
}
else
{
uint32_t x_40; 
x_40 = 65;
return x_40;
}
}
else
{
uint32_t x_41; 
x_41 = 57;
return x_41;
}
}
else
{
uint32_t x_42; 
x_42 = 56;
return x_42;
}
}
else
{
uint32_t x_43; 
x_43 = 55;
return x_43;
}
}
else
{
uint32_t x_44; 
x_44 = 54;
return x_44;
}
}
else
{
uint32_t x_45; 
x_45 = 53;
return x_45;
}
}
else
{
uint32_t x_46; 
x_46 = 52;
return x_46;
}
}
else
{
uint32_t x_47; 
x_47 = 51;
return x_47;
}
}
else
{
uint32_t x_48; 
x_48 = 50;
return x_48;
}
}
else
{
uint32_t x_49; 
x_49 = 49;
return x_49;
}
}
else
{
uint32_t x_50; 
x_50 = 48;
return x_50;
}
}
}
LEAN_EXPORT lean_object* l_Lake_hexEncodeByte___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Lake_hexEncodeByte(x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_uriEscapeByte(uint8_t x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; uint32_t x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint32_t x_11; lean_object* x_12; 
x_3 = 37;
x_4 = lean_string_push(x_2, x_3);
x_5 = 4;
x_6 = lean_uint8_shift_right(x_1, x_5);
x_7 = l_Lake_hexEncodeByte(x_6);
x_8 = lean_string_push(x_4, x_7);
x_9 = 15;
x_10 = lean_uint8_land(x_1, x_9);
x_11 = l_Lake_hexEncodeByte(x_10);
x_12 = lean_string_push(x_8, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_uriEscapeByte___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lake_uriEscapeByte(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__0(uint32_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_uint32_to_uint8(x_1);
x_7 = lean_uint8_land(x_6, x_2);
x_8 = lean_uint8_lor(x_7, x_3);
x_9 = lean_box(x_8);
x_10 = lean_apply_2(x_4, x_5, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint32_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_7 = lean_unbox(x_2);
x_8 = lean_unbox(x_3);
x_9 = l_Lake_foldlUtf8M___redArg___lam__0(x_6, x_7, x_8, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__1(uint32_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = 6;
x_9 = lean_uint32_shift_right(x_1, x_8);
x_10 = lean_uint32_to_uint8(x_9);
x_11 = lean_uint8_land(x_10, x_2);
x_12 = lean_uint8_lor(x_11, x_3);
x_13 = lean_box(x_12);
x_14 = lean_apply_2(x_4, x_7, x_13);
x_15 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_14, x_6);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint32_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_9 = lean_unbox(x_2);
x_10 = lean_unbox(x_3);
x_11 = l_Lake_foldlUtf8M___redArg___lam__1(x_8, x_9, x_10, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__2(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; uint32_t x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_5 = 12;
x_6 = lean_uint32_shift_right(x_1, x_5);
x_7 = lean_uint32_to_uint8(x_6);
x_8 = 63;
x_9 = lean_uint8_land(x_7, x_8);
x_10 = 128;
x_11 = lean_box_uint32(x_1);
x_12 = lean_box(x_8);
x_13 = lean_box(x_10);
lean_inc(x_2);
x_14 = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_14, 0, x_11);
lean_closure_set(x_14, 1, x_12);
lean_closure_set(x_14, 2, x_13);
lean_closure_set(x_14, 3, x_2);
x_15 = lean_box_uint32(x_1);
x_16 = lean_box(x_8);
x_17 = lean_box(x_10);
lean_inc(x_3);
lean_inc(x_2);
x_18 = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___redArg___lam__1___boxed), 7, 6);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_16);
lean_closure_set(x_18, 2, x_17);
lean_closure_set(x_18, 3, x_2);
lean_closure_set(x_18, 4, x_3);
lean_closure_set(x_18, 5, x_14);
x_19 = lean_uint8_lor(x_9, x_10);
x_20 = lean_box(x_19);
x_21 = lean_apply_2(x_2, x_4, x_20);
x_22 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_21, x_18);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_6 = l_Lake_foldlUtf8M___redArg___lam__2(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__4(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; uint32_t x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_5 = 6;
x_6 = lean_uint32_shift_right(x_1, x_5);
x_7 = lean_uint32_to_uint8(x_6);
x_8 = 63;
x_9 = lean_uint8_land(x_7, x_8);
x_10 = 128;
x_11 = lean_box_uint32(x_1);
x_12 = lean_box(x_8);
x_13 = lean_box(x_10);
lean_inc(x_2);
x_14 = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_14, 0, x_11);
lean_closure_set(x_14, 1, x_12);
lean_closure_set(x_14, 2, x_13);
lean_closure_set(x_14, 3, x_2);
x_15 = lean_uint8_lor(x_9, x_10);
x_16 = lean_box(x_15);
x_17 = lean_apply_2(x_2, x_4, x_16);
x_18 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_17, x_14);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_6 = l_Lake_foldlUtf8M___redArg___lam__4(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__3(uint32_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_uint32_to_uint8(x_1);
x_5 = 63;
x_6 = lean_uint8_land(x_4, x_5);
x_7 = 128;
x_8 = lean_uint8_lor(x_6, x_7);
x_9 = lean_box(x_8);
x_10 = lean_apply_2(x_2, x_3, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_5 = l_Lake_foldlUtf8M___redArg___lam__3(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg(lean_object* x_1, uint32_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; uint8_t x_6; 
x_5 = 127;
x_6 = lean_uint32_dec_le(x_2, x_5);
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; 
x_7 = 2047;
x_8 = lean_uint32_dec_le(x_2, x_7);
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 65535;
x_10 = lean_uint32_dec_le(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint32_t x_14; uint32_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = lean_box_uint32(x_2);
lean_inc(x_11);
lean_inc(x_3);
x_13 = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___redArg___lam__2___boxed), 4, 3);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_3);
lean_closure_set(x_13, 2, x_11);
x_14 = 18;
x_15 = lean_uint32_shift_right(x_2, x_14);
x_16 = lean_uint32_to_uint8(x_15);
x_17 = 7;
x_18 = lean_uint8_land(x_16, x_17);
x_19 = 240;
x_20 = lean_uint8_lor(x_18, x_19);
x_21 = lean_box(x_20);
x_22 = lean_apply_2(x_3, x_4, x_21);
x_23 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_22, x_13);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint32_t x_27; uint32_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_dec_ref(x_1);
x_25 = lean_box_uint32(x_2);
lean_inc(x_24);
lean_inc(x_3);
x_26 = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___redArg___lam__4___boxed), 4, 3);
lean_closure_set(x_26, 0, x_25);
lean_closure_set(x_26, 1, x_3);
lean_closure_set(x_26, 2, x_24);
x_27 = 12;
x_28 = lean_uint32_shift_right(x_2, x_27);
x_29 = lean_uint32_to_uint8(x_28);
x_30 = 15;
x_31 = lean_uint8_land(x_29, x_30);
x_32 = 224;
x_33 = lean_uint8_lor(x_31, x_32);
x_34 = lean_box(x_33);
x_35 = lean_apply_2(x_3, x_4, x_34);
x_36 = lean_apply_4(x_24, lean_box(0), lean_box(0), x_35, x_26);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint32_t x_40; uint32_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_dec_ref(x_1);
x_38 = lean_box_uint32(x_2);
lean_inc(x_3);
x_39 = lean_alloc_closure((void*)(l_Lake_foldlUtf8M___redArg___lam__3___boxed), 3, 2);
lean_closure_set(x_39, 0, x_38);
lean_closure_set(x_39, 1, x_3);
x_40 = 6;
x_41 = lean_uint32_shift_right(x_2, x_40);
x_42 = lean_uint32_to_uint8(x_41);
x_43 = 31;
x_44 = lean_uint8_land(x_42, x_43);
x_45 = 192;
x_46 = lean_uint8_lor(x_44, x_45);
x_47 = lean_box(x_46);
x_48 = lean_apply_2(x_3, x_4, x_47);
x_49 = lean_apply_4(x_37, lean_box(0), lean_box(0), x_48, x_39);
return x_49;
}
}
else
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; 
lean_dec_ref(x_1);
x_50 = lean_uint32_to_uint8(x_2);
x_51 = lean_box(x_50);
x_52 = lean_apply_2(x_3, x_4, x_51);
return x_52;
}
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_6 = l_Lake_foldlUtf8M___redArg(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint32_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_foldlUtf8M___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint32_t x_7; lean_object* x_8; 
x_7 = lean_unbox_uint32(x_4);
lean_dec(x_4);
x_8 = l_Lake_foldlUtf8M(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___redArg___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(x_3);
x_5 = lean_apply_2(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_Lake_foldlUtf8___redArg___lam__0(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___redArg(uint32_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lake_foldlUtf8___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = ((lean_object*)(l_Lake_foldlUtf8___redArg___closed__9));
x_6 = l_Lake_foldlUtf8M___redArg(x_5, x_1, x_4, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_5 = l_Lake_foldlUtf8___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8(lean_object* x_1, uint32_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_Lake_foldlUtf8___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = ((lean_object*)(l_Lake_foldlUtf8___redArg___closed__9));
x_7 = l_Lake_foldlUtf8M___redArg(x_6, x_2, x_5, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_6 = l_Lake_foldlUtf8(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___at___00Lake_uriEscapeChar_spec__0(uint32_t x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_4; 
x_3 = 127;
x_4 = lean_uint32_dec_le(x_1, x_3);
if (x_4 == 0)
{
uint32_t x_5; uint8_t x_6; 
x_5 = 2047;
x_6 = lean_uint32_dec_le(x_1, x_5);
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; 
x_7 = 65535;
x_8 = lean_uint32_dec_le(x_1, x_7);
if (x_8 == 0)
{
uint32_t x_9; uint32_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; uint32_t x_17; uint32_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; uint32_t x_25; uint32_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; 
x_9 = 18;
x_10 = lean_uint32_shift_right(x_1, x_9);
x_11 = lean_uint32_to_uint8(x_10);
x_12 = 7;
x_13 = lean_uint8_land(x_11, x_12);
x_14 = 240;
x_15 = lean_uint8_lor(x_13, x_14);
x_16 = l_Lake_uriEscapeByte(x_15, x_2);
x_17 = 12;
x_18 = lean_uint32_shift_right(x_1, x_17);
x_19 = lean_uint32_to_uint8(x_18);
x_20 = 63;
x_21 = lean_uint8_land(x_19, x_20);
x_22 = 128;
x_23 = lean_uint8_lor(x_21, x_22);
x_24 = l_Lake_uriEscapeByte(x_23, x_16);
x_25 = 6;
x_26 = lean_uint32_shift_right(x_1, x_25);
x_27 = lean_uint32_to_uint8(x_26);
x_28 = lean_uint8_land(x_27, x_20);
x_29 = lean_uint8_lor(x_28, x_22);
x_30 = l_Lake_uriEscapeByte(x_29, x_24);
x_31 = lean_uint32_to_uint8(x_1);
x_32 = lean_uint8_land(x_31, x_20);
x_33 = lean_uint8_lor(x_32, x_22);
x_34 = l_Lake_uriEscapeByte(x_33, x_30);
return x_34;
}
else
{
uint32_t x_35; uint32_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; uint32_t x_43; uint32_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; lean_object* x_54; 
x_35 = 12;
x_36 = lean_uint32_shift_right(x_1, x_35);
x_37 = lean_uint32_to_uint8(x_36);
x_38 = 15;
x_39 = lean_uint8_land(x_37, x_38);
x_40 = 224;
x_41 = lean_uint8_lor(x_39, x_40);
x_42 = l_Lake_uriEscapeByte(x_41, x_2);
x_43 = 6;
x_44 = lean_uint32_shift_right(x_1, x_43);
x_45 = lean_uint32_to_uint8(x_44);
x_46 = 63;
x_47 = lean_uint8_land(x_45, x_46);
x_48 = 128;
x_49 = lean_uint8_lor(x_47, x_48);
x_50 = l_Lake_uriEscapeByte(x_49, x_42);
x_51 = lean_uint32_to_uint8(x_1);
x_52 = lean_uint8_land(x_51, x_46);
x_53 = lean_uint8_lor(x_52, x_48);
x_54 = l_Lake_uriEscapeByte(x_53, x_50);
return x_54;
}
}
else
{
uint32_t x_55; uint32_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; lean_object* x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; lean_object* x_68; 
x_55 = 6;
x_56 = lean_uint32_shift_right(x_1, x_55);
x_57 = lean_uint32_to_uint8(x_56);
x_58 = 31;
x_59 = lean_uint8_land(x_57, x_58);
x_60 = 192;
x_61 = lean_uint8_lor(x_59, x_60);
x_62 = l_Lake_uriEscapeByte(x_61, x_2);
x_63 = lean_uint32_to_uint8(x_1);
x_64 = 63;
x_65 = lean_uint8_land(x_63, x_64);
x_66 = 128;
x_67 = lean_uint8_lor(x_65, x_66);
x_68 = l_Lake_uriEscapeByte(x_67, x_62);
return x_68;
}
}
else
{
uint8_t x_69; lean_object* x_70; 
x_69 = lean_uint32_to_uint8(x_1);
x_70 = l_Lake_uriEscapeByte(x_69, x_2);
return x_70;
}
}
}
LEAN_EXPORT lean_object* l_Lake_foldlUtf8M___at___00Lake_uriEscapeChar_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_Lake_foldlUtf8M___at___00Lake_uriEscapeChar_spec__0(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_uriEscapeChar(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_foldlUtf8M___at___00Lake_uriEscapeChar_spec__0(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_uriEscapeChar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_Lake_uriEscapeChar(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lake_isUriUnreservedMark(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 45;
x_3 = lean_uint32_dec_eq(x_1, x_2);
if (x_3 == 0)
{
uint32_t x_4; uint8_t x_5; 
x_4 = 95;
x_5 = lean_uint32_dec_eq(x_1, x_4);
if (x_5 == 0)
{
uint32_t x_6; uint8_t x_7; 
x_6 = 46;
x_7 = lean_uint32_dec_eq(x_1, x_6);
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; 
x_8 = 126;
x_9 = lean_uint32_dec_eq(x_1, x_8);
return x_9;
}
else
{
return x_7;
}
}
else
{
return x_5;
}
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lake_isUriUnreservedMark___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lake_isUriUnreservedMark(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_uriEncodeChar(uint32_t x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_9; uint32_t x_21; uint8_t x_22; 
x_21 = 65;
x_22 = lean_uint32_dec_le(x_21, x_1);
if (x_22 == 0)
{
goto block_20;
}
else
{
uint32_t x_23; uint8_t x_24; 
x_23 = 90;
x_24 = lean_uint32_dec_le(x_1, x_23);
if (x_24 == 0)
{
goto block_20;
}
else
{
lean_object* x_25; 
x_25 = lean_string_push(x_2, x_1);
return x_25;
}
}
block_8:
{
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = l_Lake_isUriUnreservedMark(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lake_foldlUtf8M___at___00Lake_uriEscapeChar_spec__0(x_1, x_2);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_string_push(x_2, x_1);
return x_6;
}
}
else
{
lean_object* x_7; 
x_7 = lean_string_push(x_2, x_1);
return x_7;
}
}
block_15:
{
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 48;
x_11 = lean_uint32_dec_le(x_10, x_1);
if (x_11 == 0)
{
x_3 = x_11;
goto block_8;
}
else
{
uint32_t x_12; uint8_t x_13; 
x_12 = 57;
x_13 = lean_uint32_dec_le(x_1, x_12);
x_3 = x_13;
goto block_8;
}
}
else
{
lean_object* x_14; 
x_14 = lean_string_push(x_2, x_1);
return x_14;
}
}
block_20:
{
uint32_t x_16; uint8_t x_17; 
x_16 = 97;
x_17 = lean_uint32_dec_le(x_16, x_1);
if (x_17 == 0)
{
x_9 = x_17;
goto block_15;
}
else
{
uint32_t x_18; uint8_t x_19; 
x_18 = 122;
x_19 = lean_uint32_dec_le(x_1, x_18);
x_9 = x_19;
goto block_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_uriEncodeChar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_Lake_uriEncodeChar(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_nat_sub(x_6, x_5);
x_8 = lean_nat_dec_eq(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint32_t x_10; lean_object* x_11; 
x_9 = lean_string_utf8_next_fast(x_2, x_3);
x_10 = lean_string_utf8_get_fast(x_2, x_3);
lean_dec(x_3);
x_11 = l_Lake_uriEncodeChar(x_10, x_4);
x_3 = x_9;
x_4 = x_11;
goto _start;
}
else
{
lean_dec(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_uriEncode(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = l_String_Slice_positions(x_5);
x_7 = l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___redArg(x_5, x_1, x_6, x_2);
lean_dec_ref(x_1);
lean_dec_ref(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___redArg(x_1, x_2, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00Lake_uriEncode_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0___closed__0));
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lean_Json_getNat_x3f(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_20; 
x_12 = lean_ctor_get(x_3, 0);
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
x_13 = x_3;
x_14 = x_20;
goto block_19;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_15);
x_16 = x_13;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_15);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__0));
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = lean_array_push(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget_borrowed(x_1, x_2);
x_7 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___closed__1);
lean_inc(x_6);
x_8 = lean_array_push(x_7, x_6);
x_9 = l_Array_append___redArg(x_4, x_8);
lean_dec_ref(x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_getUrl_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_18; lean_object* x_19; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_86; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_114 = ((lean_object*)(l_Lake_getUrl_x3f___closed__18));
x_115 = lean_unsigned_to_nat(0u);
x_116 = lean_array_get_size(x_2);
x_117 = lean_nat_dec_lt(x_115, x_116);
if (x_117 == 0)
{
x_86 = x_114;
goto block_113;
}
else
{
uint8_t x_118; 
x_118 = lean_nat_dec_le(x_116, x_116);
if (x_118 == 0)
{
if (x_117 == 0)
{
x_86 = x_114;
goto block_113;
}
else
{
size_t x_119; size_t x_120; lean_object* x_121; 
x_119 = 0;
x_120 = lean_usize_of_nat(x_116);
x_121 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1(x_2, x_119, x_120, x_114);
x_86 = x_121;
goto block_113;
}
}
else
{
size_t x_122; size_t x_123; lean_object* x_124; 
x_122 = 0;
x_123 = lean_usize_of_nat(x_116);
x_124 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1(x_2, x_122, x_123, x_114);
x_86 = x_124;
goto block_113;
}
}
block_8:
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
block_17:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_12 = ((lean_object*)(l_Lake_getUrl_x3f___closed__0));
x_13 = lean_string_append(x_12, x_11);
lean_dec_ref(x_11);
x_14 = 3;
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
x_16 = lean_array_push(x_10, x_15);
x_5 = x_9;
x_6 = x_16;
goto block_8;
}
block_22:
{
lean_object* x_20; lean_object* x_21; 
x_20 = ((lean_object*)(l_Lake_getUrl_x3f___closed__2));
x_21 = lean_array_push(x_19, x_20);
x_5 = x_18;
x_6 = x_21;
goto block_8;
}
block_31:
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_26 = ((lean_object*)(l_Lake_getUrl_x3f___closed__3));
x_27 = lean_string_append(x_26, x_25);
lean_dec_ref(x_25);
x_28 = 3;
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
x_30 = lean_array_push(x_24, x_29);
x_5 = x_23;
x_6 = x_30;
goto block_8;
}
block_70:
{
if (lean_obj_tag(x_36) == 0)
{
lean_dec(x_35);
lean_dec_ref(x_32);
x_18 = x_33;
x_19 = x_34;
goto block_22;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_69; 
x_37 = lean_ctor_get(x_36, 0);
x_69 = !lean_is_exclusive(x_36);
if (x_69 == 0)
{
x_38 = x_36;
x_39 = x_69;
goto block_68;
}
else
{
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_box(0);
x_39 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_unsigned_to_nat(200u);
x_41 = lean_nat_dec_eq(x_37, x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
lean_del_object(x_38);
lean_dec(x_35);
x_42 = lean_unsigned_to_nat(404u);
x_43 = lean_nat_dec_eq(x_37, x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_44 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_44);
lean_dec_ref(x_32);
x_45 = ((lean_object*)(l_Lake_getUrl_x3f___closed__4));
x_46 = l_Nat_reprFast(x_37);
x_47 = lean_string_append(x_45, x_46);
lean_dec_ref(x_46);
x_48 = ((lean_object*)(l_Lake_getUrl_x3f___closed__5));
x_49 = lean_string_append(x_47, x_48);
x_50 = lean_string_append(x_49, x_44);
lean_dec_ref(x_44);
x_51 = 3;
x_52 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_51);
x_53 = lean_array_push(x_34, x_52);
x_5 = x_33;
x_6 = x_53;
goto block_8;
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_37);
lean_dec(x_33);
lean_dec_ref(x_32);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_34);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_37);
lean_dec(x_33);
x_56 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_56);
lean_dec_ref(x_32);
x_57 = lean_string_utf8_byte_size(x_56);
x_58 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_35);
lean_ctor_set(x_58, 2, x_57);
x_59 = l_String_Slice_trimAscii(x_58);
lean_dec_ref(x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc_ref(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_59, 2);
lean_inc(x_62);
lean_dec_ref(x_59);
x_63 = lean_string_utf8_extract(x_60, x_61, x_62);
lean_dec(x_62);
lean_dec(x_61);
lean_dec_ref(x_60);
if (x_39 == 0)
{
lean_ctor_set(x_38, 0, x_63);
x_64 = x_38;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_63);
x_64 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_34);
return x_65;
}
}
}
}
}
block_85:
{
lean_object* x_76; lean_object* x_77; 
x_76 = ((lean_object*)(l_Lake_getUrl_x3f___closed__6));
x_77 = l_Lake_JsonObject_getJson_x3f(x_73, x_76);
lean_dec(x_73);
if (lean_obj_tag(x_77) == 0)
{
lean_dec(x_75);
lean_dec_ref(x_71);
x_18 = x_72;
x_19 = x_74;
goto block_22;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
x_79 = l_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0(x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_75);
lean_dec_ref(x_71);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
x_81 = ((lean_object*)(l_Lake_getUrl_x3f___closed__7));
x_82 = lean_string_append(x_81, x_80);
lean_dec(x_80);
x_9 = x_72;
x_10 = x_74;
x_11 = x_82;
goto block_17;
}
else
{
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_83; 
lean_dec(x_75);
lean_dec_ref(x_71);
x_83 = lean_ctor_get(x_79, 0);
lean_inc(x_83);
lean_dec_ref(x_79);
x_9 = x_72;
x_10 = x_74;
x_11 = x_83;
goto block_17;
}
else
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_79, 0);
lean_inc(x_84);
lean_dec_ref(x_79);
x_32 = x_71;
x_33 = x_72;
x_34 = x_74;
x_35 = x_75;
x_36 = x_84;
goto block_70;
}
}
}
}
block_113:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_87 = ((lean_object*)(l_Lake_getUrl_x3f___closed__8));
x_88 = ((lean_object*)(l_Lake_getUrl_x3f___closed__9));
x_89 = lean_array_push(x_86, x_1);
x_90 = lean_box(0);
x_91 = lean_unsigned_to_nat(0u);
x_92 = ((lean_object*)(l_Lake_getUrl_x3f___closed__10));
x_93 = 1;
x_94 = 0;
x_95 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_95, 0, x_87);
lean_ctor_set(x_95, 1, x_88);
lean_ctor_set(x_95, 2, x_89);
lean_ctor_set(x_95, 3, x_90);
lean_ctor_set(x_95, 4, x_92);
lean_ctor_set_uint8(x_95, sizeof(void*)*5, x_93);
lean_ctor_set_uint8(x_95, sizeof(void*)*5 + 1, x_94);
lean_inc_ref(x_3);
x_96 = l_Lake_captureProc_x27(x_95, x_3);
x_97 = lean_array_get_size(x_3);
lean_dec_ref(x_3);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_dec_ref(x_96);
x_100 = lean_ctor_get(x_98, 1);
lean_inc_ref(x_100);
x_101 = l_Lean_Json_parse(x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; 
lean_dec(x_98);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec_ref(x_101);
x_23 = x_97;
x_24 = x_99;
x_25 = x_102;
goto block_31;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
lean_dec_ref(x_101);
x_104 = l_Lean_Json_getObj_x3f(x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; 
lean_dec(x_98);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec_ref(x_104);
x_23 = x_97;
x_24 = x_99;
x_25 = x_105;
goto block_31;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
lean_dec_ref(x_104);
x_107 = ((lean_object*)(l_Lake_getUrl_x3f___closed__11));
x_108 = l_Lake_JsonObject_getJson_x3f(x_106, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_dec(x_106);
lean_dec(x_98);
x_18 = x_97;
x_19 = x_99;
goto block_22;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec_ref(x_108);
x_110 = l_Option_fromJson_x3f___at___00Lake_getUrl_x3f_spec__0(x_109);
if (lean_obj_tag(x_110) == 0)
{
lean_dec_ref(x_110);
x_71 = x_98;
x_72 = x_97;
x_73 = x_106;
x_74 = x_99;
x_75 = x_91;
goto block_85;
}
else
{
if (lean_obj_tag(x_110) == 0)
{
lean_dec_ref(x_110);
x_71 = x_98;
x_72 = x_97;
x_73 = x_106;
x_74 = x_99;
x_75 = x_91;
goto block_85;
}
else
{
lean_object* x_111; 
lean_dec(x_106);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec_ref(x_110);
x_32 = x_98;
x_33 = x_97;
x_34 = x_99;
x_35 = x_91;
x_36 = x_111;
goto block_70;
}
}
}
}
}
}
else
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_96, 1);
lean_inc(x_112);
lean_dec_ref(x_96);
x_5 = x_97;
x_6 = x_112;
goto block_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getUrl_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_getUrl_x3f(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_getUrl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = ((lean_object*)(l_Lake_getUrl___closed__0));
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_array_get_size(x_2);
x_46 = lean_nat_dec_lt(x_44, x_45);
if (x_46 == 0)
{
x_5 = x_43;
goto block_42;
}
else
{
uint8_t x_47; 
x_47 = lean_nat_dec_le(x_45, x_45);
if (x_47 == 0)
{
if (x_46 == 0)
{
x_5 = x_43;
goto block_42;
}
else
{
size_t x_48; size_t x_49; lean_object* x_50; 
x_48 = 0;
x_49 = lean_usize_of_nat(x_45);
x_50 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1(x_2, x_48, x_49, x_43);
x_5 = x_50;
goto block_42;
}
}
else
{
size_t x_51; size_t x_52; lean_object* x_53; 
x_51 = 0;
x_52 = lean_usize_of_nat(x_45);
x_53 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getUrl_x3f_spec__1(x_2, x_51, x_52, x_43);
x_5 = x_53;
goto block_42;
}
}
block_42:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_6 = ((lean_object*)(l_Lake_getUrl_x3f___closed__8));
x_7 = ((lean_object*)(l_Lake_getUrl_x3f___closed__9));
x_8 = lean_array_push(x_5, x_1);
x_9 = lean_box(0);
x_10 = lean_unsigned_to_nat(0u);
x_11 = ((lean_object*)(l_Lake_getUrl_x3f___closed__10));
x_12 = 1;
x_13 = 0;
x_14 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_7);
lean_ctor_set(x_14, 2, x_8);
lean_ctor_set(x_14, 3, x_9);
lean_ctor_set(x_14, 4, x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*5, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*5 + 1, x_13);
x_15 = l_Lake_captureProc_x27(x_14, x_3);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_32; 
x_16 = lean_ctor_get(x_15, 0);
x_17 = lean_ctor_get(x_15, 1);
x_32 = !lean_is_exclusive(x_15);
if (x_32 == 0)
{
x_18 = x_15;
x_19 = x_32;
goto block_31;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_20);
lean_dec(x_16);
x_21 = lean_string_utf8_byte_size(x_20);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_10);
lean_ctor_set(x_22, 2, x_21);
x_23 = l_String_Slice_trimAscii(x_22);
lean_dec_ref(x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 2);
lean_inc(x_26);
lean_dec_ref(x_23);
x_27 = lean_string_utf8_extract(x_24, x_25, x_26);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_27);
x_28 = x_18;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_17);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_41; 
x_33 = lean_ctor_get(x_15, 0);
x_34 = lean_ctor_get(x_15, 1);
x_41 = !lean_is_exclusive(x_15);
if (x_41 == 0)
{
x_35 = x_15;
x_36 = x_41;
goto block_40;
}
else
{
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_15);
x_35 = lean_box(0);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; 
if (x_36 == 0)
{
x_37 = x_35;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_34);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getUrl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_getUrl(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_5;
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
res = runtime_initialize_Lake_Util_Log(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_JsonObject(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Proc(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_TacticsExtra(builtin)
;
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
res = initialize_Lake_Util_Log(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_JsonObject(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Proc(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Url(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_Url(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_Url(builtin);
}
#ifdef __cplusplus
}
#endif

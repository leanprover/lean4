// Lean compiler output
// Module: Std.Internal.Parsec.String
// Imports: public import Std.Internal.Parsec.Basic public import Init.Data.String.Slice public import Init.Data.String.Termination import Init.Data.String.Length
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
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint32_t l_String_Slice_Pos_get_x21(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_next_x21(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__1(lean_object*);
LEAN_EXPORT uint32_t l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__2___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__4(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__5___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__0_value;
static const lean_closure_object l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__1_value;
static const lean_closure_object l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__2 = (const lean_object*)&l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__2_value;
static const lean_closure_object l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__3 = (const lean_object*)&l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__3_value;
static const lean_closure_object l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__4, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__4 = (const lean_object*)&l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__4_value;
static const lean_closure_object l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__5___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__5 = (const lean_object*)&l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__5_value;
static const lean_ctor_object l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__0_value),((lean_object*)&l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__1_value),((lean_object*)&l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__2_value),((lean_object*)&l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__3_value),((lean_object*)&l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__4_value),((lean_object*)&l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__5_value)}};
static const lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__6 = (const lean_object*)&l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__6_value;
LEAN_EXPORT const lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw = (const lean_object*)&l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__6_value;
static const lean_string_object l_Std_Internal_Parsec_String_Parser_run___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "offset "};
static const lean_object* l_Std_Internal_Parsec_String_Parser_run___redArg___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_String_Parser_run___redArg___closed__0_value;
static const lean_string_object l_Std_Internal_Parsec_String_Parser_run___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Std_Internal_Parsec_String_Parser_run___redArg___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_String_Parser_run___redArg___closed__1_value;
static const lean_string_object l_Std_Internal_Parsec_String_Parser_run___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "unexpected end of input"};
static const lean_object* l_Std_Internal_Parsec_String_Parser_run___redArg___closed__2 = (const lean_object*)&l_Std_Internal_Parsec_String_Parser_run___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_Parser_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_Parser_run(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_String_pstring___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "expected: "};
static const lean_object* l_Std_Internal_Parsec_String_pstring___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_String_pstring___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_pstring(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_skipString(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_String_pchar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "expected: '"};
static const lean_object* l_Std_Internal_Parsec_String_pchar___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_String_pchar___closed__0_value;
static const lean_string_object l_Std_Internal_Parsec_String_pchar___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Internal_Parsec_String_pchar___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_String_pchar___closed__1_value;
static const lean_string_object l_Std_Internal_Parsec_String_pchar___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Std_Internal_Parsec_String_pchar___closed__2 = (const lean_object*)&l_Std_Internal_Parsec_String_pchar___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_pchar(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_pchar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_skipChar(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_skipChar___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_Parsec_String_digit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "digit expected"};
static const lean_object* l_Std_Internal_Parsec_String_digit___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_String_digit___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_String_digit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_String_digit___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_String_digit___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_String_digit___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_digit(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitToNat(uint32_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitToNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_digits(lean_object*);
static const lean_string_object l_Std_Internal_Parsec_String_hexDigit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "hex digit expected"};
static const lean_object* l_Std_Internal_Parsec_String_hexDigit___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_String_hexDigit___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_String_hexDigit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_String_hexDigit___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_String_hexDigit___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_String_hexDigit___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_hexDigit(lean_object*);
static const lean_string_object l_Std_Internal_Parsec_String_asciiLetter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "ASCII letter expected"};
static const lean_object* l_Std_Internal_Parsec_String_asciiLetter___closed__0 = (const lean_object*)&l_Std_Internal_Parsec_String_asciiLetter___closed__0_value;
static const lean_ctor_object l_Std_Internal_Parsec_String_asciiLetter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_Parsec_String_asciiLetter___closed__0_value)}};
static const lean_object* l_Std_Internal_Parsec_String_asciiLetter___closed__1 = (const lean_object*)&l_Std_Internal_Parsec_String_asciiLetter___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_asciiLetter(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_ws(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__0(lean_object* v_it_1_){
_start:
{
lean_object* v_snd_2_; 
v_snd_2_ = lean_ctor_get(v_it_1_, 1);
lean_inc(v_snd_2_);
return v_snd_2_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__0___boxed(lean_object* v_it_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__0(v_it_3_);
lean_dec_ref(v_it_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__1(lean_object* v_it_5_){
_start:
{
lean_object* v_fst_6_; lean_object* v_snd_7_; lean_object* v___x_9_; uint8_t v_isShared_10_; uint8_t v_isSharedCheck_18_; 
v_fst_6_ = lean_ctor_get(v_it_5_, 0);
v_snd_7_ = lean_ctor_get(v_it_5_, 1);
v_isSharedCheck_18_ = !lean_is_exclusive(v_it_5_);
if (v_isSharedCheck_18_ == 0)
{
v___x_9_ = v_it_5_;
v_isShared_10_ = v_isSharedCheck_18_;
goto v_resetjp_8_;
}
else
{
lean_inc(v_snd_7_);
lean_inc(v_fst_6_);
lean_dec(v_it_5_);
v___x_9_ = lean_box(0);
v_isShared_10_ = v_isSharedCheck_18_;
goto v_resetjp_8_;
}
v_resetjp_8_:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_16_; 
v___x_11_ = lean_unsigned_to_nat(0u);
v___x_12_ = lean_string_utf8_byte_size(v_fst_6_);
lean_inc(v_fst_6_);
v___x_13_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_13_, 0, v_fst_6_);
lean_ctor_set(v___x_13_, 1, v___x_11_);
lean_ctor_set(v___x_13_, 2, v___x_12_);
v___x_14_ = l_String_Slice_Pos_next_x21(v___x_13_, v_snd_7_);
lean_dec(v_snd_7_);
lean_dec_ref_known(v___x_13_, 3);
if (v_isShared_10_ == 0)
{
lean_ctor_set(v___x_9_, 1, v___x_14_);
v___x_16_ = v___x_9_;
goto v_reusejp_15_;
}
else
{
lean_object* v_reuseFailAlloc_17_; 
v_reuseFailAlloc_17_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v_fst_6_);
lean_ctor_set(v_reuseFailAlloc_17_, 1, v___x_14_);
v___x_16_ = v_reuseFailAlloc_17_;
goto v_reusejp_15_;
}
v_reusejp_15_:
{
return v___x_16_;
}
}
}
}
uint32_t l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__2(lean_object* v_it_19_){
_start:
{
lean_object* v_fst_20_; lean_object* v_snd_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; uint32_t v___x_25_; 
v_fst_20_ = lean_ctor_get(v_it_19_, 0);
v_snd_21_ = lean_ctor_get(v_it_19_, 1);
v___x_22_ = lean_unsigned_to_nat(0u);
v___x_23_ = lean_string_utf8_byte_size(v_fst_20_);
lean_inc(v_fst_20_);
v___x_24_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_24_, 0, v_fst_20_);
lean_ctor_set(v___x_24_, 1, v___x_22_);
lean_ctor_set(v___x_24_, 2, v___x_23_);
v___x_25_ = l_String_Slice_Pos_get_x21(v___x_24_, v_snd_21_);
lean_dec_ref_known(v___x_24_, 3);
return v___x_25_;
}
}
LEAN_EXPORT void l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_it_19_ = stack[0].m_obj;
uint32_t v_res_26_;
v_res_26_ = l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__2(v_it_19_);
stack->m_num = v_res_26_;
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__2___boxed(lean_object* v_it_27_){
_start:
{
uint32_t v_res_28_; lean_object* v_r_29_; 
v_res_28_ = l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__2(v_it_27_);
lean_dec_ref(v_it_27_);
v_r_29_ = lean_box_uint32(v_res_28_);
return v_r_29_;
}
}
uint8_t l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__3(lean_object* v_it_30_){
_start:
{
lean_object* v_fst_31_; lean_object* v_snd_32_; lean_object* v___x_33_; uint8_t v_decide_34_; 
v_fst_31_ = lean_ctor_get(v_it_30_, 0);
v_snd_32_ = lean_ctor_get(v_it_30_, 1);
v___x_33_ = lean_string_utf8_byte_size(v_fst_31_);
v_decide_34_ = lean_nat_dec_eq(v_snd_32_, v___x_33_);
if (v_decide_34_ == 0)
{
uint8_t v___x_35_; 
v___x_35_ = 1;
return v___x_35_;
}
else
{
uint8_t v___x_36_; 
v___x_36_ = 0;
return v___x_36_;
}
}
}
LEAN_EXPORT void l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_it_30_ = stack[0].m_obj;
uint8_t v_res_37_;
v_res_37_ = l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__3(v_it_30_);
stack->m_num = v_res_37_;
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__3___boxed(lean_object* v_it_38_){
_start:
{
uint8_t v_res_39_; lean_object* v_r_40_; 
v_res_39_ = l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__3(v_it_38_);
lean_dec_ref(v_it_38_);
v_r_40_ = lean_box(v_res_39_);
return v_r_40_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__4(lean_object* v_it_41_, lean_object* v_h_42_){
_start:
{
lean_object* v_fst_43_; lean_object* v_snd_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_52_; 
v_fst_43_ = lean_ctor_get(v_it_41_, 0);
v_snd_44_ = lean_ctor_get(v_it_41_, 1);
v_isSharedCheck_52_ = !lean_is_exclusive(v_it_41_);
if (v_isSharedCheck_52_ == 0)
{
v___x_46_ = v_it_41_;
v_isShared_47_ = v_isSharedCheck_52_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_snd_44_);
lean_inc(v_fst_43_);
lean_dec(v_it_41_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_52_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v___x_48_; lean_object* v___x_50_; 
v___x_48_ = lean_string_utf8_next_fast(v_fst_43_, v_snd_44_);
lean_dec(v_snd_44_);
if (v_isShared_47_ == 0)
{
lean_ctor_set(v___x_46_, 1, v___x_48_);
v___x_50_ = v___x_46_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v_fst_43_);
lean_ctor_set(v_reuseFailAlloc_51_, 1, v___x_48_);
v___x_50_ = v_reuseFailAlloc_51_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
return v___x_50_;
}
}
}
}
uint32_t l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__5(lean_object* v_it_53_, lean_object* v_h_54_){
_start:
{
lean_object* v_fst_55_; lean_object* v_snd_56_; uint32_t v___x_57_; 
v_fst_55_ = lean_ctor_get(v_it_53_, 0);
v_snd_56_ = lean_ctor_get(v_it_53_, 1);
v___x_57_ = lean_string_utf8_get_fast(v_fst_55_, v_snd_56_);
return v___x_57_;
}
}
LEAN_EXPORT void l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_it_53_ = stack[0].m_obj;
uint32_t v_res_58_;
v_res_58_ = l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__5(v_it_53_, lean_box(0));
stack->m_num = v_res_58_;
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__5___boxed(lean_object* v_it_59_, lean_object* v_h_60_){
_start:
{
uint32_t v_res_61_; lean_object* v_r_62_; 
v_res_61_ = l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__5(v_it_59_, v_h_60_);
lean_dec_ref(v_it_59_);
v_r_62_ = lean_box_uint32(v_res_61_);
return v_r_62_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_Parser_run___redArg(lean_object* v_p_80_, lean_object* v_s_81_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_82_ = lean_unsigned_to_nat(0u);
v___x_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_83_, 0, v_s_81_);
lean_ctor_set(v___x_83_, 1, v___x_82_);
v___x_84_ = lean_apply_1(v_p_80_, v___x_83_);
if (lean_obj_tag(v___x_84_) == 0)
{
lean_object* v_res_85_; lean_object* v___x_86_; 
v_res_85_ = lean_ctor_get(v___x_84_, 1);
lean_inc(v_res_85_);
lean_dec_ref_known(v___x_84_, 2);
v___x_86_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_86_, 0, v_res_85_);
return v___x_86_;
}
else
{
lean_object* v_pos_87_; lean_object* v_err_88_; lean_object* v_snd_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___y_99_; 
v_pos_87_ = lean_ctor_get(v___x_84_, 0);
lean_inc(v_pos_87_);
v_err_88_ = lean_ctor_get(v___x_84_, 1);
lean_inc(v_err_88_);
lean_dec_ref_known(v___x_84_, 2);
v_snd_89_ = lean_ctor_get(v_pos_87_, 1);
lean_inc(v_snd_89_);
lean_dec(v_pos_87_);
v___x_90_ = ((lean_object*)(l_Std_Internal_Parsec_String_Parser_run___redArg___closed__0));
v___x_91_ = l_Nat_reprFast(v_snd_89_);
v___x_92_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
v___x_93_ = l_Std_Format_defWidth;
v___x_94_ = l_Std_Format_pretty(v___x_92_, v___x_93_, v___x_82_, v___x_82_);
v___x_95_ = lean_string_append(v___x_90_, v___x_94_);
lean_dec_ref(v___x_94_);
v___x_96_ = ((lean_object*)(l_Std_Internal_Parsec_String_Parser_run___redArg___closed__1));
v___x_97_ = lean_string_append(v___x_95_, v___x_96_);
if (lean_obj_tag(v_err_88_) == 0)
{
lean_object* v___x_102_; 
v___x_102_ = ((lean_object*)(l_Std_Internal_Parsec_String_Parser_run___redArg___closed__2));
v___y_99_ = v___x_102_;
goto v___jp_98_;
}
else
{
lean_object* v_s_103_; 
v_s_103_ = lean_ctor_get(v_err_88_, 0);
lean_inc_ref(v_s_103_);
lean_dec_ref_known(v_err_88_, 1);
v___y_99_ = v_s_103_;
goto v___jp_98_;
}
v___jp_98_:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = lean_string_append(v___x_97_, v___y_99_);
lean_dec_ref(v___y_99_);
v___x_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
return v___x_101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_Parser_run(lean_object* v_00_u03b1_104_, lean_object* v_p_105_, lean_object* v_s_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v_p_105_, v_s_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_pstring(lean_object* v_s_109_, lean_object* v_it_110_){
_start:
{
lean_object* v_fst_116_; lean_object* v_snd_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v_fst_116_ = lean_ctor_get(v_it_110_, 0);
v_snd_117_ = lean_ctor_get(v_it_110_, 1);
v___x_118_ = lean_string_utf8_byte_size(v_fst_116_);
v___x_119_ = lean_string_utf8_byte_size(v_s_109_);
v___x_120_ = lean_nat_sub(v___x_118_, v_snd_117_);
v___x_121_ = lean_nat_dec_le(v___x_119_, v___x_120_);
lean_dec(v___x_120_);
if (v___x_121_ == 0)
{
goto v___jp_111_;
}
else
{
lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = lean_string_memcmp(v_fst_116_, v_s_109_, v_snd_117_, v___x_122_, v___x_119_);
if (v___x_123_ == 0)
{
goto v___jp_111_;
}
else
{
lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_134_; 
lean_inc(v_snd_117_);
lean_inc(v_fst_116_);
v_isSharedCheck_134_ = !lean_is_exclusive(v_it_110_);
if (v_isSharedCheck_134_ == 0)
{
lean_object* v_unused_135_; lean_object* v_unused_136_; 
v_unused_135_ = lean_ctor_get(v_it_110_, 1);
lean_dec(v_unused_135_);
v_unused_136_ = lean_ctor_get(v_it_110_, 0);
lean_dec(v_unused_136_);
v___x_125_ = v_it_110_;
v_isShared_126_ = v_isSharedCheck_134_;
goto v_resetjp_124_;
}
else
{
lean_dec(v_it_110_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_134_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_131_; 
v___x_127_ = lean_string_length(v_s_109_);
lean_inc(v_fst_116_);
v___x_128_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_128_, 0, v_fst_116_);
lean_ctor_set(v___x_128_, 1, v___x_122_);
lean_ctor_set(v___x_128_, 2, v___x_118_);
v___x_129_ = l_String_Slice_Pos_nextn(v___x_128_, v_snd_117_, v___x_127_);
lean_dec_ref_known(v___x_128_, 3);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 1, v___x_129_);
v___x_131_ = v___x_125_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_fst_116_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v___x_129_);
v___x_131_ = v_reuseFailAlloc_133_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
lean_object* v___x_132_; 
v___x_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v_s_109_);
return v___x_132_;
}
}
}
}
v___jp_111_:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_112_ = ((lean_object*)(l_Std_Internal_Parsec_String_pstring___closed__0));
v___x_113_ = lean_string_append(v___x_112_, v_s_109_);
lean_dec_ref(v_s_109_);
v___x_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
v___x_115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_115_, 0, v_it_110_);
lean_ctor_set(v___x_115_, 1, v___x_114_);
return v___x_115_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_skipString(lean_object* v_s_137_, lean_object* v_a_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Std_Internal_Parsec_String_pstring(v_s_137_, v_a_138_);
if (lean_obj_tag(v___x_139_) == 0)
{
lean_object* v_pos_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_148_; 
v_pos_140_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_148_ == 0)
{
lean_object* v_unused_149_; 
v_unused_149_ = lean_ctor_get(v___x_139_, 1);
lean_dec(v_unused_149_);
v___x_142_ = v___x_139_;
v_isShared_143_ = v_isSharedCheck_148_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_pos_140_);
lean_dec(v___x_139_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_148_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_144_; lean_object* v___x_146_; 
v___x_144_ = lean_box(0);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 1, v___x_144_);
v___x_146_ = v___x_142_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_pos_140_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v___x_144_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
else
{
lean_object* v_pos_150_; lean_object* v_err_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_158_; 
v_pos_150_ = lean_ctor_get(v___x_139_, 0);
v_err_151_ = lean_ctor_get(v___x_139_, 1);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_158_ == 0)
{
v___x_153_ = v___x_139_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_err_151_);
lean_inc(v_pos_150_);
lean_dec(v___x_139_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_pos_150_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_err_151_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
}
lean_object* l_Std_Internal_Parsec_String_pchar(uint32_t v_c_162_, lean_object* v_a_163_){
_start:
{
lean_object* v_fst_164_; lean_object* v_snd_165_; lean_object* v___x_166_; uint8_t v_decide_167_; 
v_fst_164_ = lean_ctor_get(v_a_163_, 0);
v_snd_165_ = lean_ctor_get(v_a_163_, 1);
v___x_166_ = lean_string_utf8_byte_size(v_fst_164_);
v_decide_167_ = lean_nat_dec_eq(v_snd_165_, v___x_166_);
if (v_decide_167_ == 0)
{
uint32_t v_c_168_; uint8_t v___x_169_; 
v_c_168_ = lean_string_utf8_get_fast(v_fst_164_, v_snd_165_);
v___x_169_ = lean_uint32_dec_eq(v_c_168_, v_c_162_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_170_ = ((lean_object*)(l_Std_Internal_Parsec_String_pchar___closed__0));
v___x_171_ = ((lean_object*)(l_Std_Internal_Parsec_String_pchar___closed__1));
v___x_172_ = lean_string_push(v___x_171_, v_c_162_);
v___x_173_ = lean_string_append(v___x_170_, v___x_172_);
lean_dec_ref(v___x_172_);
v___x_174_ = ((lean_object*)(l_Std_Internal_Parsec_String_pchar___closed__2));
v___x_175_ = lean_string_append(v___x_173_, v___x_174_);
v___x_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
v___x_177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_177_, 0, v_a_163_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
return v___x_177_;
}
else
{
lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_187_; 
lean_inc(v_snd_165_);
lean_inc(v_fst_164_);
v_isSharedCheck_187_ = !lean_is_exclusive(v_a_163_);
if (v_isSharedCheck_187_ == 0)
{
lean_object* v_unused_188_; lean_object* v_unused_189_; 
v_unused_188_ = lean_ctor_get(v_a_163_, 1);
lean_dec(v_unused_188_);
v_unused_189_ = lean_ctor_get(v_a_163_, 0);
lean_dec(v_unused_189_);
v___x_179_ = v_a_163_;
v_isShared_180_ = v_isSharedCheck_187_;
goto v_resetjp_178_;
}
else
{
lean_dec(v_a_163_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_187_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_181_; lean_object* v_it_x27_183_; 
v___x_181_ = lean_string_utf8_next_fast(v_fst_164_, v_snd_165_);
lean_dec(v_snd_165_);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 1, v___x_181_);
v_it_x27_183_ = v___x_179_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_fst_164_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v___x_181_);
v_it_x27_183_ = v_reuseFailAlloc_186_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lean_box_uint32(v_c_162_);
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v_it_x27_183_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
return v___x_185_;
}
}
}
}
else
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = lean_box(0);
v___x_191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_191_, 0, v_a_163_);
lean_ctor_set(v___x_191_, 1, v___x_190_);
return v___x_191_;
}
}
}
LEAN_EXPORT void l_Std_Internal_Parsec_String_pchar_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_162_ = stack[0].m_num;
lean_object* v_a_163_ = stack[1].m_obj;
lean_object* v_res_192_;
v_res_192_ = l_Std_Internal_Parsec_String_pchar(v_c_162_, v_a_163_);
stack->m_obj
 = v_res_192_;
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_pchar___boxed(lean_object* v_c_193_, lean_object* v_a_194_){
_start:
{
uint32_t v_c_boxed_195_; lean_object* v_res_196_; 
v_c_boxed_195_ = lean_unbox_uint32(v_c_193_);
lean_dec(v_c_193_);
v_res_196_ = l_Std_Internal_Parsec_String_pchar(v_c_boxed_195_, v_a_194_);
return v_res_196_;
}
}
lean_object* l_Std_Internal_Parsec_String_skipChar(uint32_t v_c_197_, lean_object* v_a_198_){
_start:
{
lean_object* v_fst_199_; lean_object* v_snd_200_; lean_object* v___x_201_; uint8_t v_decide_202_; 
v_fst_199_ = lean_ctor_get(v_a_198_, 0);
v_snd_200_ = lean_ctor_get(v_a_198_, 1);
v___x_201_ = lean_string_utf8_byte_size(v_fst_199_);
v_decide_202_ = lean_nat_dec_eq(v_snd_200_, v___x_201_);
if (v_decide_202_ == 0)
{
uint32_t v_c_203_; uint8_t v___x_204_; 
v_c_203_ = lean_string_utf8_get_fast(v_fst_199_, v_snd_200_);
v___x_204_ = lean_uint32_dec_eq(v_c_203_, v_c_197_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_205_ = ((lean_object*)(l_Std_Internal_Parsec_String_pchar___closed__0));
v___x_206_ = ((lean_object*)(l_Std_Internal_Parsec_String_pchar___closed__1));
v___x_207_ = lean_string_push(v___x_206_, v_c_197_);
v___x_208_ = lean_string_append(v___x_205_, v___x_207_);
lean_dec_ref(v___x_207_);
v___x_209_ = ((lean_object*)(l_Std_Internal_Parsec_String_pchar___closed__2));
v___x_210_ = lean_string_append(v___x_208_, v___x_209_);
v___x_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
v___x_212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_212_, 0, v_a_198_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
return v___x_212_;
}
else
{
lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_222_; 
lean_inc(v_snd_200_);
lean_inc(v_fst_199_);
v_isSharedCheck_222_ = !lean_is_exclusive(v_a_198_);
if (v_isSharedCheck_222_ == 0)
{
lean_object* v_unused_223_; lean_object* v_unused_224_; 
v_unused_223_ = lean_ctor_get(v_a_198_, 1);
lean_dec(v_unused_223_);
v_unused_224_ = lean_ctor_get(v_a_198_, 0);
lean_dec(v_unused_224_);
v___x_214_ = v_a_198_;
v_isShared_215_ = v_isSharedCheck_222_;
goto v_resetjp_213_;
}
else
{
lean_dec(v_a_198_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_222_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_216_; lean_object* v_it_x27_218_; 
v___x_216_ = lean_string_utf8_next_fast(v_fst_199_, v_snd_200_);
lean_dec(v_snd_200_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 1, v___x_216_);
v_it_x27_218_ = v___x_214_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_fst_199_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v___x_216_);
v_it_x27_218_ = v_reuseFailAlloc_221_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = lean_box(0);
v___x_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_220_, 0, v_it_x27_218_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
return v___x_220_;
}
}
}
}
else
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = lean_box(0);
v___x_226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_226_, 0, v_a_198_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
return v___x_226_;
}
}
}
LEAN_EXPORT void l_Std_Internal_Parsec_String_skipChar_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_197_ = stack[0].m_num;
lean_object* v_a_198_ = stack[1].m_obj;
lean_object* v_res_227_;
v_res_227_ = l_Std_Internal_Parsec_String_skipChar(v_c_197_, v_a_198_);
stack->m_obj
 = v_res_227_;
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_skipChar___boxed(lean_object* v_c_228_, lean_object* v_a_229_){
_start:
{
uint32_t v_c_boxed_230_; lean_object* v_res_231_; 
v_c_boxed_230_ = lean_unbox_uint32(v_c_228_);
lean_dec(v_c_228_);
v_res_231_ = l_Std_Internal_Parsec_String_skipChar(v_c_boxed_230_, v_a_229_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_digit(lean_object* v_a_235_){
_start:
{
lean_object* v_fst_239_; lean_object* v_snd_240_; lean_object* v___x_241_; uint8_t v_decide_242_; 
v_fst_239_ = lean_ctor_get(v_a_235_, 0);
v_snd_240_ = lean_ctor_get(v_a_235_, 1);
v___x_241_ = lean_string_utf8_byte_size(v_fst_239_);
v_decide_242_ = lean_nat_dec_eq(v_snd_240_, v___x_241_);
if (v_decide_242_ == 0)
{
uint32_t v_c_243_; uint32_t v___x_244_; uint8_t v___x_245_; 
v_c_243_ = lean_string_utf8_get_fast(v_fst_239_, v_snd_240_);
v___x_244_ = 48;
v___x_245_ = lean_uint32_dec_le(v___x_244_, v_c_243_);
if (v___x_245_ == 0)
{
goto v___jp_236_;
}
else
{
uint32_t v___x_246_; uint8_t v___x_247_; 
v___x_246_ = 57;
v___x_247_ = lean_uint32_dec_le(v_c_243_, v___x_246_);
if (v___x_247_ == 0)
{
goto v___jp_236_;
}
else
{
lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_257_; 
lean_inc(v_snd_240_);
lean_inc(v_fst_239_);
v_isSharedCheck_257_ = !lean_is_exclusive(v_a_235_);
if (v_isSharedCheck_257_ == 0)
{
lean_object* v_unused_258_; lean_object* v_unused_259_; 
v_unused_258_ = lean_ctor_get(v_a_235_, 1);
lean_dec(v_unused_258_);
v_unused_259_ = lean_ctor_get(v_a_235_, 0);
lean_dec(v_unused_259_);
v___x_249_ = v_a_235_;
v_isShared_250_ = v_isSharedCheck_257_;
goto v_resetjp_248_;
}
else
{
lean_dec(v_a_235_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_257_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_251_; lean_object* v_it_x27_253_; 
v___x_251_ = lean_string_utf8_next_fast(v_fst_239_, v_snd_240_);
lean_dec(v_snd_240_);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 1, v___x_251_);
v_it_x27_253_ = v___x_249_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_fst_239_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v___x_251_);
v_it_x27_253_ = v_reuseFailAlloc_256_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_box_uint32(v_c_243_);
v___x_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_255_, 0, v_it_x27_253_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
return v___x_255_;
}
}
}
}
}
else
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_box(0);
v___x_261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_261_, 0, v_a_235_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
return v___x_261_;
}
v___jp_236_:
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = ((lean_object*)(l_Std_Internal_Parsec_String_digit___closed__1));
v___x_238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_238_, 0, v_a_235_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
return v___x_238_;
}
}
}
lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitToNat(uint32_t v_b_262_){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_263_ = lean_uint32_to_nat(v_b_262_);
v___x_264_ = lean_unsigned_to_nat(48u);
v___x_265_ = lean_nat_sub(v___x_263_, v___x_264_);
lean_dec(v___x_263_);
return v___x_265_;
}
}
LEAN_EXPORT void l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitToNat_0interp(lean_interpreter_value* stack)
{
uint32_t v_b_262_ = stack[0].m_num;
lean_object* v_res_266_;
v_res_266_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitToNat(v_b_262_);
stack->m_obj
 = v_res_266_;
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitToNat___boxed(lean_object* v_b_267_){
_start:
{
uint32_t v_b_boxed_268_; lean_object* v_res_269_; 
v_b_boxed_268_ = lean_unbox_uint32(v_b_267_);
lean_dec(v_b_267_);
v_res_269_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitToNat(v_b_boxed_268_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(lean_object* v_s_270_, lean_object* v_it_271_, lean_object* v_acc_272_){
_start:
{
lean_object* v___x_273_; uint8_t v_decide_274_; 
v___x_273_ = lean_string_utf8_byte_size(v_s_270_);
v_decide_274_ = lean_nat_dec_eq(v_it_271_, v___x_273_);
if (v_decide_274_ == 0)
{
uint32_t v_candidate_275_; uint32_t v___x_276_; uint8_t v___x_277_; 
v_candidate_275_ = lean_string_utf8_get_fast(v_s_270_, v_it_271_);
v___x_276_ = 48;
v___x_277_ = lean_uint32_dec_le(v___x_276_, v_candidate_275_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; 
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v_acc_272_);
lean_ctor_set(v___x_278_, 1, v_it_271_);
return v___x_278_;
}
else
{
uint32_t v___x_279_; uint8_t v___x_280_; 
v___x_279_ = 57;
v___x_280_ = lean_uint32_dec_le(v_candidate_275_, v___x_279_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; 
v___x_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_281_, 0, v_acc_272_);
lean_ctor_set(v___x_281_, 1, v_it_271_);
return v___x_281_;
}
else
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v_digit_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v_acc_287_; lean_object* v___x_288_; 
v___x_282_ = lean_uint32_to_nat(v_candidate_275_);
v___x_283_ = lean_unsigned_to_nat(48u);
v_digit_284_ = lean_nat_sub(v___x_282_, v___x_283_);
lean_dec(v___x_282_);
v___x_285_ = lean_unsigned_to_nat(10u);
v___x_286_ = lean_nat_mul(v_acc_272_, v___x_285_);
lean_dec(v_acc_272_);
v_acc_287_ = lean_nat_add(v___x_286_, v_digit_284_);
lean_dec(v_digit_284_);
lean_dec(v___x_286_);
v___x_288_ = lean_string_utf8_next_fast(v_s_270_, v_it_271_);
lean_dec(v_it_271_);
v_it_271_ = v___x_288_;
v_acc_272_ = v_acc_287_;
goto _start;
}
}
}
else
{
lean_object* v___x_290_; 
v___x_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_290_, 0, v_acc_272_);
lean_ctor_set(v___x_290_, 1, v_it_271_);
return v___x_290_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go___boxed(lean_object* v_s_291_, lean_object* v_it_292_, lean_object* v_acc_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(v_s_291_, v_it_292_, v_acc_293_);
lean_dec_ref(v_s_291_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore(lean_object* v_acc_295_, lean_object* v_it_296_){
_start:
{
lean_object* v_fst_297_; lean_object* v_snd_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_315_; 
v_fst_297_ = lean_ctor_get(v_it_296_, 0);
v_snd_298_ = lean_ctor_get(v_it_296_, 1);
v_isSharedCheck_315_ = !lean_is_exclusive(v_it_296_);
if (v_isSharedCheck_315_ == 0)
{
v___x_300_ = v_it_296_;
v_isShared_301_ = v_isSharedCheck_315_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_snd_298_);
lean_inc(v_fst_297_);
lean_dec(v_it_296_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_315_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_302_; lean_object* v_fst_303_; lean_object* v_snd_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_314_; 
v___x_302_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(v_fst_297_, v_snd_298_, v_acc_295_);
v_fst_303_ = lean_ctor_get(v___x_302_, 0);
v_snd_304_ = lean_ctor_get(v___x_302_, 1);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_314_ == 0)
{
v___x_306_ = v___x_302_;
v_isShared_307_ = v_isSharedCheck_314_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_snd_304_);
lean_inc(v_fst_303_);
lean_dec(v___x_302_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_314_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 1, v_snd_304_);
v___x_309_ = v___x_300_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_fst_297_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_snd_304_);
v___x_309_ = v_reuseFailAlloc_313_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_311_; 
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 1, v_fst_303_);
lean_ctor_set(v___x_306_, 0, v___x_309_);
v___x_311_ = v___x_306_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_309_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_fst_303_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_digits(lean_object* v_a_316_){
_start:
{
lean_object* v_fst_320_; lean_object* v_snd_321_; lean_object* v___x_322_; uint8_t v_decide_323_; 
v_fst_320_ = lean_ctor_get(v_a_316_, 0);
v_snd_321_ = lean_ctor_get(v_a_316_, 1);
v___x_322_ = lean_string_utf8_byte_size(v_fst_320_);
v_decide_323_ = lean_nat_dec_eq(v_snd_321_, v___x_322_);
if (v_decide_323_ == 0)
{
uint32_t v_c_324_; uint32_t v___x_325_; uint8_t v___x_326_; 
v_c_324_ = lean_string_utf8_get_fast(v_fst_320_, v_snd_321_);
v___x_325_ = 48;
v___x_326_ = lean_uint32_dec_le(v___x_325_, v_c_324_);
if (v___x_326_ == 0)
{
goto v___jp_317_;
}
else
{
uint32_t v___x_327_; uint8_t v___x_328_; 
v___x_327_ = 57;
v___x_328_ = lean_uint32_dec_le(v_c_324_, v___x_327_);
if (v___x_328_ == 0)
{
goto v___jp_317_;
}
else
{
lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_349_; 
lean_inc(v_snd_321_);
lean_inc(v_fst_320_);
v_isSharedCheck_349_ = !lean_is_exclusive(v_a_316_);
if (v_isSharedCheck_349_ == 0)
{
lean_object* v_unused_350_; lean_object* v_unused_351_; 
v_unused_350_ = lean_ctor_get(v_a_316_, 1);
lean_dec(v_unused_350_);
v_unused_351_ = lean_ctor_get(v_a_316_, 0);
lean_dec(v_unused_351_);
v___x_330_ = v_a_316_;
v_isShared_331_ = v_isSharedCheck_349_;
goto v_resetjp_329_;
}
else
{
lean_dec(v_a_316_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_349_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v_fst_337_; lean_object* v_snd_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_348_; 
v___x_332_ = lean_string_utf8_next_fast(v_fst_320_, v_snd_321_);
lean_dec(v_snd_321_);
v___x_333_ = lean_uint32_to_nat(v_c_324_);
v___x_334_ = lean_unsigned_to_nat(48u);
v___x_335_ = lean_nat_sub(v___x_333_, v___x_334_);
lean_dec(v___x_333_);
v___x_336_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(v_fst_320_, v___x_332_, v___x_335_);
v_fst_337_ = lean_ctor_get(v___x_336_, 0);
v_snd_338_ = lean_ctor_get(v___x_336_, 1);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_348_ == 0)
{
v___x_340_ = v___x_336_;
v_isShared_341_ = v_isSharedCheck_348_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_snd_338_);
lean_inc(v_fst_337_);
lean_dec(v___x_336_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_348_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 1, v_snd_338_);
v___x_343_ = v___x_330_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_fst_320_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_snd_338_);
v___x_343_ = v_reuseFailAlloc_347_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_345_; 
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 1, v_fst_337_);
lean_ctor_set(v___x_340_, 0, v___x_343_);
v___x_345_ = v___x_340_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_fst_337_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_box(0);
v___x_353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_353_, 0, v_a_316_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
return v___x_353_;
}
v___jp_317_:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = ((lean_object*)(l_Std_Internal_Parsec_String_digit___closed__1));
v___x_319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_319_, 0, v_a_316_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
return v___x_319_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_hexDigit(lean_object* v_a_357_){
_start:
{
lean_object* v_fst_361_; lean_object* v_snd_362_; lean_object* v___x_363_; uint8_t v_decide_364_; 
v_fst_361_ = lean_ctor_get(v_a_357_, 0);
v_snd_362_ = lean_ctor_get(v_a_357_, 1);
v___x_363_ = lean_string_utf8_byte_size(v_fst_361_);
v_decide_364_ = lean_nat_dec_eq(v_snd_362_, v___x_363_);
if (v_decide_364_ == 0)
{
uint32_t v_c_365_; lean_object* v___x_366_; lean_object* v_it_x27_367_; lean_object* v___x_368_; lean_object* v___x_369_; uint32_t v___x_380_; uint8_t v___x_381_; 
v_c_365_ = lean_string_utf8_get_fast(v_fst_361_, v_snd_362_);
v___x_366_ = lean_string_utf8_next_fast(v_fst_361_, v_snd_362_);
lean_inc(v_fst_361_);
v_it_x27_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_367_, 0, v_fst_361_);
lean_ctor_set(v_it_x27_367_, 1, v___x_366_);
v___x_368_ = lean_box_uint32(v_c_365_);
v___x_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_369_, 0, v_it_x27_367_);
lean_ctor_set(v___x_369_, 1, v___x_368_);
v___x_380_ = 48;
v___x_381_ = lean_uint32_dec_le(v___x_380_, v_c_365_);
if (v___x_381_ == 0)
{
goto v___jp_375_;
}
else
{
uint32_t v___x_382_; uint8_t v___x_383_; 
v___x_382_ = 57;
v___x_383_ = lean_uint32_dec_le(v_c_365_, v___x_382_);
if (v___x_383_ == 0)
{
goto v___jp_375_;
}
else
{
lean_dec_ref(v_a_357_);
return v___x_369_;
}
}
v___jp_370_:
{
uint32_t v___x_371_; uint8_t v___x_372_; 
v___x_371_ = 65;
v___x_372_ = lean_uint32_dec_le(v___x_371_, v_c_365_);
if (v___x_372_ == 0)
{
lean_dec_ref_known(v___x_369_, 2);
goto v___jp_358_;
}
else
{
uint32_t v___x_373_; uint8_t v___x_374_; 
v___x_373_ = 70;
v___x_374_ = lean_uint32_dec_le(v_c_365_, v___x_373_);
if (v___x_374_ == 0)
{
lean_dec_ref_known(v___x_369_, 2);
goto v___jp_358_;
}
else
{
lean_dec_ref(v_a_357_);
return v___x_369_;
}
}
}
v___jp_375_:
{
uint32_t v___x_376_; uint8_t v___x_377_; 
v___x_376_ = 97;
v___x_377_ = lean_uint32_dec_le(v___x_376_, v_c_365_);
if (v___x_377_ == 0)
{
goto v___jp_370_;
}
else
{
uint32_t v___x_378_; uint8_t v___x_379_; 
v___x_378_ = 102;
v___x_379_ = lean_uint32_dec_le(v_c_365_, v___x_378_);
if (v___x_379_ == 0)
{
goto v___jp_370_;
}
else
{
lean_dec_ref(v_a_357_);
return v___x_369_;
}
}
}
}
else
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = lean_box(0);
v___x_385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_385_, 0, v_a_357_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
return v___x_385_;
}
v___jp_358_:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = ((lean_object*)(l_Std_Internal_Parsec_String_hexDigit___closed__1));
v___x_360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_360_, 0, v_a_357_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
return v___x_360_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_asciiLetter(lean_object* v_a_389_){
_start:
{
lean_object* v_fst_393_; lean_object* v_snd_394_; lean_object* v___x_395_; uint8_t v_decide_396_; 
v_fst_393_ = lean_ctor_get(v_a_389_, 0);
v_snd_394_ = lean_ctor_get(v_a_389_, 1);
v___x_395_ = lean_string_utf8_byte_size(v_fst_393_);
v_decide_396_ = lean_nat_dec_eq(v_snd_394_, v___x_395_);
if (v_decide_396_ == 0)
{
uint32_t v_c_397_; lean_object* v___x_398_; lean_object* v_it_x27_399_; lean_object* v___x_400_; lean_object* v___x_401_; uint32_t v___x_407_; uint8_t v___x_408_; 
v_c_397_ = lean_string_utf8_get_fast(v_fst_393_, v_snd_394_);
v___x_398_ = lean_string_utf8_next_fast(v_fst_393_, v_snd_394_);
lean_inc(v_fst_393_);
v_it_x27_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_399_, 0, v_fst_393_);
lean_ctor_set(v_it_x27_399_, 1, v___x_398_);
v___x_400_ = lean_box_uint32(v_c_397_);
v___x_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_401_, 0, v_it_x27_399_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
v___x_407_ = 65;
v___x_408_ = lean_uint32_dec_le(v___x_407_, v_c_397_);
if (v___x_408_ == 0)
{
goto v___jp_402_;
}
else
{
uint32_t v___x_409_; uint8_t v___x_410_; 
v___x_409_ = 90;
v___x_410_ = lean_uint32_dec_le(v_c_397_, v___x_409_);
if (v___x_410_ == 0)
{
goto v___jp_402_;
}
else
{
lean_dec_ref(v_a_389_);
return v___x_401_;
}
}
v___jp_402_:
{
uint32_t v___x_403_; uint8_t v___x_404_; 
v___x_403_ = 97;
v___x_404_ = lean_uint32_dec_le(v___x_403_, v_c_397_);
if (v___x_404_ == 0)
{
lean_dec_ref_known(v___x_401_, 2);
goto v___jp_390_;
}
else
{
uint32_t v___x_405_; uint8_t v___x_406_; 
v___x_405_ = 122;
v___x_406_ = lean_uint32_dec_le(v_c_397_, v___x_405_);
if (v___x_406_ == 0)
{
lean_dec_ref_known(v___x_401_, 2);
goto v___jp_390_;
}
else
{
lean_dec_ref(v_a_389_);
return v___x_401_;
}
}
}
}
else
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = lean_box(0);
v___x_412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_412_, 0, v_a_389_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
return v___x_412_;
}
v___jp_390_:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = ((lean_object*)(l_Std_Internal_Parsec_String_asciiLetter___closed__1));
v___x_392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_392_, 0, v_a_389_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
return v___x_392_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(lean_object* v_s_413_, lean_object* v_it_414_){
_start:
{
lean_object* v___x_418_; uint8_t v_decide_419_; 
v___x_418_ = lean_string_utf8_byte_size(v_s_413_);
v_decide_419_ = lean_nat_dec_eq(v_it_414_, v___x_418_);
if (v_decide_419_ == 0)
{
uint32_t v_c_420_; uint32_t v___x_421_; uint8_t v___x_422_; 
v_c_420_ = lean_string_utf8_get_fast(v_s_413_, v_it_414_);
v___x_421_ = 9;
v___x_422_ = lean_uint32_dec_eq(v_c_420_, v___x_421_);
if (v___x_422_ == 0)
{
uint32_t v___x_423_; uint8_t v___x_424_; 
v___x_423_ = 10;
v___x_424_ = lean_uint32_dec_eq(v_c_420_, v___x_423_);
if (v___x_424_ == 0)
{
uint32_t v___x_425_; uint8_t v___x_426_; 
v___x_425_ = 13;
v___x_426_ = lean_uint32_dec_eq(v_c_420_, v___x_425_);
if (v___x_426_ == 0)
{
uint32_t v___x_427_; uint8_t v___x_428_; 
v___x_427_ = 32;
v___x_428_ = lean_uint32_dec_eq(v_c_420_, v___x_427_);
if (v___x_428_ == 0)
{
return v_it_414_;
}
else
{
goto v___jp_415_;
}
}
else
{
goto v___jp_415_;
}
}
else
{
goto v___jp_415_;
}
}
else
{
goto v___jp_415_;
}
}
else
{
return v_it_414_;
}
v___jp_415_:
{
lean_object* v___x_416_; 
v___x_416_ = lean_string_utf8_next_fast(v_s_413_, v_it_414_);
lean_dec(v_it_414_);
v_it_414_ = v___x_416_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs___boxed(lean_object* v_s_429_, lean_object* v_it_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_s_429_, v_it_430_);
lean_dec_ref(v_s_429_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_ws(lean_object* v_it_432_){
_start:
{
lean_object* v_fst_433_; lean_object* v_snd_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_444_; 
v_fst_433_ = lean_ctor_get(v_it_432_, 0);
v_snd_434_ = lean_ctor_get(v_it_432_, 1);
v_isSharedCheck_444_ = !lean_is_exclusive(v_it_432_);
if (v_isSharedCheck_444_ == 0)
{
v___x_436_ = v_it_432_;
v_isShared_437_ = v_isSharedCheck_444_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_snd_434_);
lean_inc(v_fst_433_);
lean_dec(v_it_432_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_444_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; lean_object* v___x_440_; 
v___x_438_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_433_, v_snd_434_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 1, v___x_438_);
v___x_440_ = v___x_436_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_fst_433_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v___x_438_);
v___x_440_ = v_reuseFailAlloc_443_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_box(0);
v___x_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_440_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
return v___x_442_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_take(lean_object* v_n_445_, lean_object* v_it_446_){
_start:
{
lean_object* v_fst_447_; lean_object* v_snd_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v_right_452_; lean_object* v_substr_453_; lean_object* v___x_454_; uint8_t v___x_455_; 
v_fst_447_ = lean_ctor_get(v_it_446_, 0);
v_snd_448_ = lean_ctor_get(v_it_446_, 1);
v___x_449_ = lean_unsigned_to_nat(0u);
v___x_450_ = lean_string_utf8_byte_size(v_fst_447_);
lean_inc(v_fst_447_);
v___x_451_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_451_, 0, v_fst_447_);
lean_ctor_set(v___x_451_, 1, v___x_449_);
lean_ctor_set(v___x_451_, 2, v___x_450_);
lean_inc(v_n_445_);
lean_inc(v_snd_448_);
v_right_452_ = l_String_Slice_Pos_nextn(v___x_451_, v_snd_448_, v_n_445_);
lean_dec_ref_known(v___x_451_, 3);
v_substr_453_ = lean_string_utf8_extract_fast(v_fst_447_, v_snd_448_, v_right_452_);
v___x_454_ = lean_string_length(v_substr_453_);
v___x_455_ = lean_nat_dec_eq(v___x_454_, v_n_445_);
lean_dec(v_n_445_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; lean_object* v___x_457_; 
lean_dec_ref(v_substr_453_);
lean_dec(v_right_452_);
v___x_456_ = lean_box(0);
v___x_457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_457_, 0, v_it_446_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
return v___x_457_;
}
else
{
lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_465_; 
lean_inc(v_fst_447_);
v_isSharedCheck_465_ = !lean_is_exclusive(v_it_446_);
if (v_isSharedCheck_465_ == 0)
{
lean_object* v_unused_466_; lean_object* v_unused_467_; 
v_unused_466_ = lean_ctor_get(v_it_446_, 1);
lean_dec(v_unused_466_);
v_unused_467_ = lean_ctor_get(v_it_446_, 0);
lean_dec(v_unused_467_);
v___x_459_ = v_it_446_;
v_isShared_460_ = v_isSharedCheck_465_;
goto v_resetjp_458_;
}
else
{
lean_dec(v_it_446_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_465_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 1, v_right_452_);
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_fst_447_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_right_452_);
v___x_462_ = v_reuseFailAlloc_464_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
lean_object* v___x_463_; 
v___x_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
lean_ctor_set(v___x_463_, 1, v_substr_453_);
return v___x_463_;
}
}
}
}
}
lean_object* runtime_initialize_Std_Internal_Parsec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Length(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Parsec_String(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Internal_Parsec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Parsec_String(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Internal_Parsec_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* initialize_Init_Data_String_Length(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Parsec_String(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Parsec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Parsec_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Parsec_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Parsec_String(builtin);
}
#ifdef __cplusplus
}
#endif

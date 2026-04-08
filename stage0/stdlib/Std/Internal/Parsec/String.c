// Lean compiler output
// Module: Std.Internal.Parsec.String
// Imports: public import Std.Internal.Parsec.Basic public import Init.Data.String.Slice public import Init.Data.String.Termination
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___x_13_);
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
LEAN_EXPORT uint32_t l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__2(lean_object* v_it_19_){
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
lean_dec_ref(v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__2___boxed(lean_object* v_it_26_){
_start:
{
uint32_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__2(v_it_26_);
lean_dec_ref(v_it_26_);
v_r_28_ = lean_box_uint32(v_res_27_);
return v_r_28_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__3(lean_object* v_it_29_){
_start:
{
lean_object* v_fst_30_; lean_object* v_snd_31_; lean_object* v___x_32_; uint8_t v___x_33_; 
v_fst_30_ = lean_ctor_get(v_it_29_, 0);
v_snd_31_ = lean_ctor_get(v_it_29_, 1);
v___x_32_ = lean_string_utf8_byte_size(v_fst_30_);
v___x_33_ = lean_nat_dec_eq(v_snd_31_, v___x_32_);
if (v___x_33_ == 0)
{
uint8_t v___x_34_; 
v___x_34_ = 1;
return v___x_34_;
}
else
{
uint8_t v___x_35_; 
v___x_35_ = 0;
return v___x_35_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__3___boxed(lean_object* v_it_36_){
_start:
{
uint8_t v_res_37_; lean_object* v_r_38_; 
v_res_37_ = l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__3(v_it_36_);
lean_dec_ref(v_it_36_);
v_r_38_ = lean_box(v_res_37_);
return v_r_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__4(lean_object* v_it_39_, lean_object* v_h_40_){
_start:
{
lean_object* v_fst_41_; lean_object* v_snd_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_50_; 
v_fst_41_ = lean_ctor_get(v_it_39_, 0);
v_snd_42_ = lean_ctor_get(v_it_39_, 1);
v_isSharedCheck_50_ = !lean_is_exclusive(v_it_39_);
if (v_isSharedCheck_50_ == 0)
{
v___x_44_ = v_it_39_;
v_isShared_45_ = v_isSharedCheck_50_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_snd_42_);
lean_inc(v_fst_41_);
lean_dec(v_it_39_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_50_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_46_; lean_object* v___x_48_; 
v___x_46_ = lean_string_utf8_next_fast(v_fst_41_, v_snd_42_);
lean_dec(v_snd_42_);
if (v_isShared_45_ == 0)
{
lean_ctor_set(v___x_44_, 1, v___x_46_);
v___x_48_ = v___x_44_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_fst_41_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v___x_46_);
v___x_48_ = v_reuseFailAlloc_49_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
return v___x_48_;
}
}
}
}
LEAN_EXPORT uint32_t l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__5(lean_object* v_it_51_, lean_object* v_h_52_){
_start:
{
lean_object* v_fst_53_; lean_object* v_snd_54_; uint32_t v___x_55_; 
v_fst_53_ = lean_ctor_get(v_it_51_, 0);
v_snd_54_ = lean_ctor_get(v_it_51_, 1);
v___x_55_ = lean_string_utf8_get_fast(v_fst_53_, v_snd_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__5___boxed(lean_object* v_it_56_, lean_object* v_h_57_){
_start:
{
uint32_t v_res_58_; lean_object* v_r_59_; 
v_res_58_ = l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__5(v_it_56_, v_h_57_);
lean_dec_ref(v_it_56_);
v_r_59_ = lean_box_uint32(v_res_58_);
return v_r_59_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_Parser_run___redArg(lean_object* v_p_77_, lean_object* v_s_78_){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = lean_unsigned_to_nat(0u);
v___x_80_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_80_, 0, v_s_78_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
v___x_81_ = lean_apply_1(v_p_77_, v___x_80_);
if (lean_obj_tag(v___x_81_) == 0)
{
lean_object* v_res_82_; lean_object* v___x_83_; 
v_res_82_ = lean_ctor_get(v___x_81_, 1);
lean_inc(v_res_82_);
lean_dec_ref(v___x_81_);
v___x_83_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_83_, 0, v_res_82_);
return v___x_83_;
}
else
{
lean_object* v_pos_84_; lean_object* v_err_85_; lean_object* v_snd_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___y_96_; 
v_pos_84_ = lean_ctor_get(v___x_81_, 0);
lean_inc(v_pos_84_);
v_err_85_ = lean_ctor_get(v___x_81_, 1);
lean_inc(v_err_85_);
lean_dec_ref(v___x_81_);
v_snd_86_ = lean_ctor_get(v_pos_84_, 1);
lean_inc(v_snd_86_);
lean_dec(v_pos_84_);
v___x_87_ = ((lean_object*)(l_Std_Internal_Parsec_String_Parser_run___redArg___closed__0));
v___x_88_ = l_Nat_reprFast(v_snd_86_);
v___x_89_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
v___x_90_ = l_Std_Format_defWidth;
v___x_91_ = l_Std_Format_pretty(v___x_89_, v___x_90_, v___x_79_, v___x_79_);
v___x_92_ = lean_string_append(v___x_87_, v___x_91_);
lean_dec_ref(v___x_91_);
v___x_93_ = ((lean_object*)(l_Std_Internal_Parsec_String_Parser_run___redArg___closed__1));
v___x_94_ = lean_string_append(v___x_92_, v___x_93_);
if (lean_obj_tag(v_err_85_) == 0)
{
lean_object* v___x_99_; 
v___x_99_ = ((lean_object*)(l_Std_Internal_Parsec_String_Parser_run___redArg___closed__2));
v___y_96_ = v___x_99_;
goto v___jp_95_;
}
else
{
lean_object* v_s_100_; 
v_s_100_ = lean_ctor_get(v_err_85_, 0);
lean_inc_ref(v_s_100_);
lean_dec_ref(v_err_85_);
v___y_96_ = v_s_100_;
goto v___jp_95_;
}
v___jp_95_:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_string_append(v___x_94_, v___y_96_);
lean_dec_ref(v___y_96_);
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
return v___x_98_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_Parser_run(lean_object* v_00_u03b1_101_, lean_object* v_p_102_, lean_object* v_s_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v_p_102_, v_s_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_pstring(lean_object* v_s_106_, lean_object* v_it_107_){
_start:
{
lean_object* v_fst_113_; lean_object* v_snd_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v_fst_113_ = lean_ctor_get(v_it_107_, 0);
v_snd_114_ = lean_ctor_get(v_it_107_, 1);
v___x_115_ = lean_string_utf8_byte_size(v_fst_113_);
v___x_116_ = lean_string_utf8_byte_size(v_s_106_);
v___x_117_ = lean_nat_sub(v___x_115_, v_snd_114_);
v___x_118_ = lean_nat_dec_le(v___x_116_, v___x_117_);
lean_dec(v___x_117_);
if (v___x_118_ == 0)
{
goto v___jp_108_;
}
else
{
lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_119_ = lean_unsigned_to_nat(0u);
v___x_120_ = lean_string_memcmp(v_fst_113_, v_s_106_, v_snd_114_, v___x_119_, v___x_116_);
if (v___x_120_ == 0)
{
goto v___jp_108_;
}
else
{
lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_131_; 
lean_inc(v_snd_114_);
lean_inc(v_fst_113_);
v_isSharedCheck_131_ = !lean_is_exclusive(v_it_107_);
if (v_isSharedCheck_131_ == 0)
{
lean_object* v_unused_132_; lean_object* v_unused_133_; 
v_unused_132_ = lean_ctor_get(v_it_107_, 1);
lean_dec(v_unused_132_);
v_unused_133_ = lean_ctor_get(v_it_107_, 0);
lean_dec(v_unused_133_);
v___x_122_ = v_it_107_;
v_isShared_123_ = v_isSharedCheck_131_;
goto v_resetjp_121_;
}
else
{
lean_dec(v_it_107_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_131_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_128_; 
v___x_124_ = lean_string_length(v_s_106_);
lean_inc(v_fst_113_);
v___x_125_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_125_, 0, v_fst_113_);
lean_ctor_set(v___x_125_, 1, v___x_119_);
lean_ctor_set(v___x_125_, 2, v___x_115_);
v___x_126_ = l_String_Slice_Pos_nextn(v___x_125_, v_snd_114_, v___x_124_);
lean_dec_ref(v___x_125_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v___x_126_);
v___x_128_ = v___x_122_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_fst_113_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v___x_126_);
v___x_128_ = v_reuseFailAlloc_130_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
lean_object* v___x_129_; 
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
lean_ctor_set(v___x_129_, 1, v_s_106_);
return v___x_129_;
}
}
}
}
v___jp_108_:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_109_ = ((lean_object*)(l_Std_Internal_Parsec_String_pstring___closed__0));
v___x_110_ = lean_string_append(v___x_109_, v_s_106_);
lean_dec_ref(v_s_106_);
v___x_111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
v___x_112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_112_, 0, v_it_107_);
lean_ctor_set(v___x_112_, 1, v___x_111_);
return v___x_112_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_skipString(lean_object* v_s_134_, lean_object* v_a_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Std_Internal_Parsec_String_pstring(v_s_134_, v_a_135_);
if (lean_obj_tag(v___x_136_) == 0)
{
lean_object* v_pos_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_145_; 
v_pos_137_ = lean_ctor_get(v___x_136_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_136_);
if (v_isSharedCheck_145_ == 0)
{
lean_object* v_unused_146_; 
v_unused_146_ = lean_ctor_get(v___x_136_, 1);
lean_dec(v_unused_146_);
v___x_139_ = v___x_136_;
v_isShared_140_ = v_isSharedCheck_145_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_pos_137_);
lean_dec(v___x_136_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_145_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_141_; lean_object* v___x_143_; 
v___x_141_ = lean_box(0);
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 1, v___x_141_);
v___x_143_ = v___x_139_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_pos_137_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v___x_141_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
else
{
lean_object* v_pos_147_; lean_object* v_err_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_155_; 
v_pos_147_ = lean_ctor_get(v___x_136_, 0);
v_err_148_ = lean_ctor_get(v___x_136_, 1);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_136_);
if (v_isSharedCheck_155_ == 0)
{
v___x_150_ = v___x_136_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_err_148_);
lean_inc(v_pos_147_);
lean_dec(v___x_136_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_pos_147_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_err_148_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_pchar(uint32_t v_c_159_, lean_object* v_a_160_){
_start:
{
lean_object* v_fst_161_; lean_object* v_snd_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v_fst_161_ = lean_ctor_get(v_a_160_, 0);
v_snd_162_ = lean_ctor_get(v_a_160_, 1);
v___x_163_ = lean_string_utf8_byte_size(v_fst_161_);
v___x_164_ = lean_nat_dec_eq(v_snd_162_, v___x_163_);
if (v___x_164_ == 0)
{
uint32_t v_c_165_; uint8_t v___x_166_; 
v_c_165_ = lean_string_utf8_get_fast(v_fst_161_, v_snd_162_);
v___x_166_ = lean_uint32_dec_eq(v_c_165_, v_c_159_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_167_ = ((lean_object*)(l_Std_Internal_Parsec_String_pchar___closed__0));
v___x_168_ = ((lean_object*)(l_Std_Internal_Parsec_String_pchar___closed__1));
v___x_169_ = lean_string_push(v___x_168_, v_c_159_);
v___x_170_ = lean_string_append(v___x_167_, v___x_169_);
lean_dec_ref(v___x_169_);
v___x_171_ = ((lean_object*)(l_Std_Internal_Parsec_String_pchar___closed__2));
v___x_172_ = lean_string_append(v___x_170_, v___x_171_);
v___x_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
v___x_174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_174_, 0, v_a_160_);
lean_ctor_set(v___x_174_, 1, v___x_173_);
return v___x_174_;
}
else
{
lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_184_; 
lean_inc(v_snd_162_);
lean_inc(v_fst_161_);
v_isSharedCheck_184_ = !lean_is_exclusive(v_a_160_);
if (v_isSharedCheck_184_ == 0)
{
lean_object* v_unused_185_; lean_object* v_unused_186_; 
v_unused_185_ = lean_ctor_get(v_a_160_, 1);
lean_dec(v_unused_185_);
v_unused_186_ = lean_ctor_get(v_a_160_, 0);
lean_dec(v_unused_186_);
v___x_176_ = v_a_160_;
v_isShared_177_ = v_isSharedCheck_184_;
goto v_resetjp_175_;
}
else
{
lean_dec(v_a_160_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_184_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_178_; lean_object* v_it_x27_180_; 
v___x_178_ = lean_string_utf8_next_fast(v_fst_161_, v_snd_162_);
lean_dec(v_snd_162_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 1, v___x_178_);
v_it_x27_180_ = v___x_176_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_fst_161_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v___x_178_);
v_it_x27_180_ = v_reuseFailAlloc_183_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = lean_box_uint32(v_c_159_);
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v_it_x27_180_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
return v___x_182_;
}
}
}
}
else
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = lean_box(0);
v___x_188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_188_, 0, v_a_160_);
lean_ctor_set(v___x_188_, 1, v___x_187_);
return v___x_188_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_pchar___boxed(lean_object* v_c_189_, lean_object* v_a_190_){
_start:
{
uint32_t v_c_boxed_191_; lean_object* v_res_192_; 
v_c_boxed_191_ = lean_unbox_uint32(v_c_189_);
lean_dec(v_c_189_);
v_res_192_ = l_Std_Internal_Parsec_String_pchar(v_c_boxed_191_, v_a_190_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_skipChar(uint32_t v_c_193_, lean_object* v_a_194_){
_start:
{
lean_object* v_fst_195_; lean_object* v_snd_196_; lean_object* v___x_197_; uint8_t v___x_198_; 
v_fst_195_ = lean_ctor_get(v_a_194_, 0);
v_snd_196_ = lean_ctor_get(v_a_194_, 1);
v___x_197_ = lean_string_utf8_byte_size(v_fst_195_);
v___x_198_ = lean_nat_dec_eq(v_snd_196_, v___x_197_);
if (v___x_198_ == 0)
{
uint32_t v_c_199_; uint8_t v___x_200_; 
v_c_199_ = lean_string_utf8_get_fast(v_fst_195_, v_snd_196_);
v___x_200_ = lean_uint32_dec_eq(v_c_199_, v_c_193_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_201_ = ((lean_object*)(l_Std_Internal_Parsec_String_pchar___closed__0));
v___x_202_ = ((lean_object*)(l_Std_Internal_Parsec_String_pchar___closed__1));
v___x_203_ = lean_string_push(v___x_202_, v_c_193_);
v___x_204_ = lean_string_append(v___x_201_, v___x_203_);
lean_dec_ref(v___x_203_);
v___x_205_ = ((lean_object*)(l_Std_Internal_Parsec_String_pchar___closed__2));
v___x_206_ = lean_string_append(v___x_204_, v___x_205_);
v___x_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
v___x_208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_208_, 0, v_a_194_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
return v___x_208_;
}
else
{
lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_218_; 
lean_inc(v_snd_196_);
lean_inc(v_fst_195_);
v_isSharedCheck_218_ = !lean_is_exclusive(v_a_194_);
if (v_isSharedCheck_218_ == 0)
{
lean_object* v_unused_219_; lean_object* v_unused_220_; 
v_unused_219_ = lean_ctor_get(v_a_194_, 1);
lean_dec(v_unused_219_);
v_unused_220_ = lean_ctor_get(v_a_194_, 0);
lean_dec(v_unused_220_);
v___x_210_ = v_a_194_;
v_isShared_211_ = v_isSharedCheck_218_;
goto v_resetjp_209_;
}
else
{
lean_dec(v_a_194_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_218_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_212_; lean_object* v_it_x27_214_; 
v___x_212_ = lean_string_utf8_next_fast(v_fst_195_, v_snd_196_);
lean_dec(v_snd_196_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 1, v___x_212_);
v_it_x27_214_ = v___x_210_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_fst_195_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v___x_212_);
v_it_x27_214_ = v_reuseFailAlloc_217_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_box(0);
v___x_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_216_, 0, v_it_x27_214_);
lean_ctor_set(v___x_216_, 1, v___x_215_);
return v___x_216_;
}
}
}
}
else
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_box(0);
v___x_222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_222_, 0, v_a_194_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
return v___x_222_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_skipChar___boxed(lean_object* v_c_223_, lean_object* v_a_224_){
_start:
{
uint32_t v_c_boxed_225_; lean_object* v_res_226_; 
v_c_boxed_225_ = lean_unbox_uint32(v_c_223_);
lean_dec(v_c_223_);
v_res_226_ = l_Std_Internal_Parsec_String_skipChar(v_c_boxed_225_, v_a_224_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_digit(lean_object* v_a_230_){
_start:
{
lean_object* v_fst_234_; lean_object* v_snd_235_; lean_object* v___x_236_; uint8_t v___x_237_; 
v_fst_234_ = lean_ctor_get(v_a_230_, 0);
v_snd_235_ = lean_ctor_get(v_a_230_, 1);
v___x_236_ = lean_string_utf8_byte_size(v_fst_234_);
v___x_237_ = lean_nat_dec_eq(v_snd_235_, v___x_236_);
if (v___x_237_ == 0)
{
uint32_t v_c_238_; uint32_t v___x_239_; uint8_t v___x_240_; 
v_c_238_ = lean_string_utf8_get_fast(v_fst_234_, v_snd_235_);
v___x_239_ = 48;
v___x_240_ = lean_uint32_dec_le(v___x_239_, v_c_238_);
if (v___x_240_ == 0)
{
goto v___jp_231_;
}
else
{
uint32_t v___x_241_; uint8_t v___x_242_; 
v___x_241_ = 57;
v___x_242_ = lean_uint32_dec_le(v_c_238_, v___x_241_);
if (v___x_242_ == 0)
{
goto v___jp_231_;
}
else
{
lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_252_; 
lean_inc(v_snd_235_);
lean_inc(v_fst_234_);
v_isSharedCheck_252_ = !lean_is_exclusive(v_a_230_);
if (v_isSharedCheck_252_ == 0)
{
lean_object* v_unused_253_; lean_object* v_unused_254_; 
v_unused_253_ = lean_ctor_get(v_a_230_, 1);
lean_dec(v_unused_253_);
v_unused_254_ = lean_ctor_get(v_a_230_, 0);
lean_dec(v_unused_254_);
v___x_244_ = v_a_230_;
v_isShared_245_ = v_isSharedCheck_252_;
goto v_resetjp_243_;
}
else
{
lean_dec(v_a_230_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_252_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_246_; lean_object* v_it_x27_248_; 
v___x_246_ = lean_string_utf8_next_fast(v_fst_234_, v_snd_235_);
lean_dec(v_snd_235_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 1, v___x_246_);
v_it_x27_248_ = v___x_244_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_fst_234_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v___x_246_);
v_it_x27_248_ = v_reuseFailAlloc_251_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = lean_box_uint32(v_c_238_);
v___x_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_250_, 0, v_it_x27_248_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
return v___x_250_;
}
}
}
}
}
else
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = lean_box(0);
v___x_256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_256_, 0, v_a_230_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
return v___x_256_;
}
v___jp_231_:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = ((lean_object*)(l_Std_Internal_Parsec_String_digit___closed__1));
v___x_233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_233_, 0, v_a_230_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
return v___x_233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitToNat(uint32_t v_b_257_){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_258_ = lean_uint32_to_nat(v_b_257_);
v___x_259_ = lean_unsigned_to_nat(48u);
v___x_260_ = lean_nat_sub(v___x_258_, v___x_259_);
lean_dec(v___x_258_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitToNat___boxed(lean_object* v_b_261_){
_start:
{
uint32_t v_b_boxed_262_; lean_object* v_res_263_; 
v_b_boxed_262_ = lean_unbox_uint32(v_b_261_);
lean_dec(v_b_261_);
v_res_263_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitToNat(v_b_boxed_262_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(lean_object* v_s_264_, lean_object* v_it_265_, lean_object* v_acc_266_){
_start:
{
lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_267_ = lean_string_utf8_byte_size(v_s_264_);
v___x_268_ = lean_nat_dec_eq(v_it_265_, v___x_267_);
if (v___x_268_ == 0)
{
uint32_t v_candidate_269_; uint32_t v___x_270_; uint8_t v___x_271_; 
v_candidate_269_ = lean_string_utf8_get_fast(v_s_264_, v_it_265_);
v___x_270_ = 48;
v___x_271_ = lean_uint32_dec_le(v___x_270_, v_candidate_269_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; 
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v_acc_266_);
lean_ctor_set(v___x_272_, 1, v_it_265_);
return v___x_272_;
}
else
{
uint32_t v___x_273_; uint8_t v___x_274_; 
v___x_273_ = 57;
v___x_274_ = lean_uint32_dec_le(v_candidate_269_, v___x_273_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; 
v___x_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_275_, 0, v_acc_266_);
lean_ctor_set(v___x_275_, 1, v_it_265_);
return v___x_275_;
}
else
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v_digit_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v_acc_281_; lean_object* v___x_282_; 
v___x_276_ = lean_uint32_to_nat(v_candidate_269_);
v___x_277_ = lean_unsigned_to_nat(48u);
v_digit_278_ = lean_nat_sub(v___x_276_, v___x_277_);
lean_dec(v___x_276_);
v___x_279_ = lean_unsigned_to_nat(10u);
v___x_280_ = lean_nat_mul(v_acc_266_, v___x_279_);
lean_dec(v_acc_266_);
v_acc_281_ = lean_nat_add(v___x_280_, v_digit_278_);
lean_dec(v_digit_278_);
lean_dec(v___x_280_);
v___x_282_ = lean_string_utf8_next_fast(v_s_264_, v_it_265_);
lean_dec(v_it_265_);
v_it_265_ = v___x_282_;
v_acc_266_ = v_acc_281_;
goto _start;
}
}
}
else
{
lean_object* v___x_284_; 
v___x_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_284_, 0, v_acc_266_);
lean_ctor_set(v___x_284_, 1, v_it_265_);
return v___x_284_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go___boxed(lean_object* v_s_285_, lean_object* v_it_286_, lean_object* v_acc_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(v_s_285_, v_it_286_, v_acc_287_);
lean_dec_ref(v_s_285_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore(lean_object* v_acc_289_, lean_object* v_it_290_){
_start:
{
lean_object* v_fst_291_; lean_object* v_snd_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_309_; 
v_fst_291_ = lean_ctor_get(v_it_290_, 0);
v_snd_292_ = lean_ctor_get(v_it_290_, 1);
v_isSharedCheck_309_ = !lean_is_exclusive(v_it_290_);
if (v_isSharedCheck_309_ == 0)
{
v___x_294_ = v_it_290_;
v_isShared_295_ = v_isSharedCheck_309_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_snd_292_);
lean_inc(v_fst_291_);
lean_dec(v_it_290_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_309_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_296_; lean_object* v_fst_297_; lean_object* v_snd_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_308_; 
v___x_296_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(v_fst_291_, v_snd_292_, v_acc_289_);
v_fst_297_ = lean_ctor_get(v___x_296_, 0);
v_snd_298_ = lean_ctor_get(v___x_296_, 1);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_308_ == 0)
{
v___x_300_ = v___x_296_;
v_isShared_301_ = v_isSharedCheck_308_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_snd_298_);
lean_inc(v_fst_297_);
lean_dec(v___x_296_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_308_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 1, v_snd_298_);
v___x_303_ = v___x_294_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_fst_291_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v_snd_298_);
v___x_303_ = v_reuseFailAlloc_307_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
lean_object* v___x_305_; 
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 1, v_fst_297_);
lean_ctor_set(v___x_300_, 0, v___x_303_);
v___x_305_ = v___x_300_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_303_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v_fst_297_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_digits(lean_object* v_a_310_){
_start:
{
lean_object* v_fst_314_; lean_object* v_snd_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
v_fst_314_ = lean_ctor_get(v_a_310_, 0);
v_snd_315_ = lean_ctor_get(v_a_310_, 1);
v___x_316_ = lean_string_utf8_byte_size(v_fst_314_);
v___x_317_ = lean_nat_dec_eq(v_snd_315_, v___x_316_);
if (v___x_317_ == 0)
{
uint32_t v_c_318_; uint32_t v___x_319_; uint8_t v___x_320_; 
v_c_318_ = lean_string_utf8_get_fast(v_fst_314_, v_snd_315_);
v___x_319_ = 48;
v___x_320_ = lean_uint32_dec_le(v___x_319_, v_c_318_);
if (v___x_320_ == 0)
{
goto v___jp_311_;
}
else
{
uint32_t v___x_321_; uint8_t v___x_322_; 
v___x_321_ = 57;
v___x_322_ = lean_uint32_dec_le(v_c_318_, v___x_321_);
if (v___x_322_ == 0)
{
goto v___jp_311_;
}
else
{
lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_343_; 
lean_inc(v_snd_315_);
lean_inc(v_fst_314_);
v_isSharedCheck_343_ = !lean_is_exclusive(v_a_310_);
if (v_isSharedCheck_343_ == 0)
{
lean_object* v_unused_344_; lean_object* v_unused_345_; 
v_unused_344_ = lean_ctor_get(v_a_310_, 1);
lean_dec(v_unused_344_);
v_unused_345_ = lean_ctor_get(v_a_310_, 0);
lean_dec(v_unused_345_);
v___x_324_ = v_a_310_;
v_isShared_325_ = v_isSharedCheck_343_;
goto v_resetjp_323_;
}
else
{
lean_dec(v_a_310_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_343_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v_fst_331_; lean_object* v_snd_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_342_; 
v___x_326_ = lean_string_utf8_next_fast(v_fst_314_, v_snd_315_);
lean_dec(v_snd_315_);
v___x_327_ = lean_uint32_to_nat(v_c_318_);
v___x_328_ = lean_unsigned_to_nat(48u);
v___x_329_ = lean_nat_sub(v___x_327_, v___x_328_);
lean_dec(v___x_327_);
v___x_330_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(v_fst_314_, v___x_326_, v___x_329_);
v_fst_331_ = lean_ctor_get(v___x_330_, 0);
v_snd_332_ = lean_ctor_get(v___x_330_, 1);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_342_ == 0)
{
v___x_334_ = v___x_330_;
v_isShared_335_ = v_isSharedCheck_342_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_snd_332_);
lean_inc(v_fst_331_);
lean_dec(v___x_330_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_342_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 1, v_snd_332_);
v___x_337_ = v___x_324_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_fst_314_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_snd_332_);
v___x_337_ = v_reuseFailAlloc_341_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
lean_object* v___x_339_; 
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 1, v_fst_331_);
lean_ctor_set(v___x_334_, 0, v___x_337_);
v___x_339_ = v___x_334_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_337_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_fst_331_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_box(0);
v___x_347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_347_, 0, v_a_310_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
return v___x_347_;
}
v___jp_311_:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = ((lean_object*)(l_Std_Internal_Parsec_String_digit___closed__1));
v___x_313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_313_, 0, v_a_310_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
return v___x_313_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_hexDigit(lean_object* v_a_351_){
_start:
{
lean_object* v_fst_355_; lean_object* v_snd_356_; lean_object* v___x_357_; uint8_t v___x_358_; 
v_fst_355_ = lean_ctor_get(v_a_351_, 0);
v_snd_356_ = lean_ctor_get(v_a_351_, 1);
v___x_357_ = lean_string_utf8_byte_size(v_fst_355_);
v___x_358_ = lean_nat_dec_eq(v_snd_356_, v___x_357_);
if (v___x_358_ == 0)
{
uint32_t v_c_359_; lean_object* v___x_360_; lean_object* v_it_x27_361_; lean_object* v___x_362_; lean_object* v___x_363_; uint32_t v___x_374_; uint8_t v___x_375_; 
v_c_359_ = lean_string_utf8_get_fast(v_fst_355_, v_snd_356_);
v___x_360_ = lean_string_utf8_next_fast(v_fst_355_, v_snd_356_);
lean_inc(v_fst_355_);
v_it_x27_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_361_, 0, v_fst_355_);
lean_ctor_set(v_it_x27_361_, 1, v___x_360_);
v___x_362_ = lean_box_uint32(v_c_359_);
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v_it_x27_361_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
v___x_374_ = 48;
v___x_375_ = lean_uint32_dec_le(v___x_374_, v_c_359_);
if (v___x_375_ == 0)
{
goto v___jp_369_;
}
else
{
uint32_t v___x_376_; uint8_t v___x_377_; 
v___x_376_ = 57;
v___x_377_ = lean_uint32_dec_le(v_c_359_, v___x_376_);
if (v___x_377_ == 0)
{
goto v___jp_369_;
}
else
{
lean_dec_ref(v_a_351_);
return v___x_363_;
}
}
v___jp_364_:
{
uint32_t v___x_365_; uint8_t v___x_366_; 
v___x_365_ = 65;
v___x_366_ = lean_uint32_dec_le(v___x_365_, v_c_359_);
if (v___x_366_ == 0)
{
lean_dec_ref(v___x_363_);
goto v___jp_352_;
}
else
{
uint32_t v___x_367_; uint8_t v___x_368_; 
v___x_367_ = 70;
v___x_368_ = lean_uint32_dec_le(v_c_359_, v___x_367_);
if (v___x_368_ == 0)
{
lean_dec_ref(v___x_363_);
goto v___jp_352_;
}
else
{
lean_dec_ref(v_a_351_);
return v___x_363_;
}
}
}
v___jp_369_:
{
uint32_t v___x_370_; uint8_t v___x_371_; 
v___x_370_ = 97;
v___x_371_ = lean_uint32_dec_le(v___x_370_, v_c_359_);
if (v___x_371_ == 0)
{
goto v___jp_364_;
}
else
{
uint32_t v___x_372_; uint8_t v___x_373_; 
v___x_372_ = 102;
v___x_373_ = lean_uint32_dec_le(v_c_359_, v___x_372_);
if (v___x_373_ == 0)
{
goto v___jp_364_;
}
else
{
lean_dec_ref(v_a_351_);
return v___x_363_;
}
}
}
}
else
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = lean_box(0);
v___x_379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_379_, 0, v_a_351_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
return v___x_379_;
}
v___jp_352_:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = ((lean_object*)(l_Std_Internal_Parsec_String_hexDigit___closed__1));
v___x_354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_354_, 0, v_a_351_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
return v___x_354_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_asciiLetter(lean_object* v_a_383_){
_start:
{
lean_object* v_fst_387_; lean_object* v_snd_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v_fst_387_ = lean_ctor_get(v_a_383_, 0);
v_snd_388_ = lean_ctor_get(v_a_383_, 1);
v___x_389_ = lean_string_utf8_byte_size(v_fst_387_);
v___x_390_ = lean_nat_dec_eq(v_snd_388_, v___x_389_);
if (v___x_390_ == 0)
{
uint32_t v_c_391_; lean_object* v___x_392_; lean_object* v_it_x27_393_; lean_object* v___x_394_; lean_object* v___x_395_; uint32_t v___x_401_; uint8_t v___x_402_; 
v_c_391_ = lean_string_utf8_get_fast(v_fst_387_, v_snd_388_);
v___x_392_ = lean_string_utf8_next_fast(v_fst_387_, v_snd_388_);
lean_inc(v_fst_387_);
v_it_x27_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_393_, 0, v_fst_387_);
lean_ctor_set(v_it_x27_393_, 1, v___x_392_);
v___x_394_ = lean_box_uint32(v_c_391_);
v___x_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_395_, 0, v_it_x27_393_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
v___x_401_ = 65;
v___x_402_ = lean_uint32_dec_le(v___x_401_, v_c_391_);
if (v___x_402_ == 0)
{
goto v___jp_396_;
}
else
{
uint32_t v___x_403_; uint8_t v___x_404_; 
v___x_403_ = 90;
v___x_404_ = lean_uint32_dec_le(v_c_391_, v___x_403_);
if (v___x_404_ == 0)
{
goto v___jp_396_;
}
else
{
lean_dec_ref(v_a_383_);
return v___x_395_;
}
}
v___jp_396_:
{
uint32_t v___x_397_; uint8_t v___x_398_; 
v___x_397_ = 97;
v___x_398_ = lean_uint32_dec_le(v___x_397_, v_c_391_);
if (v___x_398_ == 0)
{
lean_dec_ref(v___x_395_);
goto v___jp_384_;
}
else
{
uint32_t v___x_399_; uint8_t v___x_400_; 
v___x_399_ = 122;
v___x_400_ = lean_uint32_dec_le(v_c_391_, v___x_399_);
if (v___x_400_ == 0)
{
lean_dec_ref(v___x_395_);
goto v___jp_384_;
}
else
{
lean_dec_ref(v_a_383_);
return v___x_395_;
}
}
}
}
else
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_box(0);
v___x_406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_406_, 0, v_a_383_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
return v___x_406_;
}
v___jp_384_:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = ((lean_object*)(l_Std_Internal_Parsec_String_asciiLetter___closed__1));
v___x_386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_386_, 0, v_a_383_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
return v___x_386_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(lean_object* v_s_407_, lean_object* v_it_408_){
_start:
{
lean_object* v___x_412_; uint8_t v___x_413_; 
v___x_412_ = lean_string_utf8_byte_size(v_s_407_);
v___x_413_ = lean_nat_dec_eq(v_it_408_, v___x_412_);
if (v___x_413_ == 0)
{
uint32_t v_c_414_; uint32_t v___x_415_; uint8_t v___x_416_; 
v_c_414_ = lean_string_utf8_get_fast(v_s_407_, v_it_408_);
v___x_415_ = 9;
v___x_416_ = lean_uint32_dec_eq(v_c_414_, v___x_415_);
if (v___x_416_ == 0)
{
uint32_t v___x_417_; uint8_t v___x_418_; 
v___x_417_ = 10;
v___x_418_ = lean_uint32_dec_eq(v_c_414_, v___x_417_);
if (v___x_418_ == 0)
{
uint32_t v___x_419_; uint8_t v___x_420_; 
v___x_419_ = 13;
v___x_420_ = lean_uint32_dec_eq(v_c_414_, v___x_419_);
if (v___x_420_ == 0)
{
uint32_t v___x_421_; uint8_t v___x_422_; 
v___x_421_ = 32;
v___x_422_ = lean_uint32_dec_eq(v_c_414_, v___x_421_);
if (v___x_422_ == 0)
{
return v_it_408_;
}
else
{
goto v___jp_409_;
}
}
else
{
goto v___jp_409_;
}
}
else
{
goto v___jp_409_;
}
}
else
{
goto v___jp_409_;
}
}
else
{
return v_it_408_;
}
v___jp_409_:
{
lean_object* v___x_410_; 
v___x_410_ = lean_string_utf8_next_fast(v_s_407_, v_it_408_);
lean_dec(v_it_408_);
v_it_408_ = v___x_410_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs___boxed(lean_object* v_s_423_, lean_object* v_it_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_s_423_, v_it_424_);
lean_dec_ref(v_s_423_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_ws(lean_object* v_it_426_){
_start:
{
lean_object* v_fst_427_; lean_object* v_snd_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_438_; 
v_fst_427_ = lean_ctor_get(v_it_426_, 0);
v_snd_428_ = lean_ctor_get(v_it_426_, 1);
v_isSharedCheck_438_ = !lean_is_exclusive(v_it_426_);
if (v_isSharedCheck_438_ == 0)
{
v___x_430_ = v_it_426_;
v_isShared_431_ = v_isSharedCheck_438_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_snd_428_);
lean_inc(v_fst_427_);
lean_dec(v_it_426_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_438_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_432_; lean_object* v___x_434_; 
v___x_432_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_427_, v_snd_428_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 1, v___x_432_);
v___x_434_ = v___x_430_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_fst_427_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v___x_432_);
v___x_434_ = v_reuseFailAlloc_437_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_box(0);
v___x_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_436_, 0, v___x_434_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
return v___x_436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_take(lean_object* v_n_439_, lean_object* v_it_440_){
_start:
{
lean_object* v_fst_441_; lean_object* v_snd_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v_right_446_; lean_object* v_substr_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
v_fst_441_ = lean_ctor_get(v_it_440_, 0);
v_snd_442_ = lean_ctor_get(v_it_440_, 1);
v___x_443_ = lean_unsigned_to_nat(0u);
v___x_444_ = lean_string_utf8_byte_size(v_fst_441_);
lean_inc(v_fst_441_);
v___x_445_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_445_, 0, v_fst_441_);
lean_ctor_set(v___x_445_, 1, v___x_443_);
lean_ctor_set(v___x_445_, 2, v___x_444_);
lean_inc(v_n_439_);
lean_inc(v_snd_442_);
v_right_446_ = l_String_Slice_Pos_nextn(v___x_445_, v_snd_442_, v_n_439_);
lean_dec_ref(v___x_445_);
v_substr_447_ = lean_string_utf8_extract(v_fst_441_, v_snd_442_, v_right_446_);
v___x_448_ = lean_string_length(v_substr_447_);
v___x_449_ = lean_nat_dec_eq(v___x_448_, v_n_439_);
lean_dec(v_n_439_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; lean_object* v___x_451_; 
lean_dec_ref(v_substr_447_);
lean_dec(v_right_446_);
v___x_450_ = lean_box(0);
v___x_451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_451_, 0, v_it_440_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
return v___x_451_;
}
else
{
lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_459_; 
lean_inc(v_fst_441_);
v_isSharedCheck_459_ = !lean_is_exclusive(v_it_440_);
if (v_isSharedCheck_459_ == 0)
{
lean_object* v_unused_460_; lean_object* v_unused_461_; 
v_unused_460_ = lean_ctor_get(v_it_440_, 1);
lean_dec(v_unused_460_);
v_unused_461_ = lean_ctor_get(v_it_440_, 0);
lean_dec(v_unused_461_);
v___x_453_ = v_it_440_;
v_isShared_454_ = v_isSharedCheck_459_;
goto v_resetjp_452_;
}
else
{
lean_dec(v_it_440_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_459_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 1, v_right_446_);
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_fst_441_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_right_446_);
v___x_456_ = v_reuseFailAlloc_458_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
lean_object* v___x_457_; 
v___x_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set(v___x_457_, 1, v_substr_447_);
return v___x_457_;
}
}
}
}
}
lean_object* runtime_initialize_Std_Internal_Parsec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Termination(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Parsec_String(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Internal_Parsec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Termination(builtin);
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

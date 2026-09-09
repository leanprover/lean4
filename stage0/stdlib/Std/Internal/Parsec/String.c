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
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
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
lean_dec_ref_known(v___x_24_, 3);
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
lean_object* v_fst_30_; lean_object* v_snd_31_; lean_object* v___x_32_; uint8_t v_decide_33_; 
v_fst_30_ = lean_ctor_get(v_it_29_, 0);
v_snd_31_ = lean_ctor_get(v_it_29_, 1);
v___x_32_ = lean_string_utf8_byte_size(v_fst_30_);
v_decide_33_ = lean_nat_dec_eq(v_snd_31_, v___x_32_);
if (v_decide_33_ == 0)
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
lean_dec_ref_known(v___x_81_, 2);
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
lean_dec_ref_known(v___x_81_, 2);
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
lean_dec_ref_known(v_err_85_, 1);
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
lean_dec_ref_known(v___x_125_, 3);
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
lean_object* v_fst_161_; lean_object* v_snd_162_; lean_object* v___x_163_; uint8_t v_decide_164_; 
v_fst_161_ = lean_ctor_get(v_a_160_, 0);
v_snd_162_ = lean_ctor_get(v_a_160_, 1);
v___x_163_ = lean_string_utf8_byte_size(v_fst_161_);
v_decide_164_ = lean_nat_dec_eq(v_snd_162_, v___x_163_);
if (v_decide_164_ == 0)
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
lean_object* v_fst_195_; lean_object* v_snd_196_; lean_object* v___x_197_; uint8_t v_decide_198_; 
v_fst_195_ = lean_ctor_get(v_a_194_, 0);
v_snd_196_ = lean_ctor_get(v_a_194_, 1);
v___x_197_ = lean_string_utf8_byte_size(v_fst_195_);
v_decide_198_ = lean_nat_dec_eq(v_snd_196_, v___x_197_);
if (v_decide_198_ == 0)
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
lean_object* v_fst_231_; lean_object* v_snd_232_; lean_object* v___x_233_; uint8_t v_decide_234_; 
v_fst_231_ = lean_ctor_get(v_a_230_, 0);
v_snd_232_ = lean_ctor_get(v_a_230_, 1);
v___x_233_ = lean_string_utf8_byte_size(v_fst_231_);
v_decide_234_ = lean_nat_dec_eq(v_snd_232_, v___x_233_);
if (v_decide_234_ == 0)
{
uint32_t v_c_235_; lean_object* v___x_236_; uint8_t v___y_238_; uint32_t v___x_252_; uint8_t v___x_253_; 
v_c_235_ = lean_string_utf8_get_fast(v_fst_231_, v_snd_232_);
v___x_236_ = lean_string_utf8_next_fast(v_fst_231_, v_snd_232_);
v___x_252_ = 48;
v___x_253_ = lean_uint32_dec_le(v___x_252_, v_c_235_);
if (v___x_253_ == 0)
{
v___y_238_ = v___x_253_;
goto v___jp_237_;
}
else
{
uint32_t v___x_254_; uint8_t v___x_255_; 
v___x_254_ = 57;
v___x_255_ = lean_uint32_dec_le(v_c_235_, v___x_254_);
v___y_238_ = v___x_255_;
goto v___jp_237_;
}
v___jp_237_:
{
if (v___y_238_ == 0)
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = ((lean_object*)(l_Std_Internal_Parsec_String_digit___closed__1));
v___x_240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_240_, 0, v_a_230_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
return v___x_240_;
}
else
{
lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_249_; 
lean_inc(v_fst_231_);
v_isSharedCheck_249_ = !lean_is_exclusive(v_a_230_);
if (v_isSharedCheck_249_ == 0)
{
lean_object* v_unused_250_; lean_object* v_unused_251_; 
v_unused_250_ = lean_ctor_get(v_a_230_, 1);
lean_dec(v_unused_250_);
v_unused_251_ = lean_ctor_get(v_a_230_, 0);
lean_dec(v_unused_251_);
v___x_242_ = v_a_230_;
v_isShared_243_ = v_isSharedCheck_249_;
goto v_resetjp_241_;
}
else
{
lean_dec(v_a_230_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_249_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v_it_x27_245_; 
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 1, v___x_236_);
v_it_x27_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_fst_231_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v___x_236_);
v_it_x27_245_ = v_reuseFailAlloc_248_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = lean_box_uint32(v_c_235_);
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v_it_x27_245_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
return v___x_247_;
}
}
}
}
}
else
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = lean_box(0);
v___x_257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_257_, 0, v_a_230_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
return v___x_257_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitToNat(uint32_t v_b_258_){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_259_ = lean_uint32_to_nat(v_b_258_);
v___x_260_ = lean_unsigned_to_nat(48u);
v___x_261_ = lean_nat_sub(v___x_259_, v___x_260_);
lean_dec(v___x_259_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitToNat___boxed(lean_object* v_b_262_){
_start:
{
uint32_t v_b_boxed_263_; lean_object* v_res_264_; 
v_b_boxed_263_ = lean_unbox_uint32(v_b_262_);
lean_dec(v_b_262_);
v_res_264_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitToNat(v_b_boxed_263_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(lean_object* v_s_265_, lean_object* v_it_266_, lean_object* v_acc_267_){
_start:
{
lean_object* v___x_268_; uint8_t v_decide_269_; 
v___x_268_ = lean_string_utf8_byte_size(v_s_265_);
v_decide_269_ = lean_nat_dec_eq(v_it_266_, v___x_268_);
if (v_decide_269_ == 0)
{
uint32_t v_candidate_270_; uint8_t v___y_272_; uint32_t v___x_282_; uint8_t v___x_283_; 
v_candidate_270_ = lean_string_utf8_get_fast(v_s_265_, v_it_266_);
v___x_282_ = 48;
v___x_283_ = lean_uint32_dec_le(v___x_282_, v_candidate_270_);
if (v___x_283_ == 0)
{
v___y_272_ = v___x_283_;
goto v___jp_271_;
}
else
{
uint32_t v___x_284_; uint8_t v___x_285_; 
v___x_284_ = 57;
v___x_285_ = lean_uint32_dec_le(v_candidate_270_, v___x_284_);
v___y_272_ = v___x_285_;
goto v___jp_271_;
}
v___jp_271_:
{
if (v___y_272_ == 0)
{
lean_object* v___x_273_; 
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v_acc_267_);
lean_ctor_set(v___x_273_, 1, v_it_266_);
return v___x_273_;
}
else
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v_digit_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v_acc_279_; lean_object* v___x_280_; 
v___x_274_ = lean_uint32_to_nat(v_candidate_270_);
v___x_275_ = lean_unsigned_to_nat(48u);
v_digit_276_ = lean_nat_sub(v___x_274_, v___x_275_);
lean_dec(v___x_274_);
v___x_277_ = lean_unsigned_to_nat(10u);
v___x_278_ = lean_nat_mul(v_acc_267_, v___x_277_);
lean_dec(v_acc_267_);
v_acc_279_ = lean_nat_add(v___x_278_, v_digit_276_);
lean_dec(v_digit_276_);
lean_dec(v___x_278_);
v___x_280_ = lean_string_utf8_next_fast(v_s_265_, v_it_266_);
lean_dec(v_it_266_);
v_it_266_ = v___x_280_;
v_acc_267_ = v_acc_279_;
goto _start;
}
}
}
else
{
lean_object* v___x_286_; 
v___x_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_286_, 0, v_acc_267_);
lean_ctor_set(v___x_286_, 1, v_it_266_);
return v___x_286_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go___boxed(lean_object* v_s_287_, lean_object* v_it_288_, lean_object* v_acc_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(v_s_287_, v_it_288_, v_acc_289_);
lean_dec_ref(v_s_287_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore(lean_object* v_acc_291_, lean_object* v_it_292_){
_start:
{
lean_object* v_fst_293_; lean_object* v_snd_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_311_; 
v_fst_293_ = lean_ctor_get(v_it_292_, 0);
v_snd_294_ = lean_ctor_get(v_it_292_, 1);
v_isSharedCheck_311_ = !lean_is_exclusive(v_it_292_);
if (v_isSharedCheck_311_ == 0)
{
v___x_296_ = v_it_292_;
v_isShared_297_ = v_isSharedCheck_311_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_snd_294_);
lean_inc(v_fst_293_);
lean_dec(v_it_292_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_311_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_298_; lean_object* v_fst_299_; lean_object* v_snd_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_310_; 
v___x_298_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(v_fst_293_, v_snd_294_, v_acc_291_);
v_fst_299_ = lean_ctor_get(v___x_298_, 0);
v_snd_300_ = lean_ctor_get(v___x_298_, 1);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_310_ == 0)
{
v___x_302_ = v___x_298_;
v_isShared_303_ = v_isSharedCheck_310_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_snd_300_);
lean_inc(v_fst_299_);
lean_dec(v___x_298_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_310_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 1, v_snd_300_);
v___x_305_ = v___x_296_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_fst_293_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_snd_300_);
v___x_305_ = v_reuseFailAlloc_309_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
lean_object* v___x_307_; 
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 1, v_fst_299_);
lean_ctor_set(v___x_302_, 0, v___x_305_);
v___x_307_ = v___x_302_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v_fst_299_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_digits(lean_object* v_a_312_){
_start:
{
lean_object* v_fst_313_; lean_object* v_snd_314_; lean_object* v___x_315_; uint8_t v_decide_316_; 
v_fst_313_ = lean_ctor_get(v_a_312_, 0);
v_snd_314_ = lean_ctor_get(v_a_312_, 1);
v___x_315_ = lean_string_utf8_byte_size(v_fst_313_);
v_decide_316_ = lean_nat_dec_eq(v_snd_314_, v___x_315_);
if (v_decide_316_ == 0)
{
uint32_t v_c_317_; uint8_t v___y_319_; uint32_t v___x_345_; uint8_t v___x_346_; 
v_c_317_ = lean_string_utf8_get_fast(v_fst_313_, v_snd_314_);
v___x_345_ = 48;
v___x_346_ = lean_uint32_dec_le(v___x_345_, v_c_317_);
if (v___x_346_ == 0)
{
v___y_319_ = v___x_346_;
goto v___jp_318_;
}
else
{
uint32_t v___x_347_; uint8_t v___x_348_; 
v___x_347_ = 57;
v___x_348_ = lean_uint32_dec_le(v_c_317_, v___x_347_);
v___y_319_ = v___x_348_;
goto v___jp_318_;
}
v___jp_318_:
{
if (v___y_319_ == 0)
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = ((lean_object*)(l_Std_Internal_Parsec_String_digit___closed__1));
v___x_321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_321_, 0, v_a_312_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
return v___x_321_;
}
else
{
lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_342_; 
lean_inc(v_snd_314_);
lean_inc(v_fst_313_);
v_isSharedCheck_342_ = !lean_is_exclusive(v_a_312_);
if (v_isSharedCheck_342_ == 0)
{
lean_object* v_unused_343_; lean_object* v_unused_344_; 
v_unused_343_ = lean_ctor_get(v_a_312_, 1);
lean_dec(v_unused_343_);
v_unused_344_ = lean_ctor_get(v_a_312_, 0);
lean_dec(v_unused_344_);
v___x_323_ = v_a_312_;
v_isShared_324_ = v_isSharedCheck_342_;
goto v_resetjp_322_;
}
else
{
lean_dec(v_a_312_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_342_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v_fst_330_; lean_object* v_snd_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_341_; 
v___x_325_ = lean_string_utf8_next_fast(v_fst_313_, v_snd_314_);
lean_dec(v_snd_314_);
v___x_326_ = lean_uint32_to_nat(v_c_317_);
v___x_327_ = lean_unsigned_to_nat(48u);
v___x_328_ = lean_nat_sub(v___x_326_, v___x_327_);
lean_dec(v___x_326_);
v___x_329_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(v_fst_313_, v___x_325_, v___x_328_);
v_fst_330_ = lean_ctor_get(v___x_329_, 0);
v_snd_331_ = lean_ctor_get(v___x_329_, 1);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_341_ == 0)
{
v___x_333_ = v___x_329_;
v_isShared_334_ = v_isSharedCheck_341_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_snd_331_);
lean_inc(v_fst_330_);
lean_dec(v___x_329_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_341_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 1, v_snd_331_);
v___x_336_ = v___x_323_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_fst_313_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_snd_331_);
v___x_336_ = v_reuseFailAlloc_340_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_338_; 
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 1, v_fst_330_);
lean_ctor_set(v___x_333_, 0, v___x_336_);
v___x_338_ = v___x_333_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_336_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_fst_330_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lean_box(0);
v___x_350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_350_, 0, v_a_312_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
return v___x_350_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_hexDigit(lean_object* v_a_354_){
_start:
{
lean_object* v_fst_355_; lean_object* v_snd_356_; lean_object* v___x_357_; uint8_t v_decide_358_; 
v_fst_355_ = lean_ctor_get(v_a_354_, 0);
v_snd_356_ = lean_ctor_get(v_a_354_, 1);
v___x_357_ = lean_string_utf8_byte_size(v_fst_355_);
v_decide_358_ = lean_nat_dec_eq(v_snd_356_, v___x_357_);
if (v_decide_358_ == 0)
{
uint32_t v_c_359_; lean_object* v___x_360_; uint8_t v___y_366_; uint8_t v___y_367_; uint8_t v___y_371_; uint8_t v___y_372_; uint8_t v___y_373_; uint8_t v___y_375_; uint8_t v___y_376_; uint8_t v___y_382_; uint32_t v___x_387_; uint8_t v___x_388_; 
v_c_359_ = lean_string_utf8_get_fast(v_fst_355_, v_snd_356_);
v___x_360_ = lean_string_utf8_next_fast(v_fst_355_, v_snd_356_);
v___x_387_ = 48;
v___x_388_ = lean_uint32_dec_le(v___x_387_, v_c_359_);
if (v___x_388_ == 0)
{
v___y_382_ = v___x_388_;
goto v___jp_381_;
}
else
{
uint32_t v___x_389_; uint8_t v___x_390_; 
v___x_389_ = 57;
v___x_390_ = lean_uint32_dec_le(v_c_359_, v___x_389_);
v___y_382_ = v___x_390_;
goto v___jp_381_;
}
v___jp_361_:
{
lean_object* v_it_x27_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v_it_x27_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_362_, 0, v_fst_355_);
lean_ctor_set(v_it_x27_362_, 1, v___x_360_);
v___x_363_ = lean_box_uint32(v_c_359_);
v___x_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_364_, 0, v_it_x27_362_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
return v___x_364_;
}
v___jp_365_:
{
if (v___y_366_ == 0)
{
if (v___y_367_ == 0)
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = ((lean_object*)(l_Std_Internal_Parsec_String_hexDigit___closed__1));
v___x_369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_369_, 0, v_a_354_);
lean_ctor_set(v___x_369_, 1, v___x_368_);
return v___x_369_;
}
else
{
lean_inc(v_fst_355_);
lean_dec_ref(v_a_354_);
goto v___jp_361_;
}
}
else
{
lean_inc(v_fst_355_);
lean_dec_ref(v_a_354_);
goto v___jp_361_;
}
}
v___jp_370_:
{
if (v___y_372_ == 0)
{
v___y_366_ = v___y_371_;
v___y_367_ = v___y_373_;
goto v___jp_365_;
}
else
{
v___y_366_ = v___y_371_;
v___y_367_ = v___y_372_;
goto v___jp_365_;
}
}
v___jp_374_:
{
uint32_t v___x_377_; uint8_t v___x_378_; 
v___x_377_ = 65;
v___x_378_ = lean_uint32_dec_le(v___x_377_, v_c_359_);
if (v___x_378_ == 0)
{
v___y_371_ = v___y_375_;
v___y_372_ = v___y_376_;
v___y_373_ = v___x_378_;
goto v___jp_370_;
}
else
{
uint32_t v___x_379_; uint8_t v___x_380_; 
v___x_379_ = 70;
v___x_380_ = lean_uint32_dec_le(v_c_359_, v___x_379_);
v___y_371_ = v___y_375_;
v___y_372_ = v___y_376_;
v___y_373_ = v___x_380_;
goto v___jp_370_;
}
}
v___jp_381_:
{
uint32_t v___x_383_; uint8_t v___x_384_; 
v___x_383_ = 97;
v___x_384_ = lean_uint32_dec_le(v___x_383_, v_c_359_);
if (v___x_384_ == 0)
{
v___y_375_ = v___y_382_;
v___y_376_ = v___x_384_;
goto v___jp_374_;
}
else
{
uint32_t v___x_385_; uint8_t v___x_386_; 
v___x_385_ = 102;
v___x_386_ = lean_uint32_dec_le(v_c_359_, v___x_385_);
v___y_375_ = v___y_382_;
v___y_376_ = v___x_386_;
goto v___jp_374_;
}
}
}
else
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = lean_box(0);
v___x_392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_392_, 0, v_a_354_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
return v___x_392_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_asciiLetter(lean_object* v_a_396_){
_start:
{
lean_object* v_fst_397_; lean_object* v_snd_398_; lean_object* v___x_399_; uint8_t v_decide_400_; 
v_fst_397_ = lean_ctor_get(v_a_396_, 0);
v_snd_398_ = lean_ctor_get(v_a_396_, 1);
v___x_399_ = lean_string_utf8_byte_size(v_fst_397_);
v_decide_400_ = lean_nat_dec_eq(v_snd_398_, v___x_399_);
if (v_decide_400_ == 0)
{
uint32_t v_c_401_; lean_object* v___x_402_; uint8_t v___y_408_; uint8_t v___y_409_; uint8_t v___y_413_; uint32_t v___x_418_; uint8_t v___x_419_; 
v_c_401_ = lean_string_utf8_get_fast(v_fst_397_, v_snd_398_);
v___x_402_ = lean_string_utf8_next_fast(v_fst_397_, v_snd_398_);
v___x_418_ = 65;
v___x_419_ = lean_uint32_dec_le(v___x_418_, v_c_401_);
if (v___x_419_ == 0)
{
v___y_413_ = v___x_419_;
goto v___jp_412_;
}
else
{
uint32_t v___x_420_; uint8_t v___x_421_; 
v___x_420_ = 90;
v___x_421_ = lean_uint32_dec_le(v_c_401_, v___x_420_);
v___y_413_ = v___x_421_;
goto v___jp_412_;
}
v___jp_403_:
{
lean_object* v_it_x27_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v_it_x27_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_it_x27_404_, 0, v_fst_397_);
lean_ctor_set(v_it_x27_404_, 1, v___x_402_);
v___x_405_ = lean_box_uint32(v_c_401_);
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v_it_x27_404_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
return v___x_406_;
}
v___jp_407_:
{
if (v___y_408_ == 0)
{
if (v___y_409_ == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = ((lean_object*)(l_Std_Internal_Parsec_String_asciiLetter___closed__1));
v___x_411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_411_, 0, v_a_396_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
return v___x_411_;
}
else
{
lean_inc(v_fst_397_);
lean_dec_ref(v_a_396_);
goto v___jp_403_;
}
}
else
{
lean_inc(v_fst_397_);
lean_dec_ref(v_a_396_);
goto v___jp_403_;
}
}
v___jp_412_:
{
uint32_t v___x_414_; uint8_t v___x_415_; 
v___x_414_ = 97;
v___x_415_ = lean_uint32_dec_le(v___x_414_, v_c_401_);
if (v___x_415_ == 0)
{
v___y_408_ = v___y_413_;
v___y_409_ = v___x_415_;
goto v___jp_407_;
}
else
{
uint32_t v___x_416_; uint8_t v___x_417_; 
v___x_416_ = 122;
v___x_417_ = lean_uint32_dec_le(v_c_401_, v___x_416_);
v___y_408_ = v___y_413_;
v___y_409_ = v___x_417_;
goto v___jp_407_;
}
}
}
else
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_box(0);
v___x_423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_423_, 0, v_a_396_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
return v___x_423_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(lean_object* v_s_424_, lean_object* v_it_425_){
_start:
{
uint8_t v___y_427_; lean_object* v___x_430_; uint8_t v_decide_431_; 
v___x_430_ = lean_string_utf8_byte_size(v_s_424_);
v_decide_431_ = lean_nat_dec_eq(v_it_425_, v___x_430_);
if (v_decide_431_ == 0)
{
uint32_t v_c_432_; uint32_t v___x_433_; uint8_t v___x_434_; uint8_t v___y_436_; uint32_t v___x_437_; uint8_t v___x_438_; uint8_t v___y_440_; uint32_t v___x_441_; uint8_t v___x_442_; 
v_c_432_ = lean_string_utf8_get_fast(v_s_424_, v_it_425_);
v___x_433_ = 9;
v___x_434_ = lean_uint32_dec_eq(v_c_432_, v___x_433_);
v___x_437_ = 10;
v___x_438_ = lean_uint32_dec_eq(v_c_432_, v___x_437_);
v___x_441_ = 13;
v___x_442_ = lean_uint32_dec_eq(v_c_432_, v___x_441_);
if (v___x_442_ == 0)
{
uint32_t v___x_443_; uint8_t v___x_444_; 
v___x_443_ = 32;
v___x_444_ = lean_uint32_dec_eq(v_c_432_, v___x_443_);
v___y_440_ = v___x_444_;
goto v___jp_439_;
}
else
{
v___y_440_ = v___x_442_;
goto v___jp_439_;
}
v___jp_435_:
{
if (v___x_434_ == 0)
{
v___y_427_ = v___y_436_;
goto v___jp_426_;
}
else
{
v___y_427_ = v___x_434_;
goto v___jp_426_;
}
}
v___jp_439_:
{
if (v___x_438_ == 0)
{
v___y_436_ = v___y_440_;
goto v___jp_435_;
}
else
{
v___y_436_ = v___x_438_;
goto v___jp_435_;
}
}
}
else
{
return v_it_425_;
}
v___jp_426_:
{
if (v___y_427_ == 0)
{
return v_it_425_;
}
else
{
lean_object* v___x_428_; 
v___x_428_ = lean_string_utf8_next_fast(v_s_424_, v_it_425_);
lean_dec(v_it_425_);
v_it_425_ = v___x_428_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs___boxed(lean_object* v_s_445_, lean_object* v_it_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_s_445_, v_it_446_);
lean_dec_ref(v_s_445_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_ws(lean_object* v_it_448_){
_start:
{
lean_object* v_fst_449_; lean_object* v_snd_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_460_; 
v_fst_449_ = lean_ctor_get(v_it_448_, 0);
v_snd_450_ = lean_ctor_get(v_it_448_, 1);
v_isSharedCheck_460_ = !lean_is_exclusive(v_it_448_);
if (v_isSharedCheck_460_ == 0)
{
v___x_452_ = v_it_448_;
v_isShared_453_ = v_isSharedCheck_460_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_snd_450_);
lean_inc(v_fst_449_);
lean_dec(v_it_448_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_460_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_454_; lean_object* v___x_456_; 
v___x_454_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(v_fst_449_, v_snd_450_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 1, v___x_454_);
v___x_456_ = v___x_452_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_fst_449_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v___x_454_);
v___x_456_ = v_reuseFailAlloc_459_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = lean_box(0);
v___x_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_456_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
return v___x_458_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_take(lean_object* v_n_461_, lean_object* v_it_462_){
_start:
{
lean_object* v_fst_463_; lean_object* v_snd_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v_right_468_; lean_object* v_substr_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v_fst_463_ = lean_ctor_get(v_it_462_, 0);
v_snd_464_ = lean_ctor_get(v_it_462_, 1);
v___x_465_ = lean_unsigned_to_nat(0u);
v___x_466_ = lean_string_utf8_byte_size(v_fst_463_);
lean_inc(v_fst_463_);
v___x_467_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_467_, 0, v_fst_463_);
lean_ctor_set(v___x_467_, 1, v___x_465_);
lean_ctor_set(v___x_467_, 2, v___x_466_);
lean_inc(v_n_461_);
lean_inc(v_snd_464_);
v_right_468_ = l_String_Slice_Pos_nextn(v___x_467_, v_snd_464_, v_n_461_);
lean_dec_ref_known(v___x_467_, 3);
v_substr_469_ = lean_string_utf8_extract_fast(v_fst_463_, v_snd_464_, v_right_468_);
v___x_470_ = lean_string_length(v_substr_469_);
v___x_471_ = lean_nat_dec_eq(v___x_470_, v_n_461_);
lean_dec(v_n_461_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; lean_object* v___x_473_; 
lean_dec_ref(v_substr_469_);
lean_dec(v_right_468_);
v___x_472_ = lean_box(0);
v___x_473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_473_, 0, v_it_462_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
return v___x_473_;
}
else
{
lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_481_; 
lean_inc(v_fst_463_);
v_isSharedCheck_481_ = !lean_is_exclusive(v_it_462_);
if (v_isSharedCheck_481_ == 0)
{
lean_object* v_unused_482_; lean_object* v_unused_483_; 
v_unused_482_ = lean_ctor_get(v_it_462_, 1);
lean_dec(v_unused_482_);
v_unused_483_ = lean_ctor_get(v_it_462_, 0);
lean_dec(v_unused_483_);
v___x_475_ = v_it_462_;
v_isShared_476_ = v_isSharedCheck_481_;
goto v_resetjp_474_;
}
else
{
lean_dec(v_it_462_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_481_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 1, v_right_468_);
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_fst_463_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_right_468_);
v___x_478_ = v_reuseFailAlloc_480_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
lean_object* v___x_479_; 
v___x_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
lean_ctor_set(v___x_479_, 1, v_substr_469_);
return v___x_479_;
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

// Lean compiler output
// Module: Init.Data.String.TakeDrop
// Imports: public import Init.Data.String.Substring
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
uint8_t l_String_instDecidableLtRaw___aux__1(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_String_Slice_Pos_revSkipWhile___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_Raw_takeWhileAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_dropSuffix___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_skipWhile___redArg(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l_Char_isWhitespace___boxed(lean_object*);
lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool(lean_object*);
lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(lean_object*);
lean_object* l_String_Slice_dropPrefix___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_drop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_string_drop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropRight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropRight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_string_dropright(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_takeEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_takeRight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_takeRight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_takeWhile___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_takeWhile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_takeWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropWhile___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropWhile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_takeEndWhile___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_takeEndWhile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_takeEndWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_takeRightWhile_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_takeRightWhile_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_takeRightWhile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_takeRightWhile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropEndWhile___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropEndWhile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropEndWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropRightWhile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropRightWhile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_skipPrefix_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_skipPrefix_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_skipPrefix_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_skipPrefixWhile___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_skipPrefixWhile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_skipPrefixWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_skip_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_skip_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_skip_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_skipWhile___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_skipWhile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_skipWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_startsWith___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_startsWith___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_startsWith(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_startsWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_isPrefixOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_string_isprefixof(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_isPrefixOfImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_endsWith___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_endsWith___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_endsWith(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_endsWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_skipSuffix_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_skipSuffix_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_skipSuffix_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_skipSuffixWhile___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_skipSuffixWhile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_skipSuffixWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_revSkip_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_revSkip_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_revSkip_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_revSkipWhile___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_revSkipWhile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_revSkipWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_String_trimAsciiEnd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Char_isWhitespace___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_trimAsciiEnd___closed__0 = (const lean_object*)&l_String_trimAsciiEnd___closed__0_value;
static lean_once_cell_t l_String_trimAsciiEnd___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_trimAsciiEnd___closed__1;
LEAN_EXPORT lean_object* l_String_trimAsciiEnd(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_trimRight_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_trimRight_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_trimRight(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_trimRight(lean_object*);
static lean_once_cell_t l_String_trimAsciiStart___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_trimAsciiStart___closed__0;
LEAN_EXPORT lean_object* l_String_trimAsciiStart(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00String_trimLeft_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00String_trimLeft_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_trimLeft(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_trimLeft(lean_object*);
LEAN_EXPORT lean_object* l_String_trimAscii(lean_object*);
LEAN_EXPORT lean_object* l_String_trim(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_trim(lean_object*);
LEAN_EXPORT lean_object* lean_string_trim(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextWhile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextWhile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_nextWhile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_nextWhile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_string_nextwhile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Pos_Raw_nextUntil___lam__0(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextUntil___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextUntil(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextUntil___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_nextUntil(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_nextUntil___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix___at___00String_stripPrefix_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix___at___00String_stripPrefix_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_stripPrefix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_stripPrefix___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_Slice_stripPrefix_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_Slice_stripPrefix_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_stripPrefix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_stripPrefix___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropSuffix___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropSuffix(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropSuffix___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropSuffix___at___00String_stripSuffix_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropSuffix___at___00String_stripSuffix_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_stripSuffix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_stripSuffix___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_Slice_stripSuffix_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_Slice_stripSuffix_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_stripSuffix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_stripSuffix___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_drop(lean_object* v_s_1_, lean_object* v_n_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_3_ = lean_unsigned_to_nat(0u);
v___x_4_ = lean_string_utf8_byte_size(v_s_1_);
lean_inc_ref(v_s_1_);
v___x_5_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5_, 0, v_s_1_);
lean_ctor_set(v___x_5_, 1, v___x_3_);
lean_ctor_set(v___x_5_, 2, v___x_4_);
v___x_6_ = l_String_Slice_Pos_nextn(v___x_5_, v___x_3_, v_n_2_);
lean_dec_ref(v___x_5_);
v___x_7_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_7_, 0, v_s_1_);
lean_ctor_set(v___x_7_, 1, v___x_6_);
lean_ctor_set(v___x_7_, 2, v___x_4_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lean_string_drop(lean_object* v_s_8_, lean_object* v_n_9_){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_10_ = lean_unsigned_to_nat(0u);
v___x_11_ = lean_string_utf8_byte_size(v_s_8_);
lean_inc_ref(v_s_8_);
v___x_12_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_12_, 0, v_s_8_);
lean_ctor_set(v___x_12_, 1, v___x_10_);
lean_ctor_set(v___x_12_, 2, v___x_11_);
v___x_13_ = l_String_Slice_Pos_nextn(v___x_12_, v___x_10_, v_n_9_);
lean_dec_ref(v___x_12_);
v___x_14_ = lean_string_utf8_extract(v_s_8_, v___x_13_, v___x_11_);
lean_dec(v___x_13_);
lean_dec_ref(v_s_8_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_String_dropEnd(lean_object* v_s_15_, lean_object* v_n_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_17_ = lean_unsigned_to_nat(0u);
v___x_18_ = lean_string_utf8_byte_size(v_s_15_);
lean_inc_ref(v_s_15_);
v___x_19_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_19_, 0, v_s_15_);
lean_ctor_set(v___x_19_, 1, v___x_17_);
lean_ctor_set(v___x_19_, 2, v___x_18_);
v___x_20_ = l_String_Slice_Pos_prevn(v___x_19_, v___x_18_, v_n_16_);
lean_dec_ref(v___x_19_);
v___x_21_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_21_, 0, v_s_15_);
lean_ctor_set(v___x_21_, 1, v___x_17_);
lean_ctor_set(v___x_21_, 2, v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_String_dropRight(lean_object* v_s_22_, lean_object* v_n_23_){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_24_ = lean_unsigned_to_nat(0u);
v___x_25_ = lean_string_utf8_byte_size(v_s_22_);
lean_inc_ref(v_s_22_);
v___x_26_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_26_, 0, v_s_22_);
lean_ctor_set(v___x_26_, 1, v___x_24_);
lean_ctor_set(v___x_26_, 2, v___x_25_);
v___x_27_ = l_String_Slice_Pos_prevn(v___x_26_, v___x_25_, v_n_23_);
lean_dec_ref(v___x_26_);
v___x_28_ = lean_string_utf8_extract(v_s_22_, v___x_24_, v___x_27_);
lean_dec(v___x_27_);
lean_dec_ref(v_s_22_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropRight(lean_object* v_s_29_, lean_object* v_n_30_){
_start:
{
lean_object* v_str_31_; lean_object* v_startInclusive_32_; lean_object* v_endExclusive_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_43_; 
v_str_31_ = lean_ctor_get(v_s_29_, 0);
lean_inc_ref(v_str_31_);
v_startInclusive_32_ = lean_ctor_get(v_s_29_, 1);
lean_inc(v_startInclusive_32_);
v_endExclusive_33_ = lean_ctor_get(v_s_29_, 2);
v___x_34_ = lean_nat_sub(v_endExclusive_33_, v_startInclusive_32_);
v___x_35_ = l_String_Slice_Pos_prevn(v_s_29_, v___x_34_, v_n_30_);
v_isSharedCheck_43_ = !lean_is_exclusive(v_s_29_);
if (v_isSharedCheck_43_ == 0)
{
lean_object* v_unused_44_; lean_object* v_unused_45_; lean_object* v_unused_46_; 
v_unused_44_ = lean_ctor_get(v_s_29_, 2);
lean_dec(v_unused_44_);
v_unused_45_ = lean_ctor_get(v_s_29_, 1);
lean_dec(v_unused_45_);
v_unused_46_ = lean_ctor_get(v_s_29_, 0);
lean_dec(v_unused_46_);
v___x_37_ = v_s_29_;
v_isShared_38_ = v_isSharedCheck_43_;
goto v_resetjp_36_;
}
else
{
lean_dec(v_s_29_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_43_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_39_; lean_object* v___x_41_; 
v___x_39_ = lean_nat_add(v_startInclusive_32_, v___x_35_);
lean_dec(v___x_35_);
if (v_isShared_38_ == 0)
{
lean_ctor_set(v___x_37_, 2, v___x_39_);
v___x_41_ = v___x_37_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v_str_31_);
lean_ctor_set(v_reuseFailAlloc_42_, 1, v_startInclusive_32_);
lean_ctor_set(v_reuseFailAlloc_42_, 2, v___x_39_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
}
LEAN_EXPORT lean_object* lean_string_dropright(lean_object* v_s_47_, lean_object* v_n_48_){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_49_ = lean_unsigned_to_nat(0u);
v___x_50_ = lean_string_utf8_byte_size(v_s_47_);
lean_inc_ref(v_s_47_);
v___x_51_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_51_, 0, v_s_47_);
lean_ctor_set(v___x_51_, 1, v___x_49_);
lean_ctor_set(v___x_51_, 2, v___x_50_);
v___x_52_ = l_String_Slice_Pos_prevn(v___x_51_, v___x_50_, v_n_48_);
lean_dec_ref(v___x_51_);
v___x_53_ = lean_string_utf8_extract(v_s_47_, v___x_49_, v___x_52_);
lean_dec(v___x_52_);
lean_dec_ref(v_s_47_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_String_take(lean_object* v_s_54_, lean_object* v_n_55_){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_56_ = lean_unsigned_to_nat(0u);
v___x_57_ = lean_string_utf8_byte_size(v_s_54_);
lean_inc_ref(v_s_54_);
v___x_58_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_58_, 0, v_s_54_);
lean_ctor_set(v___x_58_, 1, v___x_56_);
lean_ctor_set(v___x_58_, 2, v___x_57_);
v___x_59_ = l_String_Slice_Pos_nextn(v___x_58_, v___x_56_, v_n_55_);
lean_dec_ref(v___x_58_);
v___x_60_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_60_, 0, v_s_54_);
lean_ctor_set(v___x_60_, 1, v___x_56_);
lean_ctor_set(v___x_60_, 2, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_String_takeEnd(lean_object* v_s_61_, lean_object* v_n_62_){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_63_ = lean_unsigned_to_nat(0u);
v___x_64_ = lean_string_utf8_byte_size(v_s_61_);
lean_inc_ref(v_s_61_);
v___x_65_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_65_, 0, v_s_61_);
lean_ctor_set(v___x_65_, 1, v___x_63_);
lean_ctor_set(v___x_65_, 2, v___x_64_);
v___x_66_ = l_String_Slice_Pos_prevn(v___x_65_, v___x_64_, v_n_62_);
lean_dec_ref(v___x_65_);
v___x_67_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_67_, 0, v_s_61_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
lean_ctor_set(v___x_67_, 2, v___x_64_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_String_takeRight(lean_object* v_s_68_, lean_object* v_n_69_){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_70_ = lean_unsigned_to_nat(0u);
v___x_71_ = lean_string_utf8_byte_size(v_s_68_);
lean_inc_ref(v_s_68_);
v___x_72_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_72_, 0, v_s_68_);
lean_ctor_set(v___x_72_, 1, v___x_70_);
lean_ctor_set(v___x_72_, 2, v___x_71_);
v___x_73_ = l_String_Slice_Pos_prevn(v___x_72_, v___x_71_, v_n_69_);
lean_dec_ref(v___x_72_);
v___x_74_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_74_, 0, v_s_68_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
lean_ctor_set(v___x_74_, 2, v___x_71_);
v___x_75_ = l_String_Slice_toString(v___x_74_);
lean_dec_ref(v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeRight(lean_object* v_s_76_, lean_object* v_n_77_){
_start:
{
lean_object* v_str_78_; lean_object* v_startInclusive_79_; lean_object* v_endExclusive_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_90_; 
v_str_78_ = lean_ctor_get(v_s_76_, 0);
lean_inc_ref(v_str_78_);
v_startInclusive_79_ = lean_ctor_get(v_s_76_, 1);
lean_inc(v_startInclusive_79_);
v_endExclusive_80_ = lean_ctor_get(v_s_76_, 2);
lean_inc(v_endExclusive_80_);
v___x_81_ = lean_nat_sub(v_endExclusive_80_, v_startInclusive_79_);
v___x_82_ = l_String_Slice_Pos_prevn(v_s_76_, v___x_81_, v_n_77_);
v_isSharedCheck_90_ = !lean_is_exclusive(v_s_76_);
if (v_isSharedCheck_90_ == 0)
{
lean_object* v_unused_91_; lean_object* v_unused_92_; lean_object* v_unused_93_; 
v_unused_91_ = lean_ctor_get(v_s_76_, 2);
lean_dec(v_unused_91_);
v_unused_92_ = lean_ctor_get(v_s_76_, 1);
lean_dec(v_unused_92_);
v_unused_93_ = lean_ctor_get(v_s_76_, 0);
lean_dec(v_unused_93_);
v___x_84_ = v_s_76_;
v_isShared_85_ = v_isSharedCheck_90_;
goto v_resetjp_83_;
}
else
{
lean_dec(v_s_76_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_90_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_86_; lean_object* v___x_88_; 
v___x_86_ = lean_nat_add(v_startInclusive_79_, v___x_82_);
lean_dec(v___x_82_);
lean_dec(v_startInclusive_79_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 1, v___x_86_);
v___x_88_ = v___x_84_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_str_78_);
lean_ctor_set(v_reuseFailAlloc_89_, 1, v___x_86_);
lean_ctor_set(v_reuseFailAlloc_89_, 2, v_endExclusive_80_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_takeWhile___redArg(lean_object* v_s_94_, lean_object* v_inst_95_){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_96_ = lean_unsigned_to_nat(0u);
v___x_97_ = lean_string_utf8_byte_size(v_s_94_);
lean_inc_ref(v_s_94_);
v___x_98_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_98_, 0, v_s_94_);
lean_ctor_set(v___x_98_, 1, v___x_96_);
lean_ctor_set(v___x_98_, 2, v___x_97_);
v___x_99_ = l_String_Slice_Pos_skipWhile___redArg(v___x_98_, v___x_96_, v_inst_95_);
lean_dec_ref(v___x_98_);
v___x_100_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_100_, 0, v_s_94_);
lean_ctor_set(v___x_100_, 1, v___x_96_);
lean_ctor_set(v___x_100_, 2, v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_String_takeWhile(lean_object* v_00_u03c1_101_, lean_object* v_s_102_, lean_object* v_pat_103_, lean_object* v_inst_104_){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_105_ = lean_unsigned_to_nat(0u);
v___x_106_ = lean_string_utf8_byte_size(v_s_102_);
lean_inc_ref(v_s_102_);
v___x_107_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_107_, 0, v_s_102_);
lean_ctor_set(v___x_107_, 1, v___x_105_);
lean_ctor_set(v___x_107_, 2, v___x_106_);
v___x_108_ = l_String_Slice_Pos_skipWhile___redArg(v___x_107_, v___x_105_, v_inst_104_);
lean_dec_ref(v___x_107_);
v___x_109_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_109_, 0, v_s_102_);
lean_ctor_set(v___x_109_, 1, v___x_105_);
lean_ctor_set(v___x_109_, 2, v___x_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_String_takeWhile___boxed(lean_object* v_00_u03c1_110_, lean_object* v_s_111_, lean_object* v_pat_112_, lean_object* v_inst_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_String_takeWhile(v_00_u03c1_110_, v_s_111_, v_pat_112_, v_inst_113_);
lean_dec(v_pat_112_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_String_dropWhile___redArg(lean_object* v_s_115_, lean_object* v_inst_116_){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_117_ = lean_unsigned_to_nat(0u);
v___x_118_ = lean_string_utf8_byte_size(v_s_115_);
lean_inc_ref(v_s_115_);
v___x_119_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_119_, 0, v_s_115_);
lean_ctor_set(v___x_119_, 1, v___x_117_);
lean_ctor_set(v___x_119_, 2, v___x_118_);
v___x_120_ = l_String_Slice_Pos_skipWhile___redArg(v___x_119_, v___x_117_, v_inst_116_);
lean_dec_ref(v___x_119_);
v___x_121_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_121_, 0, v_s_115_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
lean_ctor_set(v___x_121_, 2, v___x_118_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_String_dropWhile(lean_object* v_00_u03c1_122_, lean_object* v_s_123_, lean_object* v_pat_124_, lean_object* v_inst_125_){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = lean_string_utf8_byte_size(v_s_123_);
lean_inc_ref(v_s_123_);
v___x_128_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_128_, 0, v_s_123_);
lean_ctor_set(v___x_128_, 1, v___x_126_);
lean_ctor_set(v___x_128_, 2, v___x_127_);
v___x_129_ = l_String_Slice_Pos_skipWhile___redArg(v___x_128_, v___x_126_, v_inst_125_);
lean_dec_ref(v___x_128_);
v___x_130_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_130_, 0, v_s_123_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
lean_ctor_set(v___x_130_, 2, v___x_127_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_String_dropWhile___boxed(lean_object* v_00_u03c1_131_, lean_object* v_s_132_, lean_object* v_pat_133_, lean_object* v_inst_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_String_dropWhile(v_00_u03c1_131_, v_s_132_, v_pat_133_, v_inst_134_);
lean_dec(v_pat_133_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_String_takeEndWhile___redArg(lean_object* v_s_136_, lean_object* v_inst_137_){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_138_ = lean_unsigned_to_nat(0u);
v___x_139_ = lean_string_utf8_byte_size(v_s_136_);
lean_inc_ref(v_s_136_);
v___x_140_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_140_, 0, v_s_136_);
lean_ctor_set(v___x_140_, 1, v___x_138_);
lean_ctor_set(v___x_140_, 2, v___x_139_);
v___x_141_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_140_, v___x_139_, v_inst_137_);
lean_dec_ref(v___x_140_);
v___x_142_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_142_, 0, v_s_136_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
lean_ctor_set(v___x_142_, 2, v___x_139_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_String_takeEndWhile(lean_object* v_00_u03c1_143_, lean_object* v_s_144_, lean_object* v_pat_145_, lean_object* v_inst_146_){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_147_ = lean_unsigned_to_nat(0u);
v___x_148_ = lean_string_utf8_byte_size(v_s_144_);
lean_inc_ref(v_s_144_);
v___x_149_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_149_, 0, v_s_144_);
lean_ctor_set(v___x_149_, 1, v___x_147_);
lean_ctor_set(v___x_149_, 2, v___x_148_);
v___x_150_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_149_, v___x_148_, v_inst_146_);
lean_dec_ref(v___x_149_);
v___x_151_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_151_, 0, v_s_144_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
lean_ctor_set(v___x_151_, 2, v___x_148_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_String_takeEndWhile___boxed(lean_object* v_00_u03c1_152_, lean_object* v_s_153_, lean_object* v_pat_154_, lean_object* v_inst_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_String_takeEndWhile(v_00_u03c1_152_, v_s_153_, v_pat_154_, v_inst_155_);
lean_dec(v_pat_154_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_takeRightWhile_spec__0(lean_object* v_p_157_, lean_object* v_s_158_, lean_object* v_pos_159_){
_start:
{
lean_object* v_str_160_; lean_object* v_startInclusive_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
v_str_160_ = lean_ctor_get(v_s_158_, 0);
v_startInclusive_161_ = lean_ctor_get(v_s_158_, 1);
v___x_162_ = lean_nat_add(v_startInclusive_161_, v_pos_159_);
v___x_163_ = lean_nat_sub(v___x_162_, v_startInclusive_161_);
v___x_164_ = lean_unsigned_to_nat(0u);
v___x_165_ = lean_nat_dec_eq(v___x_163_, v___x_164_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; uint32_t v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; uint8_t v___x_174_; 
lean_inc(v_startInclusive_161_);
lean_inc_ref(v_str_160_);
v___x_166_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_166_, 0, v_str_160_);
lean_ctor_set(v___x_166_, 1, v_startInclusive_161_);
lean_ctor_set(v___x_166_, 2, v___x_162_);
v___x_167_ = lean_unsigned_to_nat(1u);
v___x_168_ = lean_nat_sub(v___x_163_, v___x_167_);
lean_dec(v___x_163_);
v___x_169_ = l_String_Slice_posLE(v___x_166_, v___x_168_);
lean_dec_ref(v___x_166_);
v___x_170_ = lean_nat_add(v_startInclusive_161_, v___x_169_);
v___x_171_ = lean_string_utf8_get_fast(v_str_160_, v___x_170_);
lean_dec(v___x_170_);
v___x_172_ = lean_box_uint32(v___x_171_);
lean_inc_ref(v_p_157_);
v___x_173_ = lean_apply_1(v_p_157_, v___x_172_);
v___x_174_ = lean_unbox(v___x_173_);
if (v___x_174_ == 0)
{
lean_dec(v___x_169_);
lean_dec_ref(v_p_157_);
return v_pos_159_;
}
else
{
uint8_t v___x_175_; 
v___x_175_ = l_String_instDecidableLtRaw___aux__1(v___x_169_, v_pos_159_);
if (v___x_175_ == 0)
{
lean_dec(v___x_169_);
lean_dec_ref(v_p_157_);
return v_pos_159_;
}
else
{
lean_dec(v_pos_159_);
v_pos_159_ = v___x_169_;
goto _start;
}
}
}
else
{
lean_dec(v___x_163_);
lean_dec(v___x_162_);
lean_dec_ref(v_p_157_);
return v_pos_159_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_takeRightWhile_spec__0___boxed(lean_object* v_p_177_, lean_object* v_s_178_, lean_object* v_pos_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_String_Slice_Pos_revSkipWhile___at___00String_takeRightWhile_spec__0(v_p_177_, v_s_178_, v_pos_179_);
lean_dec_ref(v_s_178_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_String_takeRightWhile(lean_object* v_s_181_, lean_object* v_p_182_){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_183_ = lean_unsigned_to_nat(0u);
v___x_184_ = lean_string_utf8_byte_size(v_s_181_);
lean_inc_ref(v_s_181_);
v___x_185_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_185_, 0, v_s_181_);
lean_ctor_set(v___x_185_, 1, v___x_183_);
lean_ctor_set(v___x_185_, 2, v___x_184_);
v___x_186_ = l_String_Slice_Pos_revSkipWhile___at___00String_takeRightWhile_spec__0(v_p_182_, v___x_185_, v___x_184_);
lean_dec_ref(v___x_185_);
v___x_187_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_187_, 0, v_s_181_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
lean_ctor_set(v___x_187_, 2, v___x_184_);
v___x_188_ = l_String_Slice_toString(v___x_187_);
lean_dec_ref(v___x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeRightWhile(lean_object* v_s_189_, lean_object* v_p_190_){
_start:
{
lean_object* v_str_191_; lean_object* v_startInclusive_192_; lean_object* v_endExclusive_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_203_; 
v_str_191_ = lean_ctor_get(v_s_189_, 0);
lean_inc_ref(v_str_191_);
v_startInclusive_192_ = lean_ctor_get(v_s_189_, 1);
lean_inc(v_startInclusive_192_);
v_endExclusive_193_ = lean_ctor_get(v_s_189_, 2);
lean_inc(v_endExclusive_193_);
v___x_194_ = lean_nat_sub(v_endExclusive_193_, v_startInclusive_192_);
v___x_195_ = l_String_Slice_Pos_revSkipWhile___at___00String_takeRightWhile_spec__0(v_p_190_, v_s_189_, v___x_194_);
v_isSharedCheck_203_ = !lean_is_exclusive(v_s_189_);
if (v_isSharedCheck_203_ == 0)
{
lean_object* v_unused_204_; lean_object* v_unused_205_; lean_object* v_unused_206_; 
v_unused_204_ = lean_ctor_get(v_s_189_, 2);
lean_dec(v_unused_204_);
v_unused_205_ = lean_ctor_get(v_s_189_, 1);
lean_dec(v_unused_205_);
v_unused_206_ = lean_ctor_get(v_s_189_, 0);
lean_dec(v_unused_206_);
v___x_197_ = v_s_189_;
v_isShared_198_ = v_isSharedCheck_203_;
goto v_resetjp_196_;
}
else
{
lean_dec(v_s_189_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_203_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_199_; lean_object* v___x_201_; 
v___x_199_ = lean_nat_add(v_startInclusive_192_, v___x_195_);
lean_dec(v___x_195_);
lean_dec(v_startInclusive_192_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 1, v___x_199_);
v___x_201_ = v___x_197_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_str_191_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v___x_199_);
lean_ctor_set(v_reuseFailAlloc_202_, 2, v_endExclusive_193_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropEndWhile___redArg(lean_object* v_s_207_, lean_object* v_inst_208_){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_209_ = lean_unsigned_to_nat(0u);
v___x_210_ = lean_string_utf8_byte_size(v_s_207_);
lean_inc_ref(v_s_207_);
v___x_211_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_211_, 0, v_s_207_);
lean_ctor_set(v___x_211_, 1, v___x_209_);
lean_ctor_set(v___x_211_, 2, v___x_210_);
v___x_212_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_211_, v___x_210_, v_inst_208_);
lean_dec_ref(v___x_211_);
v___x_213_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_213_, 0, v_s_207_);
lean_ctor_set(v___x_213_, 1, v___x_209_);
lean_ctor_set(v___x_213_, 2, v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_String_dropEndWhile(lean_object* v_00_u03c1_214_, lean_object* v_s_215_, lean_object* v_pat_216_, lean_object* v_inst_217_){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_218_ = lean_unsigned_to_nat(0u);
v___x_219_ = lean_string_utf8_byte_size(v_s_215_);
lean_inc_ref(v_s_215_);
v___x_220_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_220_, 0, v_s_215_);
lean_ctor_set(v___x_220_, 1, v___x_218_);
lean_ctor_set(v___x_220_, 2, v___x_219_);
v___x_221_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_220_, v___x_219_, v_inst_217_);
lean_dec_ref(v___x_220_);
v___x_222_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_222_, 0, v_s_215_);
lean_ctor_set(v___x_222_, 1, v___x_218_);
lean_ctor_set(v___x_222_, 2, v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_String_dropEndWhile___boxed(lean_object* v_00_u03c1_223_, lean_object* v_s_224_, lean_object* v_pat_225_, lean_object* v_inst_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_String_dropEndWhile(v_00_u03c1_223_, v_s_224_, v_pat_225_, v_inst_226_);
lean_dec(v_pat_225_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_String_dropRightWhile(lean_object* v_s_228_, lean_object* v_p_229_){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_230_ = lean_unsigned_to_nat(0u);
v___x_231_ = lean_string_utf8_byte_size(v_s_228_);
lean_inc_ref(v_s_228_);
v___x_232_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_232_, 0, v_s_228_);
lean_ctor_set(v___x_232_, 1, v___x_230_);
lean_ctor_set(v___x_232_, 2, v___x_231_);
v___x_233_ = l_String_Slice_Pos_revSkipWhile___at___00String_takeRightWhile_spec__0(v_p_229_, v___x_232_, v___x_231_);
lean_dec_ref(v___x_232_);
v___x_234_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_234_, 0, v_s_228_);
lean_ctor_set(v___x_234_, 1, v___x_230_);
lean_ctor_set(v___x_234_, 2, v___x_233_);
v___x_235_ = l_String_Slice_toString(v___x_234_);
lean_dec_ref(v___x_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropRightWhile(lean_object* v_s_236_, lean_object* v_p_237_){
_start:
{
lean_object* v_str_238_; lean_object* v_startInclusive_239_; lean_object* v_endExclusive_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_250_; 
v_str_238_ = lean_ctor_get(v_s_236_, 0);
lean_inc_ref(v_str_238_);
v_startInclusive_239_ = lean_ctor_get(v_s_236_, 1);
lean_inc(v_startInclusive_239_);
v_endExclusive_240_ = lean_ctor_get(v_s_236_, 2);
v___x_241_ = lean_nat_sub(v_endExclusive_240_, v_startInclusive_239_);
v___x_242_ = l_String_Slice_Pos_revSkipWhile___at___00String_takeRightWhile_spec__0(v_p_237_, v_s_236_, v___x_241_);
v_isSharedCheck_250_ = !lean_is_exclusive(v_s_236_);
if (v_isSharedCheck_250_ == 0)
{
lean_object* v_unused_251_; lean_object* v_unused_252_; lean_object* v_unused_253_; 
v_unused_251_ = lean_ctor_get(v_s_236_, 2);
lean_dec(v_unused_251_);
v_unused_252_ = lean_ctor_get(v_s_236_, 1);
lean_dec(v_unused_252_);
v_unused_253_ = lean_ctor_get(v_s_236_, 0);
lean_dec(v_unused_253_);
v___x_244_ = v_s_236_;
v_isShared_245_ = v_isSharedCheck_250_;
goto v_resetjp_243_;
}
else
{
lean_dec(v_s_236_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_250_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_246_ = lean_nat_add(v_startInclusive_239_, v___x_242_);
lean_dec(v___x_242_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 2, v___x_246_);
v___x_248_ = v___x_244_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_str_238_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v_startInclusive_239_);
lean_ctor_set(v_reuseFailAlloc_249_, 2, v___x_246_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_skipPrefix_x3f___redArg(lean_object* v_s_254_, lean_object* v_inst_255_){
_start:
{
lean_object* v_skipPrefix_x3f_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_275_; 
v_skipPrefix_x3f_256_ = lean_ctor_get(v_inst_255_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v_inst_255_);
if (v_isSharedCheck_275_ == 0)
{
lean_object* v_unused_276_; lean_object* v_unused_277_; 
v_unused_276_ = lean_ctor_get(v_inst_255_, 2);
lean_dec(v_unused_276_);
v_unused_277_ = lean_ctor_get(v_inst_255_, 1);
lean_dec(v_unused_277_);
v___x_258_ = v_inst_255_;
v_isShared_259_ = v_isSharedCheck_275_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_skipPrefix_x3f_256_);
lean_dec(v_inst_255_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_275_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_260_ = lean_string_utf8_byte_size(v_s_254_);
v___x_261_ = lean_unsigned_to_nat(0u);
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 2, v___x_260_);
lean_ctor_set(v___x_258_, 1, v___x_261_);
lean_ctor_set(v___x_258_, 0, v_s_254_);
v___x_263_ = v___x_258_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_s_254_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v___x_261_);
lean_ctor_set(v_reuseFailAlloc_274_, 2, v___x_260_);
v___x_263_ = v_reuseFailAlloc_274_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
lean_object* v___x_264_; 
v___x_264_ = lean_apply_1(v_skipPrefix_x3f_256_, v___x_263_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v___x_265_; 
v___x_265_ = lean_box(0);
return v___x_265_;
}
else
{
lean_object* v_val_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_273_; 
v_val_266_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_273_ == 0)
{
v___x_268_ = v___x_264_;
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_val_266_);
lean_dec(v___x_264_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_271_; 
if (v_isShared_269_ == 0)
{
v___x_271_ = v___x_268_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_val_266_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_skipPrefix_x3f(lean_object* v_00_u03c1_278_, lean_object* v_s_279_, lean_object* v_pat_280_, lean_object* v_inst_281_){
_start:
{
lean_object* v_skipPrefix_x3f_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_301_; 
v_skipPrefix_x3f_282_ = lean_ctor_get(v_inst_281_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v_inst_281_);
if (v_isSharedCheck_301_ == 0)
{
lean_object* v_unused_302_; lean_object* v_unused_303_; 
v_unused_302_ = lean_ctor_get(v_inst_281_, 2);
lean_dec(v_unused_302_);
v_unused_303_ = lean_ctor_get(v_inst_281_, 1);
lean_dec(v_unused_303_);
v___x_284_ = v_inst_281_;
v_isShared_285_ = v_isSharedCheck_301_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_skipPrefix_x3f_282_);
lean_dec(v_inst_281_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_301_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_289_; 
v___x_286_ = lean_string_utf8_byte_size(v_s_279_);
v___x_287_ = lean_unsigned_to_nat(0u);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 2, v___x_286_);
lean_ctor_set(v___x_284_, 1, v___x_287_);
lean_ctor_set(v___x_284_, 0, v_s_279_);
v___x_289_ = v___x_284_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_s_279_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v___x_287_);
lean_ctor_set(v_reuseFailAlloc_300_, 2, v___x_286_);
v___x_289_ = v_reuseFailAlloc_300_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
lean_object* v___x_290_; 
v___x_290_ = lean_apply_1(v_skipPrefix_x3f_282_, v___x_289_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v___x_291_; 
v___x_291_ = lean_box(0);
return v___x_291_;
}
else
{
lean_object* v_val_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_299_; 
v_val_292_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_299_ == 0)
{
v___x_294_ = v___x_290_;
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_val_292_);
lean_dec(v___x_290_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_val_292_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_skipPrefix_x3f___boxed(lean_object* v_00_u03c1_304_, lean_object* v_s_305_, lean_object* v_pat_306_, lean_object* v_inst_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_String_skipPrefix_x3f(v_00_u03c1_304_, v_s_305_, v_pat_306_, v_inst_307_);
lean_dec(v_pat_306_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_String_skipPrefixWhile___redArg(lean_object* v_s_309_, lean_object* v_inst_310_){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_311_ = lean_unsigned_to_nat(0u);
v___x_312_ = lean_string_utf8_byte_size(v_s_309_);
v___x_313_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_313_, 0, v_s_309_);
lean_ctor_set(v___x_313_, 1, v___x_311_);
lean_ctor_set(v___x_313_, 2, v___x_312_);
v___x_314_ = l_String_Slice_Pos_skipWhile___redArg(v___x_313_, v___x_311_, v_inst_310_);
lean_dec_ref(v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_String_skipPrefixWhile(lean_object* v_00_u03c1_315_, lean_object* v_s_316_, lean_object* v_pat_317_, lean_object* v_inst_318_){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_319_ = lean_unsigned_to_nat(0u);
v___x_320_ = lean_string_utf8_byte_size(v_s_316_);
v___x_321_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_321_, 0, v_s_316_);
lean_ctor_set(v___x_321_, 1, v___x_319_);
lean_ctor_set(v___x_321_, 2, v___x_320_);
v___x_322_ = l_String_Slice_Pos_skipWhile___redArg(v___x_321_, v___x_319_, v_inst_318_);
lean_dec_ref(v___x_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_String_skipPrefixWhile___boxed(lean_object* v_00_u03c1_323_, lean_object* v_s_324_, lean_object* v_pat_325_, lean_object* v_inst_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_String_skipPrefixWhile(v_00_u03c1_323_, v_s_324_, v_pat_325_, v_inst_326_);
lean_dec(v_pat_325_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_skip_x3f___redArg(lean_object* v_s_328_, lean_object* v_pos_329_, lean_object* v_inst_330_){
_start:
{
lean_object* v_skipPrefix_x3f_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_350_; 
v_skipPrefix_x3f_331_ = lean_ctor_get(v_inst_330_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v_inst_330_);
if (v_isSharedCheck_350_ == 0)
{
lean_object* v_unused_351_; lean_object* v_unused_352_; 
v_unused_351_ = lean_ctor_get(v_inst_330_, 2);
lean_dec(v_unused_351_);
v_unused_352_ = lean_ctor_get(v_inst_330_, 1);
lean_dec(v_unused_352_);
v___x_333_ = v_inst_330_;
v_isShared_334_ = v_isSharedCheck_350_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_skipPrefix_x3f_331_);
lean_dec(v_inst_330_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_350_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; lean_object* v___x_337_; 
v___x_335_ = lean_string_utf8_byte_size(v_s_328_);
lean_inc(v_pos_329_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 2, v___x_335_);
lean_ctor_set(v___x_333_, 1, v_pos_329_);
lean_ctor_set(v___x_333_, 0, v_s_328_);
v___x_337_ = v___x_333_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_s_328_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v_pos_329_);
lean_ctor_set(v_reuseFailAlloc_349_, 2, v___x_335_);
v___x_337_ = v_reuseFailAlloc_349_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
lean_object* v___x_338_; 
v___x_338_ = lean_apply_1(v_skipPrefix_x3f_331_, v___x_337_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v___x_339_; 
lean_dec(v_pos_329_);
v___x_339_ = lean_box(0);
return v___x_339_;
}
else
{
lean_object* v_val_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_348_; 
v_val_340_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_348_ == 0)
{
v___x_342_ = v___x_338_;
v_isShared_343_ = v_isSharedCheck_348_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_val_340_);
lean_dec(v___x_338_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_348_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_344_; lean_object* v___x_346_; 
v___x_344_ = lean_nat_add(v_pos_329_, v_val_340_);
lean_dec(v_val_340_);
lean_dec(v_pos_329_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 0, v___x_344_);
v___x_346_ = v___x_342_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_344_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_skip_x3f(lean_object* v_00_u03c1_353_, lean_object* v_s_354_, lean_object* v_pos_355_, lean_object* v_pat_356_, lean_object* v_inst_357_){
_start:
{
lean_object* v_skipPrefix_x3f_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_377_; 
v_skipPrefix_x3f_358_ = lean_ctor_get(v_inst_357_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v_inst_357_);
if (v_isSharedCheck_377_ == 0)
{
lean_object* v_unused_378_; lean_object* v_unused_379_; 
v_unused_378_ = lean_ctor_get(v_inst_357_, 2);
lean_dec(v_unused_378_);
v_unused_379_ = lean_ctor_get(v_inst_357_, 1);
lean_dec(v_unused_379_);
v___x_360_ = v_inst_357_;
v_isShared_361_ = v_isSharedCheck_377_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_skipPrefix_x3f_358_);
lean_dec(v_inst_357_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_377_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v___x_364_; 
v___x_362_ = lean_string_utf8_byte_size(v_s_354_);
lean_inc(v_pos_355_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 2, v___x_362_);
lean_ctor_set(v___x_360_, 1, v_pos_355_);
lean_ctor_set(v___x_360_, 0, v_s_354_);
v___x_364_ = v___x_360_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_s_354_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_pos_355_);
lean_ctor_set(v_reuseFailAlloc_376_, 2, v___x_362_);
v___x_364_ = v_reuseFailAlloc_376_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
lean_object* v___x_365_; 
v___x_365_ = lean_apply_1(v_skipPrefix_x3f_358_, v___x_364_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v___x_366_; 
lean_dec(v_pos_355_);
v___x_366_ = lean_box(0);
return v___x_366_;
}
else
{
lean_object* v_val_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_375_; 
v_val_367_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_375_ == 0)
{
v___x_369_ = v___x_365_;
v_isShared_370_ = v_isSharedCheck_375_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_val_367_);
lean_dec(v___x_365_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_375_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_371_ = lean_nat_add(v_pos_355_, v_val_367_);
lean_dec(v_val_367_);
lean_dec(v_pos_355_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 0, v___x_371_);
v___x_373_ = v___x_369_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_371_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_skip_x3f___boxed(lean_object* v_00_u03c1_380_, lean_object* v_s_381_, lean_object* v_pos_382_, lean_object* v_pat_383_, lean_object* v_inst_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_String_Pos_skip_x3f(v_00_u03c1_380_, v_s_381_, v_pos_382_, v_pat_383_, v_inst_384_);
lean_dec(v_pat_383_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_skipWhile___redArg(lean_object* v_s_386_, lean_object* v_pos_387_, lean_object* v_inst_388_){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_389_ = lean_unsigned_to_nat(0u);
v___x_390_ = lean_string_utf8_byte_size(v_s_386_);
v___x_391_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_391_, 0, v_s_386_);
lean_ctor_set(v___x_391_, 1, v___x_389_);
lean_ctor_set(v___x_391_, 2, v___x_390_);
v___x_392_ = l_String_Slice_Pos_skipWhile___redArg(v___x_391_, v_pos_387_, v_inst_388_);
lean_dec_ref(v___x_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_skipWhile(lean_object* v_00_u03c1_393_, lean_object* v_s_394_, lean_object* v_pos_395_, lean_object* v_pat_396_, lean_object* v_inst_397_){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_398_ = lean_unsigned_to_nat(0u);
v___x_399_ = lean_string_utf8_byte_size(v_s_394_);
v___x_400_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_400_, 0, v_s_394_);
lean_ctor_set(v___x_400_, 1, v___x_398_);
lean_ctor_set(v___x_400_, 2, v___x_399_);
v___x_401_ = l_String_Slice_Pos_skipWhile___redArg(v___x_400_, v_pos_395_, v_inst_397_);
lean_dec_ref(v___x_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_skipWhile___boxed(lean_object* v_00_u03c1_402_, lean_object* v_s_403_, lean_object* v_pos_404_, lean_object* v_pat_405_, lean_object* v_inst_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_String_Pos_skipWhile(v_00_u03c1_402_, v_s_403_, v_pos_404_, v_pat_405_, v_inst_406_);
lean_dec(v_pat_405_);
return v_res_407_;
}
}
LEAN_EXPORT uint8_t l_String_startsWith___redArg(lean_object* v_s_408_, lean_object* v_inst_409_){
_start:
{
lean_object* v_startsWith_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_421_; 
v_startsWith_410_ = lean_ctor_get(v_inst_409_, 2);
v_isSharedCheck_421_ = !lean_is_exclusive(v_inst_409_);
if (v_isSharedCheck_421_ == 0)
{
lean_object* v_unused_422_; lean_object* v_unused_423_; 
v_unused_422_ = lean_ctor_get(v_inst_409_, 1);
lean_dec(v_unused_422_);
v_unused_423_ = lean_ctor_get(v_inst_409_, 0);
lean_dec(v_unused_423_);
v___x_412_ = v_inst_409_;
v_isShared_413_ = v_isSharedCheck_421_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_startsWith_410_);
lean_dec(v_inst_409_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_421_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_414_ = lean_string_utf8_byte_size(v_s_408_);
v___x_415_ = lean_unsigned_to_nat(0u);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 2, v___x_414_);
lean_ctor_set(v___x_412_, 1, v___x_415_);
lean_ctor_set(v___x_412_, 0, v_s_408_);
v___x_417_ = v___x_412_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_s_408_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_420_, 2, v___x_414_);
v___x_417_ = v_reuseFailAlloc_420_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_418_ = lean_apply_1(v_startsWith_410_, v___x_417_);
v___x_419_ = lean_unbox(v___x_418_);
return v___x_419_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_startsWith___redArg___boxed(lean_object* v_s_424_, lean_object* v_inst_425_){
_start:
{
uint8_t v_res_426_; lean_object* v_r_427_; 
v_res_426_ = l_String_startsWith___redArg(v_s_424_, v_inst_425_);
v_r_427_ = lean_box(v_res_426_);
return v_r_427_;
}
}
LEAN_EXPORT uint8_t l_String_startsWith(lean_object* v_00_u03c1_428_, lean_object* v_s_429_, lean_object* v_pat_430_, lean_object* v_inst_431_){
_start:
{
lean_object* v_startsWith_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_443_; 
v_startsWith_432_ = lean_ctor_get(v_inst_431_, 2);
v_isSharedCheck_443_ = !lean_is_exclusive(v_inst_431_);
if (v_isSharedCheck_443_ == 0)
{
lean_object* v_unused_444_; lean_object* v_unused_445_; 
v_unused_444_ = lean_ctor_get(v_inst_431_, 1);
lean_dec(v_unused_444_);
v_unused_445_ = lean_ctor_get(v_inst_431_, 0);
lean_dec(v_unused_445_);
v___x_434_ = v_inst_431_;
v_isShared_435_ = v_isSharedCheck_443_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_startsWith_432_);
lean_dec(v_inst_431_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_443_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_439_; 
v___x_436_ = lean_string_utf8_byte_size(v_s_429_);
v___x_437_ = lean_unsigned_to_nat(0u);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 2, v___x_436_);
lean_ctor_set(v___x_434_, 1, v___x_437_);
lean_ctor_set(v___x_434_, 0, v_s_429_);
v___x_439_ = v___x_434_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_s_429_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v___x_437_);
lean_ctor_set(v_reuseFailAlloc_442_, 2, v___x_436_);
v___x_439_ = v_reuseFailAlloc_442_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_440_ = lean_apply_1(v_startsWith_432_, v___x_439_);
v___x_441_ = lean_unbox(v___x_440_);
return v___x_441_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_startsWith___boxed(lean_object* v_00_u03c1_446_, lean_object* v_s_447_, lean_object* v_pat_448_, lean_object* v_inst_449_){
_start:
{
uint8_t v_res_450_; lean_object* v_r_451_; 
v_res_450_ = l_String_startsWith(v_00_u03c1_446_, v_s_447_, v_pat_448_, v_inst_449_);
lean_dec(v_pat_448_);
v_r_451_ = lean_box(v_res_450_);
return v_r_451_;
}
}
LEAN_EXPORT uint8_t l_String_isPrefixOf(lean_object* v_p_452_, lean_object* v_s_453_){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_454_ = lean_string_utf8_byte_size(v_s_453_);
v___x_455_ = lean_string_utf8_byte_size(v_p_452_);
v___x_456_ = lean_nat_dec_le(v___x_455_, v___x_454_);
if (v___x_456_ == 0)
{
return v___x_456_;
}
else
{
lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_457_ = lean_unsigned_to_nat(0u);
v___x_458_ = lean_string_memcmp(v_s_453_, v_p_452_, v___x_457_, v___x_457_, v___x_455_);
return v___x_458_;
}
}
}
LEAN_EXPORT lean_object* l_String_isPrefixOf___boxed(lean_object* v_p_459_, lean_object* v_s_460_){
_start:
{
uint8_t v_res_461_; lean_object* v_r_462_; 
v_res_461_ = l_String_isPrefixOf(v_p_459_, v_s_460_);
lean_dec_ref(v_s_460_);
lean_dec_ref(v_p_459_);
v_r_462_ = lean_box(v_res_461_);
return v_r_462_;
}
}
LEAN_EXPORT uint8_t lean_string_isprefixof(lean_object* v_p_463_, lean_object* v_s_464_){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_465_ = lean_string_utf8_byte_size(v_s_464_);
v___x_466_ = lean_string_utf8_byte_size(v_p_463_);
v___x_467_ = lean_nat_dec_le(v___x_466_, v___x_465_);
if (v___x_467_ == 0)
{
lean_dec_ref(v_s_464_);
lean_dec_ref(v_p_463_);
return v___x_467_;
}
else
{
lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_468_ = lean_unsigned_to_nat(0u);
v___x_469_ = lean_string_memcmp(v_s_464_, v_p_463_, v___x_468_, v___x_468_, v___x_466_);
lean_dec_ref(v_p_463_);
lean_dec_ref(v_s_464_);
return v___x_469_;
}
}
}
LEAN_EXPORT lean_object* l_String_Internal_isPrefixOfImpl___boxed(lean_object* v_p_470_, lean_object* v_s_471_){
_start:
{
uint8_t v_res_472_; lean_object* v_r_473_; 
v_res_472_ = lean_string_isprefixof(v_p_470_, v_s_471_);
v_r_473_ = lean_box(v_res_472_);
return v_r_473_;
}
}
LEAN_EXPORT uint8_t l_String_endsWith___redArg(lean_object* v_s_474_, lean_object* v_inst_475_){
_start:
{
lean_object* v_endsWith_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_487_; 
v_endsWith_476_ = lean_ctor_get(v_inst_475_, 2);
v_isSharedCheck_487_ = !lean_is_exclusive(v_inst_475_);
if (v_isSharedCheck_487_ == 0)
{
lean_object* v_unused_488_; lean_object* v_unused_489_; 
v_unused_488_ = lean_ctor_get(v_inst_475_, 1);
lean_dec(v_unused_488_);
v_unused_489_ = lean_ctor_get(v_inst_475_, 0);
lean_dec(v_unused_489_);
v___x_478_ = v_inst_475_;
v_isShared_479_ = v_isSharedCheck_487_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_endsWith_476_);
lean_dec(v_inst_475_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_487_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_483_; 
v___x_480_ = lean_string_utf8_byte_size(v_s_474_);
v___x_481_ = lean_unsigned_to_nat(0u);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 2, v___x_480_);
lean_ctor_set(v___x_478_, 1, v___x_481_);
lean_ctor_set(v___x_478_, 0, v_s_474_);
v___x_483_ = v___x_478_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_s_474_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v___x_481_);
lean_ctor_set(v_reuseFailAlloc_486_, 2, v___x_480_);
v___x_483_ = v_reuseFailAlloc_486_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_484_ = lean_apply_1(v_endsWith_476_, v___x_483_);
v___x_485_ = lean_unbox(v___x_484_);
return v___x_485_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_endsWith___redArg___boxed(lean_object* v_s_490_, lean_object* v_inst_491_){
_start:
{
uint8_t v_res_492_; lean_object* v_r_493_; 
v_res_492_ = l_String_endsWith___redArg(v_s_490_, v_inst_491_);
v_r_493_ = lean_box(v_res_492_);
return v_r_493_;
}
}
LEAN_EXPORT uint8_t l_String_endsWith(lean_object* v_00_u03c1_494_, lean_object* v_s_495_, lean_object* v_pat_496_, lean_object* v_inst_497_){
_start:
{
lean_object* v_endsWith_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_509_; 
v_endsWith_498_ = lean_ctor_get(v_inst_497_, 2);
v_isSharedCheck_509_ = !lean_is_exclusive(v_inst_497_);
if (v_isSharedCheck_509_ == 0)
{
lean_object* v_unused_510_; lean_object* v_unused_511_; 
v_unused_510_ = lean_ctor_get(v_inst_497_, 1);
lean_dec(v_unused_510_);
v_unused_511_ = lean_ctor_get(v_inst_497_, 0);
lean_dec(v_unused_511_);
v___x_500_ = v_inst_497_;
v_isShared_501_ = v_isSharedCheck_509_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_endsWith_498_);
lean_dec(v_inst_497_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_509_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_502_ = lean_string_utf8_byte_size(v_s_495_);
v___x_503_ = lean_unsigned_to_nat(0u);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 2, v___x_502_);
lean_ctor_set(v___x_500_, 1, v___x_503_);
lean_ctor_set(v___x_500_, 0, v_s_495_);
v___x_505_ = v___x_500_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_s_495_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v___x_503_);
lean_ctor_set(v_reuseFailAlloc_508_, 2, v___x_502_);
v___x_505_ = v_reuseFailAlloc_508_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_506_ = lean_apply_1(v_endsWith_498_, v___x_505_);
v___x_507_ = lean_unbox(v___x_506_);
return v___x_507_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_endsWith___boxed(lean_object* v_00_u03c1_512_, lean_object* v_s_513_, lean_object* v_pat_514_, lean_object* v_inst_515_){
_start:
{
uint8_t v_res_516_; lean_object* v_r_517_; 
v_res_516_ = l_String_endsWith(v_00_u03c1_512_, v_s_513_, v_pat_514_, v_inst_515_);
lean_dec(v_pat_514_);
v_r_517_ = lean_box(v_res_516_);
return v_r_517_;
}
}
LEAN_EXPORT lean_object* l_String_skipSuffix_x3f___redArg(lean_object* v_s_518_, lean_object* v_inst_519_){
_start:
{
lean_object* v_skipSuffix_x3f_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_539_; 
v_skipSuffix_x3f_520_ = lean_ctor_get(v_inst_519_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v_inst_519_);
if (v_isSharedCheck_539_ == 0)
{
lean_object* v_unused_540_; lean_object* v_unused_541_; 
v_unused_540_ = lean_ctor_get(v_inst_519_, 2);
lean_dec(v_unused_540_);
v_unused_541_ = lean_ctor_get(v_inst_519_, 1);
lean_dec(v_unused_541_);
v___x_522_ = v_inst_519_;
v_isShared_523_ = v_isSharedCheck_539_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_skipSuffix_x3f_520_);
lean_dec(v_inst_519_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_539_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_527_; 
v___x_524_ = lean_string_utf8_byte_size(v_s_518_);
v___x_525_ = lean_unsigned_to_nat(0u);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 2, v___x_524_);
lean_ctor_set(v___x_522_, 1, v___x_525_);
lean_ctor_set(v___x_522_, 0, v_s_518_);
v___x_527_ = v___x_522_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_s_518_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v___x_525_);
lean_ctor_set(v_reuseFailAlloc_538_, 2, v___x_524_);
v___x_527_ = v_reuseFailAlloc_538_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v___x_528_; 
v___x_528_ = lean_apply_1(v_skipSuffix_x3f_520_, v___x_527_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v___x_529_; 
v___x_529_ = lean_box(0);
return v___x_529_;
}
else
{
lean_object* v_val_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_537_; 
v_val_530_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_537_ == 0)
{
v___x_532_ = v___x_528_;
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_val_530_);
lean_dec(v___x_528_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_533_ == 0)
{
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_val_530_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_skipSuffix_x3f(lean_object* v_00_u03c1_542_, lean_object* v_s_543_, lean_object* v_pat_544_, lean_object* v_inst_545_){
_start:
{
lean_object* v_skipSuffix_x3f_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_565_; 
v_skipSuffix_x3f_546_ = lean_ctor_get(v_inst_545_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v_inst_545_);
if (v_isSharedCheck_565_ == 0)
{
lean_object* v_unused_566_; lean_object* v_unused_567_; 
v_unused_566_ = lean_ctor_get(v_inst_545_, 2);
lean_dec(v_unused_566_);
v_unused_567_ = lean_ctor_get(v_inst_545_, 1);
lean_dec(v_unused_567_);
v___x_548_ = v_inst_545_;
v_isShared_549_ = v_isSharedCheck_565_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_skipSuffix_x3f_546_);
lean_dec(v_inst_545_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_565_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_550_ = lean_string_utf8_byte_size(v_s_543_);
v___x_551_ = lean_unsigned_to_nat(0u);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 2, v___x_550_);
lean_ctor_set(v___x_548_, 1, v___x_551_);
lean_ctor_set(v___x_548_, 0, v_s_543_);
v___x_553_ = v___x_548_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_s_543_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v___x_551_);
lean_ctor_set(v_reuseFailAlloc_564_, 2, v___x_550_);
v___x_553_ = v_reuseFailAlloc_564_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_object* v___x_554_; 
v___x_554_ = lean_apply_1(v_skipSuffix_x3f_546_, v___x_553_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v___x_555_; 
v___x_555_ = lean_box(0);
return v___x_555_;
}
else
{
lean_object* v_val_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
v_val_556_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_554_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_val_556_);
lean_dec(v___x_554_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_val_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_skipSuffix_x3f___boxed(lean_object* v_00_u03c1_568_, lean_object* v_s_569_, lean_object* v_pat_570_, lean_object* v_inst_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_String_skipSuffix_x3f(v_00_u03c1_568_, v_s_569_, v_pat_570_, v_inst_571_);
lean_dec(v_pat_570_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_String_skipSuffixWhile___redArg(lean_object* v_s_573_, lean_object* v_inst_574_){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_575_ = lean_unsigned_to_nat(0u);
v___x_576_ = lean_string_utf8_byte_size(v_s_573_);
v___x_577_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_577_, 0, v_s_573_);
lean_ctor_set(v___x_577_, 1, v___x_575_);
lean_ctor_set(v___x_577_, 2, v___x_576_);
v___x_578_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_577_, v___x_576_, v_inst_574_);
lean_dec_ref(v___x_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_String_skipSuffixWhile(lean_object* v_00_u03c1_579_, lean_object* v_s_580_, lean_object* v_pat_581_, lean_object* v_inst_582_){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_583_ = lean_unsigned_to_nat(0u);
v___x_584_ = lean_string_utf8_byte_size(v_s_580_);
v___x_585_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_585_, 0, v_s_580_);
lean_ctor_set(v___x_585_, 1, v___x_583_);
lean_ctor_set(v___x_585_, 2, v___x_584_);
v___x_586_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_585_, v___x_584_, v_inst_582_);
lean_dec_ref(v___x_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_String_skipSuffixWhile___boxed(lean_object* v_00_u03c1_587_, lean_object* v_s_588_, lean_object* v_pat_589_, lean_object* v_inst_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_String_skipSuffixWhile(v_00_u03c1_587_, v_s_588_, v_pat_589_, v_inst_590_);
lean_dec(v_pat_589_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_revSkip_x3f___redArg(lean_object* v_s_592_, lean_object* v_pos_593_, lean_object* v_inst_594_){
_start:
{
lean_object* v_skipSuffix_x3f_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_614_; 
v_skipSuffix_x3f_595_ = lean_ctor_get(v_inst_594_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v_inst_594_);
if (v_isSharedCheck_614_ == 0)
{
lean_object* v_unused_615_; lean_object* v_unused_616_; 
v_unused_615_ = lean_ctor_get(v_inst_594_, 2);
lean_dec(v_unused_615_);
v_unused_616_ = lean_ctor_get(v_inst_594_, 1);
lean_dec(v_unused_616_);
v___x_597_ = v_inst_594_;
v_isShared_598_ = v_isSharedCheck_614_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_skipSuffix_x3f_595_);
lean_dec(v_inst_594_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_614_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_599_; lean_object* v___x_601_; 
v___x_599_ = lean_string_utf8_byte_size(v_s_592_);
lean_inc(v_pos_593_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 2, v___x_599_);
lean_ctor_set(v___x_597_, 1, v_pos_593_);
lean_ctor_set(v___x_597_, 0, v_s_592_);
v___x_601_ = v___x_597_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_s_592_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_pos_593_);
lean_ctor_set(v_reuseFailAlloc_613_, 2, v___x_599_);
v___x_601_ = v_reuseFailAlloc_613_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
lean_object* v___x_602_; 
v___x_602_ = lean_apply_1(v_skipSuffix_x3f_595_, v___x_601_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v___x_603_; 
lean_dec(v_pos_593_);
v___x_603_ = lean_box(0);
return v___x_603_;
}
else
{
lean_object* v_val_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_612_; 
v_val_604_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_612_ == 0)
{
v___x_606_ = v___x_602_;
v_isShared_607_ = v_isSharedCheck_612_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_val_604_);
lean_dec(v___x_602_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_612_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_608_ = lean_nat_add(v_pos_593_, v_val_604_);
lean_dec(v_val_604_);
lean_dec(v_pos_593_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v___x_608_);
v___x_610_ = v___x_606_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_608_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_revSkip_x3f(lean_object* v_00_u03c1_617_, lean_object* v_s_618_, lean_object* v_pos_619_, lean_object* v_pat_620_, lean_object* v_inst_621_){
_start:
{
lean_object* v_skipSuffix_x3f_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_641_; 
v_skipSuffix_x3f_622_ = lean_ctor_get(v_inst_621_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v_inst_621_);
if (v_isSharedCheck_641_ == 0)
{
lean_object* v_unused_642_; lean_object* v_unused_643_; 
v_unused_642_ = lean_ctor_get(v_inst_621_, 2);
lean_dec(v_unused_642_);
v_unused_643_ = lean_ctor_get(v_inst_621_, 1);
lean_dec(v_unused_643_);
v___x_624_ = v_inst_621_;
v_isShared_625_ = v_isSharedCheck_641_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_skipSuffix_x3f_622_);
lean_dec(v_inst_621_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_641_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_626_; lean_object* v___x_628_; 
v___x_626_ = lean_string_utf8_byte_size(v_s_618_);
lean_inc(v_pos_619_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 2, v___x_626_);
lean_ctor_set(v___x_624_, 1, v_pos_619_);
lean_ctor_set(v___x_624_, 0, v_s_618_);
v___x_628_ = v___x_624_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_s_618_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_pos_619_);
lean_ctor_set(v_reuseFailAlloc_640_, 2, v___x_626_);
v___x_628_ = v_reuseFailAlloc_640_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_object* v___x_629_; 
v___x_629_ = lean_apply_1(v_skipSuffix_x3f_622_, v___x_628_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v___x_630_; 
lean_dec(v_pos_619_);
v___x_630_ = lean_box(0);
return v___x_630_;
}
else
{
lean_object* v_val_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_639_; 
v_val_631_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_639_ == 0)
{
v___x_633_ = v___x_629_;
v_isShared_634_ = v_isSharedCheck_639_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_val_631_);
lean_dec(v___x_629_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_639_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_635_ = lean_nat_add(v_pos_619_, v_val_631_);
lean_dec(v_val_631_);
lean_dec(v_pos_619_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 0, v___x_635_);
v___x_637_ = v___x_633_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_635_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_revSkip_x3f___boxed(lean_object* v_00_u03c1_644_, lean_object* v_s_645_, lean_object* v_pos_646_, lean_object* v_pat_647_, lean_object* v_inst_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_String_Pos_revSkip_x3f(v_00_u03c1_644_, v_s_645_, v_pos_646_, v_pat_647_, v_inst_648_);
lean_dec(v_pat_647_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_revSkipWhile___redArg(lean_object* v_s_650_, lean_object* v_pos_651_, lean_object* v_inst_652_){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_653_ = lean_unsigned_to_nat(0u);
v___x_654_ = lean_string_utf8_byte_size(v_s_650_);
v___x_655_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_655_, 0, v_s_650_);
lean_ctor_set(v___x_655_, 1, v___x_653_);
lean_ctor_set(v___x_655_, 2, v___x_654_);
v___x_656_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_655_, v_pos_651_, v_inst_652_);
lean_dec_ref(v___x_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_revSkipWhile(lean_object* v_00_u03c1_657_, lean_object* v_s_658_, lean_object* v_pos_659_, lean_object* v_pat_660_, lean_object* v_inst_661_){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_662_ = lean_unsigned_to_nat(0u);
v___x_663_ = lean_string_utf8_byte_size(v_s_658_);
v___x_664_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_664_, 0, v_s_658_);
lean_ctor_set(v___x_664_, 1, v___x_662_);
lean_ctor_set(v___x_664_, 2, v___x_663_);
v___x_665_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_664_, v_pos_659_, v_inst_661_);
lean_dec_ref(v___x_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_revSkipWhile___boxed(lean_object* v_00_u03c1_666_, lean_object* v_s_667_, lean_object* v_pos_668_, lean_object* v_pat_669_, lean_object* v_inst_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_String_Pos_revSkipWhile(v_00_u03c1_666_, v_s_667_, v_pos_668_, v_pat_669_, v_inst_670_);
lean_dec(v_pat_669_);
return v_res_671_;
}
}
static lean_object* _init_l_String_trimAsciiEnd___closed__1(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = ((lean_object*)(l_String_trimAsciiEnd___closed__0));
v___x_674_ = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool(v___x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_String_trimAsciiEnd(lean_object* v_s_675_){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_676_ = lean_unsigned_to_nat(0u);
v___x_677_ = lean_string_utf8_byte_size(v_s_675_);
lean_inc_ref(v_s_675_);
v___x_678_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_678_, 0, v_s_675_);
lean_ctor_set(v___x_678_, 1, v___x_676_);
lean_ctor_set(v___x_678_, 2, v___x_677_);
v___x_679_ = lean_obj_once(&l_String_trimAsciiEnd___closed__1, &l_String_trimAsciiEnd___closed__1_once, _init_l_String_trimAsciiEnd___closed__1);
v___x_680_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_678_, v___x_677_, v___x_679_);
lean_dec_ref(v___x_678_);
v___x_681_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_681_, 0, v_s_675_);
lean_ctor_set(v___x_681_, 1, v___x_676_);
lean_ctor_set(v___x_681_, 2, v___x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_trimRight_spec__0(lean_object* v_s_682_, lean_object* v_pos_683_){
_start:
{
lean_object* v_str_684_; lean_object* v_startInclusive_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; uint8_t v___x_689_; 
v_str_684_ = lean_ctor_get(v_s_682_, 0);
v_startInclusive_685_ = lean_ctor_get(v_s_682_, 1);
v___x_686_ = lean_nat_add(v_startInclusive_685_, v_pos_683_);
v___x_687_ = lean_nat_sub(v___x_686_, v_startInclusive_685_);
v___x_688_ = lean_unsigned_to_nat(0u);
v___x_689_ = lean_nat_dec_eq(v___x_687_, v___x_688_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; uint8_t v___y_698_; lean_object* v___x_699_; uint32_t v___x_700_; uint8_t v___y_702_; uint32_t v___x_707_; uint8_t v___x_708_; 
lean_inc(v_startInclusive_685_);
lean_inc_ref(v_str_684_);
v___x_690_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_690_, 0, v_str_684_);
lean_ctor_set(v___x_690_, 1, v_startInclusive_685_);
lean_ctor_set(v___x_690_, 2, v___x_686_);
v___x_691_ = lean_unsigned_to_nat(1u);
v___x_692_ = lean_nat_sub(v___x_687_, v___x_691_);
lean_dec(v___x_687_);
v___x_693_ = l_String_Slice_posLE(v___x_690_, v___x_692_);
lean_dec_ref(v___x_690_);
v___x_699_ = lean_nat_add(v_startInclusive_685_, v___x_693_);
v___x_700_ = lean_string_utf8_get_fast(v_str_684_, v___x_699_);
lean_dec(v___x_699_);
v___x_707_ = 32;
v___x_708_ = lean_uint32_dec_eq(v___x_700_, v___x_707_);
if (v___x_708_ == 0)
{
uint32_t v___x_709_; uint8_t v___x_710_; 
v___x_709_ = 9;
v___x_710_ = lean_uint32_dec_eq(v___x_700_, v___x_709_);
v___y_702_ = v___x_710_;
goto v___jp_701_;
}
else
{
v___y_702_ = v___x_708_;
goto v___jp_701_;
}
v___jp_694_:
{
uint8_t v___x_695_; 
v___x_695_ = l_String_instDecidableLtRaw___aux__1(v___x_693_, v_pos_683_);
if (v___x_695_ == 0)
{
lean_dec(v___x_693_);
return v_pos_683_;
}
else
{
lean_dec(v_pos_683_);
v_pos_683_ = v___x_693_;
goto _start;
}
}
v___jp_697_:
{
if (v___y_698_ == 0)
{
lean_dec(v___x_693_);
return v_pos_683_;
}
else
{
goto v___jp_694_;
}
}
v___jp_701_:
{
if (v___y_702_ == 0)
{
uint32_t v___x_703_; uint8_t v___x_704_; 
v___x_703_ = 13;
v___x_704_ = lean_uint32_dec_eq(v___x_700_, v___x_703_);
if (v___x_704_ == 0)
{
uint32_t v___x_705_; uint8_t v___x_706_; 
v___x_705_ = 10;
v___x_706_ = lean_uint32_dec_eq(v___x_700_, v___x_705_);
v___y_698_ = v___x_706_;
goto v___jp_697_;
}
else
{
v___y_698_ = v___x_704_;
goto v___jp_697_;
}
}
else
{
goto v___jp_694_;
}
}
}
else
{
lean_dec(v___x_687_);
lean_dec(v___x_686_);
return v_pos_683_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_trimRight_spec__0___boxed(lean_object* v_s_711_, lean_object* v_pos_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_String_Slice_Pos_revSkipWhile___at___00String_trimRight_spec__0(v_s_711_, v_pos_712_);
lean_dec_ref(v_s_711_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_String_trimRight(lean_object* v_s_714_){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_715_ = lean_unsigned_to_nat(0u);
v___x_716_ = lean_string_utf8_byte_size(v_s_714_);
lean_inc_ref(v_s_714_);
v___x_717_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_717_, 0, v_s_714_);
lean_ctor_set(v___x_717_, 1, v___x_715_);
lean_ctor_set(v___x_717_, 2, v___x_716_);
v___x_718_ = l_String_Slice_Pos_revSkipWhile___at___00String_trimRight_spec__0(v___x_717_, v___x_716_);
lean_dec_ref(v___x_717_);
v___x_719_ = lean_string_utf8_extract(v_s_714_, v___x_715_, v___x_718_);
lean_dec(v___x_718_);
lean_dec_ref(v_s_714_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimRight(lean_object* v_s_720_){
_start:
{
lean_object* v_str_721_; lean_object* v_startInclusive_722_; lean_object* v_endExclusive_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_733_; 
v_str_721_ = lean_ctor_get(v_s_720_, 0);
lean_inc_ref(v_str_721_);
v_startInclusive_722_ = lean_ctor_get(v_s_720_, 1);
lean_inc(v_startInclusive_722_);
v_endExclusive_723_ = lean_ctor_get(v_s_720_, 2);
v___x_724_ = lean_nat_sub(v_endExclusive_723_, v_startInclusive_722_);
v___x_725_ = l_String_Slice_Pos_revSkipWhile___at___00String_trimRight_spec__0(v_s_720_, v___x_724_);
v_isSharedCheck_733_ = !lean_is_exclusive(v_s_720_);
if (v_isSharedCheck_733_ == 0)
{
lean_object* v_unused_734_; lean_object* v_unused_735_; lean_object* v_unused_736_; 
v_unused_734_ = lean_ctor_get(v_s_720_, 2);
lean_dec(v_unused_734_);
v_unused_735_ = lean_ctor_get(v_s_720_, 1);
lean_dec(v_unused_735_);
v_unused_736_ = lean_ctor_get(v_s_720_, 0);
lean_dec(v_unused_736_);
v___x_727_ = v_s_720_;
v_isShared_728_ = v_isSharedCheck_733_;
goto v_resetjp_726_;
}
else
{
lean_dec(v_s_720_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_733_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; lean_object* v___x_731_; 
v___x_729_ = lean_nat_add(v_startInclusive_722_, v___x_725_);
lean_dec(v___x_725_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 2, v___x_729_);
v___x_731_ = v___x_727_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_str_721_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_startInclusive_722_);
lean_ctor_set(v_reuseFailAlloc_732_, 2, v___x_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
static lean_object* _init_l_String_trimAsciiStart___closed__0(void){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = ((lean_object*)(l_String_trimAsciiEnd___closed__0));
v___x_738_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___x_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_String_trimAsciiStart(lean_object* v_s_739_){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_740_ = lean_unsigned_to_nat(0u);
v___x_741_ = lean_string_utf8_byte_size(v_s_739_);
lean_inc_ref(v_s_739_);
v___x_742_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_742_, 0, v_s_739_);
lean_ctor_set(v___x_742_, 1, v___x_740_);
lean_ctor_set(v___x_742_, 2, v___x_741_);
v___x_743_ = lean_obj_once(&l_String_trimAsciiStart___closed__0, &l_String_trimAsciiStart___closed__0_once, _init_l_String_trimAsciiStart___closed__0);
v___x_744_ = l_String_Slice_Pos_skipWhile___redArg(v___x_742_, v___x_740_, v___x_743_);
lean_dec_ref(v___x_742_);
v___x_745_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_745_, 0, v_s_739_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
lean_ctor_set(v___x_745_, 2, v___x_741_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00String_trimLeft_spec__0(lean_object* v_s_746_, lean_object* v_pos_747_){
_start:
{
lean_object* v_str_748_; lean_object* v_startInclusive_749_; lean_object* v_endExclusive_750_; lean_object* v___x_751_; uint8_t v___y_759_; lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v_str_748_ = lean_ctor_get(v_s_746_, 0);
v_startInclusive_749_ = lean_ctor_get(v_s_746_, 1);
v_endExclusive_750_ = lean_ctor_get(v_s_746_, 2);
v___x_751_ = lean_nat_add(v_startInclusive_749_, v_pos_747_);
v___x_760_ = lean_unsigned_to_nat(0u);
v___x_761_ = lean_nat_sub(v_endExclusive_750_, v___x_751_);
v___x_762_ = lean_nat_dec_eq(v___x_760_, v___x_761_);
lean_dec(v___x_761_);
if (v___x_762_ == 0)
{
uint32_t v___x_763_; uint8_t v___y_765_; uint32_t v___x_770_; uint8_t v___x_771_; 
v___x_763_ = lean_string_utf8_get_fast(v_str_748_, v___x_751_);
v___x_770_ = 32;
v___x_771_ = lean_uint32_dec_eq(v___x_763_, v___x_770_);
if (v___x_771_ == 0)
{
uint32_t v___x_772_; uint8_t v___x_773_; 
v___x_772_ = 9;
v___x_773_ = lean_uint32_dec_eq(v___x_763_, v___x_772_);
v___y_765_ = v___x_773_;
goto v___jp_764_;
}
else
{
v___y_765_ = v___x_771_;
goto v___jp_764_;
}
v___jp_764_:
{
if (v___y_765_ == 0)
{
uint32_t v___x_766_; uint8_t v___x_767_; 
v___x_766_ = 13;
v___x_767_ = lean_uint32_dec_eq(v___x_763_, v___x_766_);
if (v___x_767_ == 0)
{
uint32_t v___x_768_; uint8_t v___x_769_; 
v___x_768_ = 10;
v___x_769_ = lean_uint32_dec_eq(v___x_763_, v___x_768_);
v___y_759_ = v___x_769_;
goto v___jp_758_;
}
else
{
v___y_759_ = v___x_767_;
goto v___jp_758_;
}
}
else
{
goto v___jp_752_;
}
}
}
else
{
lean_dec(v___x_751_);
return v_pos_747_;
}
v___jp_752_:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_753_ = lean_string_utf8_next_fast(v_str_748_, v___x_751_);
v___x_754_ = lean_nat_sub(v___x_753_, v___x_751_);
lean_dec(v___x_751_);
v___x_755_ = lean_nat_add(v_pos_747_, v___x_754_);
lean_dec(v___x_754_);
v___x_756_ = l_String_instDecidableLtRaw___aux__1(v_pos_747_, v___x_755_);
if (v___x_756_ == 0)
{
lean_dec(v___x_755_);
return v_pos_747_;
}
else
{
lean_dec(v_pos_747_);
v_pos_747_ = v___x_755_;
goto _start;
}
}
v___jp_758_:
{
if (v___y_759_ == 0)
{
lean_dec(v___x_751_);
return v_pos_747_;
}
else
{
goto v___jp_752_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00String_trimLeft_spec__0___boxed(lean_object* v_s_774_, lean_object* v_pos_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_String_Slice_Pos_skipWhile___at___00String_trimLeft_spec__0(v_s_774_, v_pos_775_);
lean_dec_ref(v_s_774_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_String_trimLeft(lean_object* v_s_777_){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_778_ = lean_unsigned_to_nat(0u);
v___x_779_ = lean_string_utf8_byte_size(v_s_777_);
lean_inc_ref(v_s_777_);
v___x_780_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_780_, 0, v_s_777_);
lean_ctor_set(v___x_780_, 1, v___x_778_);
lean_ctor_set(v___x_780_, 2, v___x_779_);
v___x_781_ = l_String_Slice_Pos_skipWhile___at___00String_trimLeft_spec__0(v___x_780_, v___x_778_);
lean_dec_ref(v___x_780_);
v___x_782_ = lean_string_utf8_extract(v_s_777_, v___x_781_, v___x_779_);
lean_dec(v___x_781_);
lean_dec_ref(v_s_777_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimLeft(lean_object* v_s_783_){
_start:
{
lean_object* v_str_784_; lean_object* v_startInclusive_785_; lean_object* v_endExclusive_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_796_; 
v_str_784_ = lean_ctor_get(v_s_783_, 0);
lean_inc_ref(v_str_784_);
v_startInclusive_785_ = lean_ctor_get(v_s_783_, 1);
lean_inc(v_startInclusive_785_);
v_endExclusive_786_ = lean_ctor_get(v_s_783_, 2);
lean_inc(v_endExclusive_786_);
v___x_787_ = lean_unsigned_to_nat(0u);
v___x_788_ = l_String_Slice_Pos_skipWhile___at___00String_trimLeft_spec__0(v_s_783_, v___x_787_);
v_isSharedCheck_796_ = !lean_is_exclusive(v_s_783_);
if (v_isSharedCheck_796_ == 0)
{
lean_object* v_unused_797_; lean_object* v_unused_798_; lean_object* v_unused_799_; 
v_unused_797_ = lean_ctor_get(v_s_783_, 2);
lean_dec(v_unused_797_);
v_unused_798_ = lean_ctor_get(v_s_783_, 1);
lean_dec(v_unused_798_);
v_unused_799_ = lean_ctor_get(v_s_783_, 0);
lean_dec(v_unused_799_);
v___x_790_ = v_s_783_;
v_isShared_791_ = v_isSharedCheck_796_;
goto v_resetjp_789_;
}
else
{
lean_dec(v_s_783_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_796_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_792_ = lean_nat_add(v_startInclusive_785_, v___x_788_);
lean_dec(v___x_788_);
lean_dec(v_startInclusive_785_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 1, v___x_792_);
v___x_794_ = v___x_790_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_str_784_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v___x_792_);
lean_ctor_set(v_reuseFailAlloc_795_, 2, v_endExclusive_786_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_trimAscii(lean_object* v_s_800_){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_801_ = lean_unsigned_to_nat(0u);
v___x_802_ = lean_string_utf8_byte_size(v_s_800_);
v___x_803_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_803_, 0, v_s_800_);
lean_ctor_set(v___x_803_, 1, v___x_801_);
lean_ctor_set(v___x_803_, 2, v___x_802_);
v___x_804_ = l_String_Slice_trimAscii(v___x_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_String_trim(lean_object* v_s_805_){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v_str_810_; lean_object* v_startInclusive_811_; lean_object* v_endExclusive_812_; lean_object* v___x_813_; 
v___x_806_ = lean_unsigned_to_nat(0u);
v___x_807_ = lean_string_utf8_byte_size(v_s_805_);
v___x_808_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_808_, 0, v_s_805_);
lean_ctor_set(v___x_808_, 1, v___x_806_);
lean_ctor_set(v___x_808_, 2, v___x_807_);
v___x_809_ = l_String_Slice_trimAscii(v___x_808_);
v_str_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc_ref(v_str_810_);
v_startInclusive_811_ = lean_ctor_get(v___x_809_, 1);
lean_inc(v_startInclusive_811_);
v_endExclusive_812_ = lean_ctor_get(v___x_809_, 2);
lean_inc(v_endExclusive_812_);
lean_dec_ref(v___x_809_);
v___x_813_ = lean_string_utf8_extract(v_str_810_, v_startInclusive_811_, v_endExclusive_812_);
lean_dec(v_endExclusive_812_);
lean_dec(v_startInclusive_811_);
lean_dec_ref(v_str_810_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trim(lean_object* v_s_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_String_Slice_trimAscii(v_s_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* lean_string_trim(lean_object* v_s_816_){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v_str_821_; lean_object* v_startInclusive_822_; lean_object* v_endExclusive_823_; lean_object* v___x_824_; 
v___x_817_ = lean_unsigned_to_nat(0u);
v___x_818_ = lean_string_utf8_byte_size(v_s_816_);
v___x_819_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_819_, 0, v_s_816_);
lean_ctor_set(v___x_819_, 1, v___x_817_);
lean_ctor_set(v___x_819_, 2, v___x_818_);
v___x_820_ = l_String_Slice_trimAscii(v___x_819_);
v_str_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc_ref(v_str_821_);
v_startInclusive_822_ = lean_ctor_get(v___x_820_, 1);
lean_inc(v_startInclusive_822_);
v_endExclusive_823_ = lean_ctor_get(v___x_820_, 2);
lean_inc(v_endExclusive_823_);
lean_dec_ref(v___x_820_);
v___x_824_ = lean_string_utf8_extract(v_str_821_, v_startInclusive_822_, v_endExclusive_823_);
lean_dec(v_endExclusive_823_);
lean_dec(v_startInclusive_822_);
lean_dec_ref(v_str_821_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextWhile(lean_object* v_s_825_, lean_object* v_p_826_, lean_object* v_i_827_){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = lean_string_utf8_byte_size(v_s_825_);
v___x_829_ = l_Substring_Raw_takeWhileAux(v_s_825_, v___x_828_, v_p_826_, v_i_827_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextWhile___boxed(lean_object* v_s_830_, lean_object* v_p_831_, lean_object* v_i_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_String_Pos_Raw_nextWhile(v_s_830_, v_p_831_, v_i_832_);
lean_dec_ref(v_s_830_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_String_nextWhile(lean_object* v_s_834_, lean_object* v_p_835_, lean_object* v_i_836_){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = lean_string_utf8_byte_size(v_s_834_);
v___x_838_ = l_Substring_Raw_takeWhileAux(v_s_834_, v___x_837_, v_p_835_, v_i_836_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_String_nextWhile___boxed(lean_object* v_s_839_, lean_object* v_p_840_, lean_object* v_i_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_String_nextWhile(v_s_839_, v_p_840_, v_i_841_);
lean_dec_ref(v_s_839_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0(lean_object* v_p_843_, lean_object* v_s_844_, lean_object* v_stopPos_845_, lean_object* v_i_846_){
_start:
{
uint8_t v___x_847_; 
v___x_847_ = l_String_instDecidableLtRaw___aux__1(v_i_846_, v_stopPos_845_);
if (v___x_847_ == 0)
{
lean_dec_ref(v_p_843_);
return v_i_846_;
}
else
{
uint32_t v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; uint8_t v___x_851_; 
v___x_848_ = lean_string_utf8_get(v_s_844_, v_i_846_);
v___x_849_ = lean_box_uint32(v___x_848_);
lean_inc_ref(v_p_843_);
v___x_850_ = lean_apply_1(v_p_843_, v___x_849_);
v___x_851_ = lean_unbox(v___x_850_);
if (v___x_851_ == 0)
{
lean_dec_ref(v_p_843_);
return v_i_846_;
}
else
{
lean_object* v___x_852_; 
v___x_852_ = lean_string_utf8_next(v_s_844_, v_i_846_);
lean_dec(v_i_846_);
v_i_846_ = v___x_852_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0___boxed(lean_object* v_p_854_, lean_object* v_s_855_, lean_object* v_stopPos_856_, lean_object* v_i_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0(v_p_854_, v_s_855_, v_stopPos_856_, v_i_857_);
lean_dec(v_stopPos_856_);
lean_dec_ref(v_s_855_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* lean_string_nextwhile(lean_object* v_s_859_, lean_object* v_p_860_, lean_object* v_i_861_){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_string_utf8_byte_size(v_s_859_);
v___x_863_ = l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0(v_p_860_, v_s_859_, v___x_862_, v_i_861_);
lean_dec_ref(v_s_859_);
return v___x_863_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_Raw_nextUntil___lam__0(lean_object* v_p_864_, uint32_t v_c_865_){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; uint8_t v___x_868_; 
v___x_866_ = lean_box_uint32(v_c_865_);
v___x_867_ = lean_apply_1(v_p_864_, v___x_866_);
v___x_868_ = lean_unbox(v___x_867_);
if (v___x_868_ == 0)
{
uint8_t v___x_869_; 
v___x_869_ = 1;
return v___x_869_;
}
else
{
uint8_t v___x_870_; 
v___x_870_ = 0;
return v___x_870_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextUntil___lam__0___boxed(lean_object* v_p_871_, lean_object* v_c_872_){
_start:
{
uint32_t v_c_boxed_873_; uint8_t v_res_874_; lean_object* v_r_875_; 
v_c_boxed_873_ = lean_unbox_uint32(v_c_872_);
lean_dec(v_c_872_);
v_res_874_ = l_String_Pos_Raw_nextUntil___lam__0(v_p_871_, v_c_boxed_873_);
v_r_875_ = lean_box(v_res_874_);
return v_r_875_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextUntil(lean_object* v_s_876_, lean_object* v_p_877_, lean_object* v_i_878_){
_start:
{
lean_object* v___f_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___f_879_ = lean_alloc_closure((void*)(l_String_Pos_Raw_nextUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_879_, 0, v_p_877_);
v___x_880_ = lean_string_utf8_byte_size(v_s_876_);
v___x_881_ = l_Substring_Raw_takeWhileAux(v_s_876_, v___x_880_, v___f_879_, v_i_878_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextUntil___boxed(lean_object* v_s_882_, lean_object* v_p_883_, lean_object* v_i_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_String_Pos_Raw_nextUntil(v_s_882_, v_p_883_, v_i_884_);
lean_dec_ref(v_s_882_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0(lean_object* v_p_886_, lean_object* v_s_887_, lean_object* v_stopPos_888_, lean_object* v_i_889_){
_start:
{
uint8_t v___x_890_; 
v___x_890_ = l_String_instDecidableLtRaw___aux__1(v_i_889_, v_stopPos_888_);
if (v___x_890_ == 0)
{
lean_dec_ref(v_p_886_);
return v_i_889_;
}
else
{
uint32_t v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; uint8_t v___x_894_; 
v___x_891_ = lean_string_utf8_get(v_s_887_, v_i_889_);
v___x_892_ = lean_box_uint32(v___x_891_);
lean_inc_ref(v_p_886_);
v___x_893_ = lean_apply_1(v_p_886_, v___x_892_);
v___x_894_ = lean_unbox(v___x_893_);
if (v___x_894_ == 0)
{
lean_object* v___x_895_; 
v___x_895_ = lean_string_utf8_next(v_s_887_, v_i_889_);
lean_dec(v_i_889_);
v_i_889_ = v___x_895_;
goto _start;
}
else
{
lean_dec_ref(v_p_886_);
return v_i_889_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0___boxed(lean_object* v_p_897_, lean_object* v_s_898_, lean_object* v_stopPos_899_, lean_object* v_i_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0(v_p_897_, v_s_898_, v_stopPos_899_, v_i_900_);
lean_dec(v_stopPos_899_);
lean_dec_ref(v_s_898_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_String_nextUntil(lean_object* v_s_902_, lean_object* v_p_903_, lean_object* v_i_904_){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = lean_string_utf8_byte_size(v_s_902_);
v___x_906_ = l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0(v_p_903_, v_s_902_, v___x_905_, v_i_904_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_String_nextUntil___boxed(lean_object* v_s_907_, lean_object* v_p_908_, lean_object* v_i_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_String_nextUntil(v_s_907_, v_p_908_, v_i_909_);
lean_dec_ref(v_s_907_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___redArg(lean_object* v_s_911_, lean_object* v_inst_912_){
_start:
{
lean_object* v_skipPrefix_x3f_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_933_; 
v_skipPrefix_x3f_913_ = lean_ctor_get(v_inst_912_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v_inst_912_);
if (v_isSharedCheck_933_ == 0)
{
lean_object* v_unused_934_; lean_object* v_unused_935_; 
v_unused_934_ = lean_ctor_get(v_inst_912_, 2);
lean_dec(v_unused_934_);
v_unused_935_ = lean_ctor_get(v_inst_912_, 1);
lean_dec(v_unused_935_);
v___x_915_ = v_inst_912_;
v_isShared_916_ = v_isSharedCheck_933_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_skipPrefix_x3f_913_);
lean_dec(v_inst_912_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_933_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_920_; 
v___x_917_ = lean_string_utf8_byte_size(v_s_911_);
v___x_918_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_s_911_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 2, v___x_917_);
lean_ctor_set(v___x_915_, 1, v___x_918_);
lean_ctor_set(v___x_915_, 0, v_s_911_);
v___x_920_ = v___x_915_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_s_911_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v___x_918_);
lean_ctor_set(v_reuseFailAlloc_932_, 2, v___x_917_);
v___x_920_ = v_reuseFailAlloc_932_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
lean_object* v___x_921_; 
v___x_921_ = lean_apply_1(v_skipPrefix_x3f_913_, v___x_920_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v___x_922_; 
lean_dec_ref(v_s_911_);
v___x_922_ = lean_box(0);
return v___x_922_;
}
else
{
lean_object* v_val_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_931_; 
v_val_923_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_931_ == 0)
{
v___x_925_ = v___x_921_;
v_isShared_926_ = v_isSharedCheck_931_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_val_923_);
lean_dec(v___x_921_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_931_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_927_; lean_object* v___x_929_; 
v___x_927_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_927_, 0, v_s_911_);
lean_ctor_set(v___x_927_, 1, v_val_923_);
lean_ctor_set(v___x_927_, 2, v___x_917_);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 0, v___x_927_);
v___x_929_ = v___x_925_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_927_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f(lean_object* v_00_u03c1_936_, lean_object* v_s_937_, lean_object* v_pat_938_, lean_object* v_inst_939_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l_String_dropPrefix_x3f___redArg(v_s_937_, v_inst_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___boxed(lean_object* v_00_u03c1_941_, lean_object* v_s_942_, lean_object* v_pat_943_, lean_object* v_inst_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_String_dropPrefix_x3f(v_00_u03c1_941_, v_s_942_, v_pat_943_, v_inst_944_);
lean_dec(v_pat_943_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___redArg(lean_object* v_s_946_, lean_object* v_inst_947_){
_start:
{
lean_object* v_skipSuffix_x3f_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_968_; 
v_skipSuffix_x3f_948_ = lean_ctor_get(v_inst_947_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v_inst_947_);
if (v_isSharedCheck_968_ == 0)
{
lean_object* v_unused_969_; lean_object* v_unused_970_; 
v_unused_969_ = lean_ctor_get(v_inst_947_, 2);
lean_dec(v_unused_969_);
v_unused_970_ = lean_ctor_get(v_inst_947_, 1);
lean_dec(v_unused_970_);
v___x_950_ = v_inst_947_;
v_isShared_951_ = v_isSharedCheck_968_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_skipSuffix_x3f_948_);
lean_dec(v_inst_947_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_968_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_955_; 
v___x_952_ = lean_string_utf8_byte_size(v_s_946_);
v___x_953_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_s_946_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 2, v___x_952_);
lean_ctor_set(v___x_950_, 1, v___x_953_);
lean_ctor_set(v___x_950_, 0, v_s_946_);
v___x_955_ = v___x_950_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_s_946_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v___x_953_);
lean_ctor_set(v_reuseFailAlloc_967_, 2, v___x_952_);
v___x_955_ = v_reuseFailAlloc_967_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
lean_object* v___x_956_; 
v___x_956_ = lean_apply_1(v_skipSuffix_x3f_948_, v___x_955_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v___x_957_; 
lean_dec_ref(v_s_946_);
v___x_957_ = lean_box(0);
return v___x_957_;
}
else
{
lean_object* v_val_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_966_; 
v_val_958_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_966_ == 0)
{
v___x_960_ = v___x_956_;
v_isShared_961_ = v_isSharedCheck_966_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_val_958_);
lean_dec(v___x_956_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_966_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_962_; lean_object* v___x_964_; 
v___x_962_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_962_, 0, v_s_946_);
lean_ctor_set(v___x_962_, 1, v___x_953_);
lean_ctor_set(v___x_962_, 2, v_val_958_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 0, v___x_962_);
v___x_964_ = v___x_960_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_962_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f(lean_object* v_00_u03c1_971_, lean_object* v_s_972_, lean_object* v_pat_973_, lean_object* v_inst_974_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_String_dropSuffix_x3f___redArg(v_s_972_, v_inst_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___boxed(lean_object* v_00_u03c1_976_, lean_object* v_s_977_, lean_object* v_pat_978_, lean_object* v_inst_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_String_dropSuffix_x3f(v_00_u03c1_976_, v_s_977_, v_pat_978_, v_inst_979_);
lean_dec(v_pat_978_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix___redArg(lean_object* v_s_981_, lean_object* v_inst_982_){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_983_ = lean_unsigned_to_nat(0u);
v___x_984_ = lean_string_utf8_byte_size(v_s_981_);
v___x_985_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_985_, 0, v_s_981_);
lean_ctor_set(v___x_985_, 1, v___x_983_);
lean_ctor_set(v___x_985_, 2, v___x_984_);
v___x_986_ = l_String_Slice_dropPrefix___redArg(v___x_985_, v_inst_982_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix(lean_object* v_00_u03c1_987_, lean_object* v_s_988_, lean_object* v_pat_989_, lean_object* v_inst_990_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_String_dropPrefix___redArg(v_s_988_, v_inst_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix___boxed(lean_object* v_00_u03c1_992_, lean_object* v_s_993_, lean_object* v_pat_994_, lean_object* v_inst_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_String_dropPrefix(v_00_u03c1_992_, v_s_993_, v_pat_994_, v_inst_995_);
lean_dec(v_pat_994_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg(lean_object* v_pre_997_, lean_object* v_s_998_){
_start:
{
lean_object* v_str_999_; lean_object* v_startInclusive_1000_; lean_object* v_endExclusive_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; uint8_t v___x_1004_; 
v_str_999_ = lean_ctor_get(v_s_998_, 0);
v_startInclusive_1000_ = lean_ctor_get(v_s_998_, 1);
v_endExclusive_1001_ = lean_ctor_get(v_s_998_, 2);
v___x_1002_ = lean_string_utf8_byte_size(v_pre_997_);
v___x_1003_ = lean_nat_sub(v_endExclusive_1001_, v_startInclusive_1000_);
v___x_1004_ = lean_nat_dec_le(v___x_1002_, v___x_1003_);
lean_dec(v___x_1003_);
if (v___x_1004_ == 0)
{
return v_s_998_;
}
else
{
lean_object* v___x_1005_; uint8_t v___x_1006_; 
v___x_1005_ = lean_unsigned_to_nat(0u);
v___x_1006_ = lean_string_memcmp(v_str_999_, v_pre_997_, v_startInclusive_1000_, v___x_1005_, v___x_1002_);
if (v___x_1006_ == 0)
{
return v_s_998_;
}
else
{
lean_object* v___x_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1015_; 
lean_inc(v_endExclusive_1001_);
lean_inc(v_startInclusive_1000_);
lean_inc_ref(v_str_999_);
v___x_1007_ = l_String_Slice_pos_x21(v_s_998_, v___x_1002_);
v_isSharedCheck_1015_ = !lean_is_exclusive(v_s_998_);
if (v_isSharedCheck_1015_ == 0)
{
lean_object* v_unused_1016_; lean_object* v_unused_1017_; lean_object* v_unused_1018_; 
v_unused_1016_ = lean_ctor_get(v_s_998_, 2);
lean_dec(v_unused_1016_);
v_unused_1017_ = lean_ctor_get(v_s_998_, 1);
lean_dec(v_unused_1017_);
v_unused_1018_ = lean_ctor_get(v_s_998_, 0);
lean_dec(v_unused_1018_);
v___x_1009_ = v_s_998_;
v_isShared_1010_ = v_isSharedCheck_1015_;
goto v_resetjp_1008_;
}
else
{
lean_dec(v_s_998_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1015_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1011_; lean_object* v___x_1013_; 
v___x_1011_ = lean_nat_add(v_startInclusive_1000_, v___x_1007_);
lean_dec(v___x_1007_);
lean_dec(v_startInclusive_1000_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 1, v___x_1011_);
v___x_1013_ = v___x_1009_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_str_999_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v___x_1011_);
lean_ctor_set(v_reuseFailAlloc_1014_, 2, v_endExclusive_1001_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg___boxed(lean_object* v_pre_1019_, lean_object* v_s_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg(v_pre_1019_, v_s_1020_);
lean_dec_ref(v_pre_1019_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix___at___00String_stripPrefix_spec__0(lean_object* v_pre_1022_, lean_object* v_s_1023_, lean_object* v_pat_1024_){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1025_ = lean_unsigned_to_nat(0u);
v___x_1026_ = lean_string_utf8_byte_size(v_s_1023_);
v___x_1027_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1027_, 0, v_s_1023_);
lean_ctor_set(v___x_1027_, 1, v___x_1025_);
lean_ctor_set(v___x_1027_, 2, v___x_1026_);
v___x_1028_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg(v_pre_1022_, v___x_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix___at___00String_stripPrefix_spec__0___boxed(lean_object* v_pre_1029_, lean_object* v_s_1030_, lean_object* v_pat_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_String_dropPrefix___at___00String_stripPrefix_spec__0(v_pre_1029_, v_s_1030_, v_pat_1031_);
lean_dec_ref(v_pat_1031_);
lean_dec_ref(v_pre_1029_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_String_stripPrefix(lean_object* v_s_1033_, lean_object* v_pre_1034_){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = l_String_dropPrefix___at___00String_stripPrefix_spec__0(v_pre_1034_, v_s_1033_, v_pre_1034_);
v___x_1036_ = l_String_Slice_toString(v___x_1035_);
lean_dec_ref(v___x_1035_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_String_stripPrefix___boxed(lean_object* v_s_1037_, lean_object* v_pre_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l_String_stripPrefix(v_s_1037_, v_pre_1038_);
lean_dec_ref(v_pre_1038_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0(lean_object* v_pat_1040_, lean_object* v_pre_1041_, lean_object* v_s_1042_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg(v_pre_1041_, v_s_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___boxed(lean_object* v_pat_1044_, lean_object* v_pre_1045_, lean_object* v_s_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0(v_pat_1044_, v_pre_1045_, v_s_1046_);
lean_dec_ref(v_pre_1045_);
lean_dec_ref(v_pat_1044_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_Slice_stripPrefix_spec__0(lean_object* v_pre_1048_, lean_object* v_s_1049_){
_start:
{
lean_object* v_str_1050_; lean_object* v_startInclusive_1051_; lean_object* v_endExclusive_1052_; lean_object* v_str_1053_; lean_object* v_startInclusive_1054_; lean_object* v_endExclusive_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; 
v_str_1050_ = lean_ctor_get(v_pre_1048_, 0);
v_startInclusive_1051_ = lean_ctor_get(v_pre_1048_, 1);
v_endExclusive_1052_ = lean_ctor_get(v_pre_1048_, 2);
v_str_1053_ = lean_ctor_get(v_s_1049_, 0);
v_startInclusive_1054_ = lean_ctor_get(v_s_1049_, 1);
v_endExclusive_1055_ = lean_ctor_get(v_s_1049_, 2);
v___x_1056_ = lean_nat_sub(v_endExclusive_1052_, v_startInclusive_1051_);
v___x_1057_ = lean_nat_sub(v_endExclusive_1055_, v_startInclusive_1054_);
v___x_1058_ = lean_nat_dec_le(v___x_1056_, v___x_1057_);
lean_dec(v___x_1057_);
if (v___x_1058_ == 0)
{
lean_dec(v___x_1056_);
return v_s_1049_;
}
else
{
uint8_t v___x_1059_; 
v___x_1059_ = lean_string_memcmp(v_str_1053_, v_str_1050_, v_startInclusive_1054_, v_startInclusive_1051_, v___x_1056_);
if (v___x_1059_ == 0)
{
lean_dec(v___x_1056_);
return v_s_1049_;
}
else
{
lean_object* v___x_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1068_; 
lean_inc(v_endExclusive_1055_);
lean_inc(v_startInclusive_1054_);
lean_inc_ref(v_str_1053_);
v___x_1060_ = l_String_Slice_pos_x21(v_s_1049_, v___x_1056_);
lean_dec(v___x_1056_);
v_isSharedCheck_1068_ = !lean_is_exclusive(v_s_1049_);
if (v_isSharedCheck_1068_ == 0)
{
lean_object* v_unused_1069_; lean_object* v_unused_1070_; lean_object* v_unused_1071_; 
v_unused_1069_ = lean_ctor_get(v_s_1049_, 2);
lean_dec(v_unused_1069_);
v_unused_1070_ = lean_ctor_get(v_s_1049_, 1);
lean_dec(v_unused_1070_);
v_unused_1071_ = lean_ctor_get(v_s_1049_, 0);
lean_dec(v_unused_1071_);
v___x_1062_ = v_s_1049_;
v_isShared_1063_ = v_isSharedCheck_1068_;
goto v_resetjp_1061_;
}
else
{
lean_dec(v_s_1049_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1068_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1064_; lean_object* v___x_1066_; 
v___x_1064_ = lean_nat_add(v_startInclusive_1054_, v___x_1060_);
lean_dec(v___x_1060_);
lean_dec(v_startInclusive_1054_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 1, v___x_1064_);
v___x_1066_ = v___x_1062_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_str_1053_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v___x_1064_);
lean_ctor_set(v_reuseFailAlloc_1067_, 2, v_endExclusive_1055_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_Slice_stripPrefix_spec__0___boxed(lean_object* v_pre_1072_, lean_object* v_s_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_String_Slice_dropPrefix___at___00String_Slice_stripPrefix_spec__0(v_pre_1072_, v_s_1073_);
lean_dec_ref(v_pre_1072_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_stripPrefix(lean_object* v_s_1075_, lean_object* v_pre_1076_){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_String_Slice_dropPrefix___at___00String_Slice_stripPrefix_spec__0(v_pre_1076_, v_s_1075_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_stripPrefix___boxed(lean_object* v_s_1078_, lean_object* v_pre_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_String_Slice_stripPrefix(v_s_1078_, v_pre_1079_);
lean_dec_ref(v_pre_1079_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix___redArg(lean_object* v_s_1081_, lean_object* v_inst_1082_){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1083_ = lean_unsigned_to_nat(0u);
v___x_1084_ = lean_string_utf8_byte_size(v_s_1081_);
v___x_1085_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1085_, 0, v_s_1081_);
lean_ctor_set(v___x_1085_, 1, v___x_1083_);
lean_ctor_set(v___x_1085_, 2, v___x_1084_);
v___x_1086_ = l_String_Slice_dropSuffix___redArg(v___x_1085_, v_inst_1082_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix(lean_object* v_00_u03c1_1087_, lean_object* v_s_1088_, lean_object* v_pat_1089_, lean_object* v_inst_1090_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_String_dropSuffix___redArg(v_s_1088_, v_inst_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix___boxed(lean_object* v_00_u03c1_1092_, lean_object* v_s_1093_, lean_object* v_pat_1094_, lean_object* v_inst_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_String_dropSuffix(v_00_u03c1_1092_, v_s_1093_, v_pat_1094_, v_inst_1095_);
lean_dec(v_pat_1094_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0___redArg(lean_object* v_suff_1097_, lean_object* v_s_1098_){
_start:
{
lean_object* v_str_1099_; lean_object* v_startInclusive_1100_; lean_object* v_endExclusive_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; uint8_t v___x_1104_; 
v_str_1099_ = lean_ctor_get(v_s_1098_, 0);
v_startInclusive_1100_ = lean_ctor_get(v_s_1098_, 1);
v_endExclusive_1101_ = lean_ctor_get(v_s_1098_, 2);
v___x_1102_ = lean_string_utf8_byte_size(v_suff_1097_);
v___x_1103_ = lean_nat_sub(v_endExclusive_1101_, v_startInclusive_1100_);
v___x_1104_ = lean_nat_dec_le(v___x_1102_, v___x_1103_);
if (v___x_1104_ == 0)
{
lean_dec(v___x_1103_);
return v_s_1098_;
}
else
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; uint8_t v___x_1108_; 
v___x_1105_ = lean_unsigned_to_nat(0u);
v___x_1106_ = lean_nat_sub(v___x_1103_, v___x_1102_);
lean_dec(v___x_1103_);
v___x_1107_ = lean_nat_add(v_startInclusive_1100_, v___x_1106_);
v___x_1108_ = lean_string_memcmp(v_str_1099_, v_suff_1097_, v___x_1107_, v___x_1105_, v___x_1102_);
lean_dec(v___x_1107_);
if (v___x_1108_ == 0)
{
lean_dec(v___x_1106_);
return v_s_1098_;
}
else
{
lean_object* v___x_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1117_; 
lean_inc(v_startInclusive_1100_);
lean_inc_ref(v_str_1099_);
v___x_1109_ = l_String_Slice_pos_x21(v_s_1098_, v___x_1106_);
lean_dec(v___x_1106_);
v_isSharedCheck_1117_ = !lean_is_exclusive(v_s_1098_);
if (v_isSharedCheck_1117_ == 0)
{
lean_object* v_unused_1118_; lean_object* v_unused_1119_; lean_object* v_unused_1120_; 
v_unused_1118_ = lean_ctor_get(v_s_1098_, 2);
lean_dec(v_unused_1118_);
v_unused_1119_ = lean_ctor_get(v_s_1098_, 1);
lean_dec(v_unused_1119_);
v_unused_1120_ = lean_ctor_get(v_s_1098_, 0);
lean_dec(v_unused_1120_);
v___x_1111_ = v_s_1098_;
v_isShared_1112_ = v_isSharedCheck_1117_;
goto v_resetjp_1110_;
}
else
{
lean_dec(v_s_1098_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1117_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; lean_object* v___x_1115_; 
v___x_1113_ = lean_nat_add(v_startInclusive_1100_, v___x_1109_);
lean_dec(v___x_1109_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 2, v___x_1113_);
v___x_1115_ = v___x_1111_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_str_1099_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v_startInclusive_1100_);
lean_ctor_set(v_reuseFailAlloc_1116_, 2, v___x_1113_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0___redArg___boxed(lean_object* v_suff_1121_, lean_object* v_s_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0___redArg(v_suff_1121_, v_s_1122_);
lean_dec_ref(v_suff_1121_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix___at___00String_stripSuffix_spec__0(lean_object* v_suff_1124_, lean_object* v_s_1125_, lean_object* v_pat_1126_){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1127_ = lean_unsigned_to_nat(0u);
v___x_1128_ = lean_string_utf8_byte_size(v_s_1125_);
v___x_1129_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1129_, 0, v_s_1125_);
lean_ctor_set(v___x_1129_, 1, v___x_1127_);
lean_ctor_set(v___x_1129_, 2, v___x_1128_);
v___x_1130_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0___redArg(v_suff_1124_, v___x_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix___at___00String_stripSuffix_spec__0___boxed(lean_object* v_suff_1131_, lean_object* v_s_1132_, lean_object* v_pat_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_String_dropSuffix___at___00String_stripSuffix_spec__0(v_suff_1131_, v_s_1132_, v_pat_1133_);
lean_dec_ref(v_pat_1133_);
lean_dec_ref(v_suff_1131_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_String_stripSuffix(lean_object* v_s_1135_, lean_object* v_suff_1136_){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = l_String_dropSuffix___at___00String_stripSuffix_spec__0(v_suff_1136_, v_s_1135_, v_suff_1136_);
v___x_1138_ = l_String_Slice_toString(v___x_1137_);
lean_dec_ref(v___x_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_String_stripSuffix___boxed(lean_object* v_s_1139_, lean_object* v_suff_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_String_stripSuffix(v_s_1139_, v_suff_1140_);
lean_dec_ref(v_suff_1140_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0(lean_object* v_pat_1142_, lean_object* v_suff_1143_, lean_object* v_s_1144_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0___redArg(v_suff_1143_, v_s_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0___boxed(lean_object* v_pat_1146_, lean_object* v_suff_1147_, lean_object* v_s_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0(v_pat_1146_, v_suff_1147_, v_s_1148_);
lean_dec_ref(v_suff_1147_);
lean_dec_ref(v_pat_1146_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_Slice_stripSuffix_spec__0(lean_object* v_suff_1150_, lean_object* v_s_1151_){
_start:
{
lean_object* v_str_1152_; lean_object* v_startInclusive_1153_; lean_object* v_endExclusive_1154_; lean_object* v_str_1155_; lean_object* v_startInclusive_1156_; lean_object* v_endExclusive_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
v_str_1152_ = lean_ctor_get(v_suff_1150_, 0);
v_startInclusive_1153_ = lean_ctor_get(v_suff_1150_, 1);
v_endExclusive_1154_ = lean_ctor_get(v_suff_1150_, 2);
v_str_1155_ = lean_ctor_get(v_s_1151_, 0);
v_startInclusive_1156_ = lean_ctor_get(v_s_1151_, 1);
v_endExclusive_1157_ = lean_ctor_get(v_s_1151_, 2);
v___x_1158_ = lean_nat_sub(v_endExclusive_1154_, v_startInclusive_1153_);
v___x_1159_ = lean_nat_sub(v_endExclusive_1157_, v_startInclusive_1156_);
v___x_1160_ = lean_nat_dec_le(v___x_1158_, v___x_1159_);
if (v___x_1160_ == 0)
{
lean_dec(v___x_1159_);
lean_dec(v___x_1158_);
return v_s_1151_;
}
else
{
lean_object* v___x_1161_; lean_object* v___x_1162_; uint8_t v___x_1163_; 
v___x_1161_ = lean_nat_sub(v___x_1159_, v___x_1158_);
lean_dec(v___x_1159_);
v___x_1162_ = lean_nat_add(v_startInclusive_1156_, v___x_1161_);
v___x_1163_ = lean_string_memcmp(v_str_1155_, v_str_1152_, v___x_1162_, v_startInclusive_1153_, v___x_1158_);
lean_dec(v___x_1158_);
lean_dec(v___x_1162_);
if (v___x_1163_ == 0)
{
lean_dec(v___x_1161_);
return v_s_1151_;
}
else
{
lean_object* v___x_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1172_; 
lean_inc(v_startInclusive_1156_);
lean_inc_ref(v_str_1155_);
v___x_1164_ = l_String_Slice_pos_x21(v_s_1151_, v___x_1161_);
lean_dec(v___x_1161_);
v_isSharedCheck_1172_ = !lean_is_exclusive(v_s_1151_);
if (v_isSharedCheck_1172_ == 0)
{
lean_object* v_unused_1173_; lean_object* v_unused_1174_; lean_object* v_unused_1175_; 
v_unused_1173_ = lean_ctor_get(v_s_1151_, 2);
lean_dec(v_unused_1173_);
v_unused_1174_ = lean_ctor_get(v_s_1151_, 1);
lean_dec(v_unused_1174_);
v_unused_1175_ = lean_ctor_get(v_s_1151_, 0);
lean_dec(v_unused_1175_);
v___x_1166_ = v_s_1151_;
v_isShared_1167_ = v_isSharedCheck_1172_;
goto v_resetjp_1165_;
}
else
{
lean_dec(v_s_1151_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1172_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1168_; lean_object* v___x_1170_; 
v___x_1168_ = lean_nat_add(v_startInclusive_1156_, v___x_1164_);
lean_dec(v___x_1164_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 2, v___x_1168_);
v___x_1170_ = v___x_1166_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_str_1155_);
lean_ctor_set(v_reuseFailAlloc_1171_, 1, v_startInclusive_1156_);
lean_ctor_set(v_reuseFailAlloc_1171_, 2, v___x_1168_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_Slice_stripSuffix_spec__0___boxed(lean_object* v_suff_1176_, lean_object* v_s_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_String_Slice_dropSuffix___at___00String_Slice_stripSuffix_spec__0(v_suff_1176_, v_s_1177_);
lean_dec_ref(v_suff_1176_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_stripSuffix(lean_object* v_s_1179_, lean_object* v_suff_1180_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l_String_Slice_dropSuffix___at___00String_Slice_stripSuffix_spec__0(v_suff_1180_, v_s_1179_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_stripSuffix___boxed(lean_object* v_s_1182_, lean_object* v_suff_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_String_Slice_stripSuffix(v_s_1182_, v_suff_1183_);
lean_dec_ref(v_suff_1183_);
return v_res_1184_;
}
}
lean_object* runtime_initialize_Init_Data_String_Substring(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_String_Substring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_TakeDrop(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Substring(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Substring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_TakeDrop(builtin);
}
#ifdef __cplusplus
}
#endif

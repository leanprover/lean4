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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_String_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_all(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_revAll___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_revAll___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_revAll(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_revAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_175_ = lean_nat_dec_lt(v___x_169_, v_pos_159_);
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
LEAN_EXPORT uint8_t l_String_all___redArg(lean_object* v_s_328_, lean_object* v_inst_329_){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_330_ = lean_unsigned_to_nat(0u);
v___x_331_ = lean_string_utf8_byte_size(v_s_328_);
v___x_332_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_332_, 0, v_s_328_);
lean_ctor_set(v___x_332_, 1, v___x_330_);
lean_ctor_set(v___x_332_, 2, v___x_331_);
v___x_333_ = l_String_Slice_Pos_skipWhile___redArg(v___x_332_, v___x_330_, v_inst_329_);
lean_dec_ref(v___x_332_);
v___x_334_ = lean_nat_dec_eq(v___x_333_, v___x_331_);
lean_dec(v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_String_all___redArg___boxed(lean_object* v_s_335_, lean_object* v_inst_336_){
_start:
{
uint8_t v_res_337_; lean_object* v_r_338_; 
v_res_337_ = l_String_all___redArg(v_s_335_, v_inst_336_);
v_r_338_ = lean_box(v_res_337_);
return v_r_338_;
}
}
LEAN_EXPORT uint8_t l_String_all(lean_object* v_00_u03c1_339_, lean_object* v_s_340_, lean_object* v_pat_341_, lean_object* v_inst_342_){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_343_ = lean_unsigned_to_nat(0u);
v___x_344_ = lean_string_utf8_byte_size(v_s_340_);
v___x_345_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_345_, 0, v_s_340_);
lean_ctor_set(v___x_345_, 1, v___x_343_);
lean_ctor_set(v___x_345_, 2, v___x_344_);
v___x_346_ = l_String_Slice_Pos_skipWhile___redArg(v___x_345_, v___x_343_, v_inst_342_);
lean_dec_ref(v___x_345_);
v___x_347_ = lean_nat_dec_eq(v___x_346_, v___x_344_);
lean_dec(v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_String_all___boxed(lean_object* v_00_u03c1_348_, lean_object* v_s_349_, lean_object* v_pat_350_, lean_object* v_inst_351_){
_start:
{
uint8_t v_res_352_; lean_object* v_r_353_; 
v_res_352_ = l_String_all(v_00_u03c1_348_, v_s_349_, v_pat_350_, v_inst_351_);
lean_dec(v_pat_350_);
v_r_353_ = lean_box(v_res_352_);
return v_r_353_;
}
}
LEAN_EXPORT uint8_t l_String_revAll___redArg(lean_object* v_s_354_, lean_object* v_inst_355_){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_356_ = lean_unsigned_to_nat(0u);
v___x_357_ = lean_string_utf8_byte_size(v_s_354_);
v___x_358_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_358_, 0, v_s_354_);
lean_ctor_set(v___x_358_, 1, v___x_356_);
lean_ctor_set(v___x_358_, 2, v___x_357_);
v___x_359_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_358_, v___x_357_, v_inst_355_);
lean_dec_ref(v___x_358_);
v___x_360_ = lean_nat_dec_eq(v___x_359_, v___x_356_);
lean_dec(v___x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_String_revAll___redArg___boxed(lean_object* v_s_361_, lean_object* v_inst_362_){
_start:
{
uint8_t v_res_363_; lean_object* v_r_364_; 
v_res_363_ = l_String_revAll___redArg(v_s_361_, v_inst_362_);
v_r_364_ = lean_box(v_res_363_);
return v_r_364_;
}
}
LEAN_EXPORT uint8_t l_String_revAll(lean_object* v_00_u03c1_365_, lean_object* v_s_366_, lean_object* v_pat_367_, lean_object* v_inst_368_){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_369_ = lean_unsigned_to_nat(0u);
v___x_370_ = lean_string_utf8_byte_size(v_s_366_);
v___x_371_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_371_, 0, v_s_366_);
lean_ctor_set(v___x_371_, 1, v___x_369_);
lean_ctor_set(v___x_371_, 2, v___x_370_);
v___x_372_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_371_, v___x_370_, v_inst_368_);
lean_dec_ref(v___x_371_);
v___x_373_ = lean_nat_dec_eq(v___x_372_, v___x_369_);
lean_dec(v___x_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_String_revAll___boxed(lean_object* v_00_u03c1_374_, lean_object* v_s_375_, lean_object* v_pat_376_, lean_object* v_inst_377_){
_start:
{
uint8_t v_res_378_; lean_object* v_r_379_; 
v_res_378_ = l_String_revAll(v_00_u03c1_374_, v_s_375_, v_pat_376_, v_inst_377_);
lean_dec(v_pat_376_);
v_r_379_ = lean_box(v_res_378_);
return v_r_379_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_skip_x3f___redArg(lean_object* v_s_380_, lean_object* v_pos_381_, lean_object* v_inst_382_){
_start:
{
lean_object* v_skipPrefix_x3f_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_402_; 
v_skipPrefix_x3f_383_ = lean_ctor_get(v_inst_382_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v_inst_382_);
if (v_isSharedCheck_402_ == 0)
{
lean_object* v_unused_403_; lean_object* v_unused_404_; 
v_unused_403_ = lean_ctor_get(v_inst_382_, 2);
lean_dec(v_unused_403_);
v_unused_404_ = lean_ctor_get(v_inst_382_, 1);
lean_dec(v_unused_404_);
v___x_385_ = v_inst_382_;
v_isShared_386_ = v_isSharedCheck_402_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_skipPrefix_x3f_383_);
lean_dec(v_inst_382_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_402_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_387_; lean_object* v___x_389_; 
v___x_387_ = lean_string_utf8_byte_size(v_s_380_);
lean_inc(v_pos_381_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 2, v___x_387_);
lean_ctor_set(v___x_385_, 1, v_pos_381_);
lean_ctor_set(v___x_385_, 0, v_s_380_);
v___x_389_ = v___x_385_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_s_380_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v_pos_381_);
lean_ctor_set(v_reuseFailAlloc_401_, 2, v___x_387_);
v___x_389_ = v_reuseFailAlloc_401_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
lean_object* v___x_390_; 
v___x_390_ = lean_apply_1(v_skipPrefix_x3f_383_, v___x_389_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v___x_391_; 
lean_dec(v_pos_381_);
v___x_391_ = lean_box(0);
return v___x_391_;
}
else
{
lean_object* v_val_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_400_; 
v_val_392_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_400_ == 0)
{
v___x_394_ = v___x_390_;
v_isShared_395_ = v_isSharedCheck_400_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_val_392_);
lean_dec(v___x_390_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_400_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_396_ = lean_nat_add(v_pos_381_, v_val_392_);
lean_dec(v_val_392_);
lean_dec(v_pos_381_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v___x_396_);
v___x_398_ = v___x_394_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_396_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_skip_x3f(lean_object* v_00_u03c1_405_, lean_object* v_s_406_, lean_object* v_pos_407_, lean_object* v_pat_408_, lean_object* v_inst_409_){
_start:
{
lean_object* v_skipPrefix_x3f_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_429_; 
v_skipPrefix_x3f_410_ = lean_ctor_get(v_inst_409_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v_inst_409_);
if (v_isSharedCheck_429_ == 0)
{
lean_object* v_unused_430_; lean_object* v_unused_431_; 
v_unused_430_ = lean_ctor_get(v_inst_409_, 2);
lean_dec(v_unused_430_);
v_unused_431_ = lean_ctor_get(v_inst_409_, 1);
lean_dec(v_unused_431_);
v___x_412_ = v_inst_409_;
v_isShared_413_ = v_isSharedCheck_429_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_skipPrefix_x3f_410_);
lean_dec(v_inst_409_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_429_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_414_ = lean_string_utf8_byte_size(v_s_406_);
lean_inc(v_pos_407_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 2, v___x_414_);
lean_ctor_set(v___x_412_, 1, v_pos_407_);
lean_ctor_set(v___x_412_, 0, v_s_406_);
v___x_416_ = v___x_412_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_s_406_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_pos_407_);
lean_ctor_set(v_reuseFailAlloc_428_, 2, v___x_414_);
v___x_416_ = v_reuseFailAlloc_428_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_417_; 
v___x_417_ = lean_apply_1(v_skipPrefix_x3f_410_, v___x_416_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v___x_418_; 
lean_dec(v_pos_407_);
v___x_418_ = lean_box(0);
return v___x_418_;
}
else
{
lean_object* v_val_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_427_; 
v_val_419_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_427_ == 0)
{
v___x_421_ = v___x_417_;
v_isShared_422_ = v_isSharedCheck_427_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_val_419_);
lean_dec(v___x_417_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_427_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_423_; lean_object* v___x_425_; 
v___x_423_ = lean_nat_add(v_pos_407_, v_val_419_);
lean_dec(v_val_419_);
lean_dec(v_pos_407_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v___x_423_);
v___x_425_ = v___x_421_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_423_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_skip_x3f___boxed(lean_object* v_00_u03c1_432_, lean_object* v_s_433_, lean_object* v_pos_434_, lean_object* v_pat_435_, lean_object* v_inst_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_String_Pos_skip_x3f(v_00_u03c1_432_, v_s_433_, v_pos_434_, v_pat_435_, v_inst_436_);
lean_dec(v_pat_435_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_skipWhile___redArg(lean_object* v_s_438_, lean_object* v_pos_439_, lean_object* v_inst_440_){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_441_ = lean_unsigned_to_nat(0u);
v___x_442_ = lean_string_utf8_byte_size(v_s_438_);
v___x_443_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_443_, 0, v_s_438_);
lean_ctor_set(v___x_443_, 1, v___x_441_);
lean_ctor_set(v___x_443_, 2, v___x_442_);
v___x_444_ = l_String_Slice_Pos_skipWhile___redArg(v___x_443_, v_pos_439_, v_inst_440_);
lean_dec_ref(v___x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_skipWhile(lean_object* v_00_u03c1_445_, lean_object* v_s_446_, lean_object* v_pos_447_, lean_object* v_pat_448_, lean_object* v_inst_449_){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_450_ = lean_unsigned_to_nat(0u);
v___x_451_ = lean_string_utf8_byte_size(v_s_446_);
v___x_452_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_452_, 0, v_s_446_);
lean_ctor_set(v___x_452_, 1, v___x_450_);
lean_ctor_set(v___x_452_, 2, v___x_451_);
v___x_453_ = l_String_Slice_Pos_skipWhile___redArg(v___x_452_, v_pos_447_, v_inst_449_);
lean_dec_ref(v___x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_skipWhile___boxed(lean_object* v_00_u03c1_454_, lean_object* v_s_455_, lean_object* v_pos_456_, lean_object* v_pat_457_, lean_object* v_inst_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_String_Pos_skipWhile(v_00_u03c1_454_, v_s_455_, v_pos_456_, v_pat_457_, v_inst_458_);
lean_dec(v_pat_457_);
return v_res_459_;
}
}
LEAN_EXPORT uint8_t l_String_startsWith___redArg(lean_object* v_s_460_, lean_object* v_inst_461_){
_start:
{
lean_object* v_startsWith_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_473_; 
v_startsWith_462_ = lean_ctor_get(v_inst_461_, 2);
v_isSharedCheck_473_ = !lean_is_exclusive(v_inst_461_);
if (v_isSharedCheck_473_ == 0)
{
lean_object* v_unused_474_; lean_object* v_unused_475_; 
v_unused_474_ = lean_ctor_get(v_inst_461_, 1);
lean_dec(v_unused_474_);
v_unused_475_ = lean_ctor_get(v_inst_461_, 0);
lean_dec(v_unused_475_);
v___x_464_ = v_inst_461_;
v_isShared_465_ = v_isSharedCheck_473_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_startsWith_462_);
lean_dec(v_inst_461_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_473_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_466_ = lean_string_utf8_byte_size(v_s_460_);
v___x_467_ = lean_unsigned_to_nat(0u);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 2, v___x_466_);
lean_ctor_set(v___x_464_, 1, v___x_467_);
lean_ctor_set(v___x_464_, 0, v_s_460_);
v___x_469_ = v___x_464_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_s_460_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_472_, 2, v___x_466_);
v___x_469_ = v_reuseFailAlloc_472_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_470_ = lean_apply_1(v_startsWith_462_, v___x_469_);
v___x_471_ = lean_unbox(v___x_470_);
return v___x_471_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_startsWith___redArg___boxed(lean_object* v_s_476_, lean_object* v_inst_477_){
_start:
{
uint8_t v_res_478_; lean_object* v_r_479_; 
v_res_478_ = l_String_startsWith___redArg(v_s_476_, v_inst_477_);
v_r_479_ = lean_box(v_res_478_);
return v_r_479_;
}
}
LEAN_EXPORT uint8_t l_String_startsWith(lean_object* v_00_u03c1_480_, lean_object* v_s_481_, lean_object* v_pat_482_, lean_object* v_inst_483_){
_start:
{
lean_object* v_startsWith_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_495_; 
v_startsWith_484_ = lean_ctor_get(v_inst_483_, 2);
v_isSharedCheck_495_ = !lean_is_exclusive(v_inst_483_);
if (v_isSharedCheck_495_ == 0)
{
lean_object* v_unused_496_; lean_object* v_unused_497_; 
v_unused_496_ = lean_ctor_get(v_inst_483_, 1);
lean_dec(v_unused_496_);
v_unused_497_ = lean_ctor_get(v_inst_483_, 0);
lean_dec(v_unused_497_);
v___x_486_ = v_inst_483_;
v_isShared_487_ = v_isSharedCheck_495_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_startsWith_484_);
lean_dec(v_inst_483_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_495_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_488_ = lean_string_utf8_byte_size(v_s_481_);
v___x_489_ = lean_unsigned_to_nat(0u);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 2, v___x_488_);
lean_ctor_set(v___x_486_, 1, v___x_489_);
lean_ctor_set(v___x_486_, 0, v_s_481_);
v___x_491_ = v___x_486_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_s_481_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v___x_489_);
lean_ctor_set(v_reuseFailAlloc_494_, 2, v___x_488_);
v___x_491_ = v_reuseFailAlloc_494_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_492_ = lean_apply_1(v_startsWith_484_, v___x_491_);
v___x_493_ = lean_unbox(v___x_492_);
return v___x_493_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_startsWith___boxed(lean_object* v_00_u03c1_498_, lean_object* v_s_499_, lean_object* v_pat_500_, lean_object* v_inst_501_){
_start:
{
uint8_t v_res_502_; lean_object* v_r_503_; 
v_res_502_ = l_String_startsWith(v_00_u03c1_498_, v_s_499_, v_pat_500_, v_inst_501_);
lean_dec(v_pat_500_);
v_r_503_ = lean_box(v_res_502_);
return v_r_503_;
}
}
LEAN_EXPORT uint8_t l_String_isPrefixOf(lean_object* v_p_504_, lean_object* v_s_505_){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_506_ = lean_string_utf8_byte_size(v_s_505_);
v___x_507_ = lean_string_utf8_byte_size(v_p_504_);
v___x_508_ = lean_nat_dec_le(v___x_507_, v___x_506_);
if (v___x_508_ == 0)
{
return v___x_508_;
}
else
{
lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_509_ = lean_unsigned_to_nat(0u);
v___x_510_ = lean_string_memcmp(v_s_505_, v_p_504_, v___x_509_, v___x_509_, v___x_507_);
return v___x_510_;
}
}
}
LEAN_EXPORT lean_object* l_String_isPrefixOf___boxed(lean_object* v_p_511_, lean_object* v_s_512_){
_start:
{
uint8_t v_res_513_; lean_object* v_r_514_; 
v_res_513_ = l_String_isPrefixOf(v_p_511_, v_s_512_);
lean_dec_ref(v_s_512_);
lean_dec_ref(v_p_511_);
v_r_514_ = lean_box(v_res_513_);
return v_r_514_;
}
}
LEAN_EXPORT uint8_t lean_string_isprefixof(lean_object* v_p_515_, lean_object* v_s_516_){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_517_ = lean_string_utf8_byte_size(v_s_516_);
v___x_518_ = lean_string_utf8_byte_size(v_p_515_);
v___x_519_ = lean_nat_dec_le(v___x_518_, v___x_517_);
if (v___x_519_ == 0)
{
lean_dec_ref(v_s_516_);
lean_dec_ref(v_p_515_);
return v___x_519_;
}
else
{
lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_520_ = lean_unsigned_to_nat(0u);
v___x_521_ = lean_string_memcmp(v_s_516_, v_p_515_, v___x_520_, v___x_520_, v___x_518_);
lean_dec_ref(v_p_515_);
lean_dec_ref(v_s_516_);
return v___x_521_;
}
}
}
LEAN_EXPORT lean_object* l_String_Internal_isPrefixOfImpl___boxed(lean_object* v_p_522_, lean_object* v_s_523_){
_start:
{
uint8_t v_res_524_; lean_object* v_r_525_; 
v_res_524_ = lean_string_isprefixof(v_p_522_, v_s_523_);
v_r_525_ = lean_box(v_res_524_);
return v_r_525_;
}
}
LEAN_EXPORT uint8_t l_String_endsWith___redArg(lean_object* v_s_526_, lean_object* v_inst_527_){
_start:
{
lean_object* v_endsWith_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_539_; 
v_endsWith_528_ = lean_ctor_get(v_inst_527_, 2);
v_isSharedCheck_539_ = !lean_is_exclusive(v_inst_527_);
if (v_isSharedCheck_539_ == 0)
{
lean_object* v_unused_540_; lean_object* v_unused_541_; 
v_unused_540_ = lean_ctor_get(v_inst_527_, 1);
lean_dec(v_unused_540_);
v_unused_541_ = lean_ctor_get(v_inst_527_, 0);
lean_dec(v_unused_541_);
v___x_530_ = v_inst_527_;
v_isShared_531_ = v_isSharedCheck_539_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_endsWith_528_);
lean_dec(v_inst_527_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_539_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_532_ = lean_string_utf8_byte_size(v_s_526_);
v___x_533_ = lean_unsigned_to_nat(0u);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 2, v___x_532_);
lean_ctor_set(v___x_530_, 1, v___x_533_);
lean_ctor_set(v___x_530_, 0, v_s_526_);
v___x_535_ = v___x_530_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_s_526_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v___x_533_);
lean_ctor_set(v_reuseFailAlloc_538_, 2, v___x_532_);
v___x_535_ = v_reuseFailAlloc_538_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_object* v___x_536_; uint8_t v___x_537_; 
v___x_536_ = lean_apply_1(v_endsWith_528_, v___x_535_);
v___x_537_ = lean_unbox(v___x_536_);
return v___x_537_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_endsWith___redArg___boxed(lean_object* v_s_542_, lean_object* v_inst_543_){
_start:
{
uint8_t v_res_544_; lean_object* v_r_545_; 
v_res_544_ = l_String_endsWith___redArg(v_s_542_, v_inst_543_);
v_r_545_ = lean_box(v_res_544_);
return v_r_545_;
}
}
LEAN_EXPORT uint8_t l_String_endsWith(lean_object* v_00_u03c1_546_, lean_object* v_s_547_, lean_object* v_pat_548_, lean_object* v_inst_549_){
_start:
{
lean_object* v_endsWith_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_561_; 
v_endsWith_550_ = lean_ctor_get(v_inst_549_, 2);
v_isSharedCheck_561_ = !lean_is_exclusive(v_inst_549_);
if (v_isSharedCheck_561_ == 0)
{
lean_object* v_unused_562_; lean_object* v_unused_563_; 
v_unused_562_ = lean_ctor_get(v_inst_549_, 1);
lean_dec(v_unused_562_);
v_unused_563_ = lean_ctor_get(v_inst_549_, 0);
lean_dec(v_unused_563_);
v___x_552_ = v_inst_549_;
v_isShared_553_ = v_isSharedCheck_561_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_endsWith_550_);
lean_dec(v_inst_549_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_561_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_554_ = lean_string_utf8_byte_size(v_s_547_);
v___x_555_ = lean_unsigned_to_nat(0u);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 2, v___x_554_);
lean_ctor_set(v___x_552_, 1, v___x_555_);
lean_ctor_set(v___x_552_, 0, v_s_547_);
v___x_557_ = v___x_552_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_s_547_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v___x_555_);
lean_ctor_set(v_reuseFailAlloc_560_, 2, v___x_554_);
v___x_557_ = v_reuseFailAlloc_560_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_558_ = lean_apply_1(v_endsWith_550_, v___x_557_);
v___x_559_ = lean_unbox(v___x_558_);
return v___x_559_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_endsWith___boxed(lean_object* v_00_u03c1_564_, lean_object* v_s_565_, lean_object* v_pat_566_, lean_object* v_inst_567_){
_start:
{
uint8_t v_res_568_; lean_object* v_r_569_; 
v_res_568_ = l_String_endsWith(v_00_u03c1_564_, v_s_565_, v_pat_566_, v_inst_567_);
lean_dec(v_pat_566_);
v_r_569_ = lean_box(v_res_568_);
return v_r_569_;
}
}
LEAN_EXPORT lean_object* l_String_skipSuffix_x3f___redArg(lean_object* v_s_570_, lean_object* v_inst_571_){
_start:
{
lean_object* v_skipSuffix_x3f_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_591_; 
v_skipSuffix_x3f_572_ = lean_ctor_get(v_inst_571_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v_inst_571_);
if (v_isSharedCheck_591_ == 0)
{
lean_object* v_unused_592_; lean_object* v_unused_593_; 
v_unused_592_ = lean_ctor_get(v_inst_571_, 2);
lean_dec(v_unused_592_);
v_unused_593_ = lean_ctor_get(v_inst_571_, 1);
lean_dec(v_unused_593_);
v___x_574_ = v_inst_571_;
v_isShared_575_ = v_isSharedCheck_591_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_skipSuffix_x3f_572_);
lean_dec(v_inst_571_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_591_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_579_; 
v___x_576_ = lean_string_utf8_byte_size(v_s_570_);
v___x_577_ = lean_unsigned_to_nat(0u);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 2, v___x_576_);
lean_ctor_set(v___x_574_, 1, v___x_577_);
lean_ctor_set(v___x_574_, 0, v_s_570_);
v___x_579_ = v___x_574_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_s_570_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v___x_577_);
lean_ctor_set(v_reuseFailAlloc_590_, 2, v___x_576_);
v___x_579_ = v_reuseFailAlloc_590_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_580_; 
v___x_580_ = lean_apply_1(v_skipSuffix_x3f_572_, v___x_579_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v___x_581_; 
v___x_581_ = lean_box(0);
return v___x_581_;
}
else
{
lean_object* v_val_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
v_val_582_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_580_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_val_582_);
lean_dec(v___x_580_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_val_582_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_skipSuffix_x3f(lean_object* v_00_u03c1_594_, lean_object* v_s_595_, lean_object* v_pat_596_, lean_object* v_inst_597_){
_start:
{
lean_object* v_skipSuffix_x3f_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_617_; 
v_skipSuffix_x3f_598_ = lean_ctor_get(v_inst_597_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v_inst_597_);
if (v_isSharedCheck_617_ == 0)
{
lean_object* v_unused_618_; lean_object* v_unused_619_; 
v_unused_618_ = lean_ctor_get(v_inst_597_, 2);
lean_dec(v_unused_618_);
v_unused_619_ = lean_ctor_get(v_inst_597_, 1);
lean_dec(v_unused_619_);
v___x_600_ = v_inst_597_;
v_isShared_601_ = v_isSharedCheck_617_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_skipSuffix_x3f_598_);
lean_dec(v_inst_597_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_617_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_605_; 
v___x_602_ = lean_string_utf8_byte_size(v_s_595_);
v___x_603_ = lean_unsigned_to_nat(0u);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 2, v___x_602_);
lean_ctor_set(v___x_600_, 1, v___x_603_);
lean_ctor_set(v___x_600_, 0, v_s_595_);
v___x_605_ = v___x_600_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_s_595_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_616_, 2, v___x_602_);
v___x_605_ = v_reuseFailAlloc_616_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_606_; 
v___x_606_ = lean_apply_1(v_skipSuffix_x3f_598_, v___x_605_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v___x_607_; 
v___x_607_ = lean_box(0);
return v___x_607_;
}
else
{
lean_object* v_val_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
v_val_608_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_606_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_val_608_);
lean_dec(v___x_606_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_val_608_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_skipSuffix_x3f___boxed(lean_object* v_00_u03c1_620_, lean_object* v_s_621_, lean_object* v_pat_622_, lean_object* v_inst_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_String_skipSuffix_x3f(v_00_u03c1_620_, v_s_621_, v_pat_622_, v_inst_623_);
lean_dec(v_pat_622_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_String_skipSuffixWhile___redArg(lean_object* v_s_625_, lean_object* v_inst_626_){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_627_ = lean_unsigned_to_nat(0u);
v___x_628_ = lean_string_utf8_byte_size(v_s_625_);
v___x_629_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_629_, 0, v_s_625_);
lean_ctor_set(v___x_629_, 1, v___x_627_);
lean_ctor_set(v___x_629_, 2, v___x_628_);
v___x_630_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_629_, v___x_628_, v_inst_626_);
lean_dec_ref(v___x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_String_skipSuffixWhile(lean_object* v_00_u03c1_631_, lean_object* v_s_632_, lean_object* v_pat_633_, lean_object* v_inst_634_){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_635_ = lean_unsigned_to_nat(0u);
v___x_636_ = lean_string_utf8_byte_size(v_s_632_);
v___x_637_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_637_, 0, v_s_632_);
lean_ctor_set(v___x_637_, 1, v___x_635_);
lean_ctor_set(v___x_637_, 2, v___x_636_);
v___x_638_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_637_, v___x_636_, v_inst_634_);
lean_dec_ref(v___x_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_String_skipSuffixWhile___boxed(lean_object* v_00_u03c1_639_, lean_object* v_s_640_, lean_object* v_pat_641_, lean_object* v_inst_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_String_skipSuffixWhile(v_00_u03c1_639_, v_s_640_, v_pat_641_, v_inst_642_);
lean_dec(v_pat_641_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_revSkip_x3f___redArg(lean_object* v_s_644_, lean_object* v_pos_645_, lean_object* v_inst_646_){
_start:
{
lean_object* v_skipSuffix_x3f_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_665_; 
v_skipSuffix_x3f_647_ = lean_ctor_get(v_inst_646_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v_inst_646_);
if (v_isSharedCheck_665_ == 0)
{
lean_object* v_unused_666_; lean_object* v_unused_667_; 
v_unused_666_ = lean_ctor_get(v_inst_646_, 2);
lean_dec(v_unused_666_);
v_unused_667_ = lean_ctor_get(v_inst_646_, 1);
lean_dec(v_unused_667_);
v___x_649_ = v_inst_646_;
v_isShared_650_ = v_isSharedCheck_665_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_skipSuffix_x3f_647_);
lean_dec(v_inst_646_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_665_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_651_; lean_object* v___x_653_; 
v___x_651_ = lean_unsigned_to_nat(0u);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 2, v_pos_645_);
lean_ctor_set(v___x_649_, 1, v___x_651_);
lean_ctor_set(v___x_649_, 0, v_s_644_);
v___x_653_ = v___x_649_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_s_644_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_664_, 2, v_pos_645_);
v___x_653_ = v_reuseFailAlloc_664_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
lean_object* v___x_654_; 
v___x_654_ = lean_apply_1(v_skipSuffix_x3f_647_, v___x_653_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v___x_655_; 
v___x_655_ = lean_box(0);
return v___x_655_;
}
else
{
lean_object* v_val_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
v_val_656_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_663_ == 0)
{
v___x_658_ = v___x_654_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_val_656_);
lean_dec(v___x_654_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_val_656_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_revSkip_x3f(lean_object* v_00_u03c1_668_, lean_object* v_s_669_, lean_object* v_pos_670_, lean_object* v_pat_671_, lean_object* v_inst_672_){
_start:
{
lean_object* v_skipSuffix_x3f_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_691_; 
v_skipSuffix_x3f_673_ = lean_ctor_get(v_inst_672_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v_inst_672_);
if (v_isSharedCheck_691_ == 0)
{
lean_object* v_unused_692_; lean_object* v_unused_693_; 
v_unused_692_ = lean_ctor_get(v_inst_672_, 2);
lean_dec(v_unused_692_);
v_unused_693_ = lean_ctor_get(v_inst_672_, 1);
lean_dec(v_unused_693_);
v___x_675_ = v_inst_672_;
v_isShared_676_ = v_isSharedCheck_691_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_skipSuffix_x3f_673_);
lean_dec(v_inst_672_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_691_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_677_ = lean_unsigned_to_nat(0u);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 2, v_pos_670_);
lean_ctor_set(v___x_675_, 1, v___x_677_);
lean_ctor_set(v___x_675_, 0, v_s_669_);
v___x_679_ = v___x_675_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_s_669_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v___x_677_);
lean_ctor_set(v_reuseFailAlloc_690_, 2, v_pos_670_);
v___x_679_ = v_reuseFailAlloc_690_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_680_; 
v___x_680_ = lean_apply_1(v_skipSuffix_x3f_673_, v___x_679_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v___x_681_; 
v___x_681_ = lean_box(0);
return v___x_681_;
}
else
{
lean_object* v_val_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
v_val_682_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_680_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_val_682_);
lean_dec(v___x_680_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_val_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_revSkip_x3f___boxed(lean_object* v_00_u03c1_694_, lean_object* v_s_695_, lean_object* v_pos_696_, lean_object* v_pat_697_, lean_object* v_inst_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_String_Pos_revSkip_x3f(v_00_u03c1_694_, v_s_695_, v_pos_696_, v_pat_697_, v_inst_698_);
lean_dec(v_pat_697_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_revSkipWhile___redArg(lean_object* v_s_700_, lean_object* v_pos_701_, lean_object* v_inst_702_){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_703_ = lean_unsigned_to_nat(0u);
v___x_704_ = lean_string_utf8_byte_size(v_s_700_);
v___x_705_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_705_, 0, v_s_700_);
lean_ctor_set(v___x_705_, 1, v___x_703_);
lean_ctor_set(v___x_705_, 2, v___x_704_);
v___x_706_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_705_, v_pos_701_, v_inst_702_);
lean_dec_ref(v___x_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_revSkipWhile(lean_object* v_00_u03c1_707_, lean_object* v_s_708_, lean_object* v_pos_709_, lean_object* v_pat_710_, lean_object* v_inst_711_){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_712_ = lean_unsigned_to_nat(0u);
v___x_713_ = lean_string_utf8_byte_size(v_s_708_);
v___x_714_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_714_, 0, v_s_708_);
lean_ctor_set(v___x_714_, 1, v___x_712_);
lean_ctor_set(v___x_714_, 2, v___x_713_);
v___x_715_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_714_, v_pos_709_, v_inst_711_);
lean_dec_ref(v___x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_revSkipWhile___boxed(lean_object* v_00_u03c1_716_, lean_object* v_s_717_, lean_object* v_pos_718_, lean_object* v_pat_719_, lean_object* v_inst_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_String_Pos_revSkipWhile(v_00_u03c1_716_, v_s_717_, v_pos_718_, v_pat_719_, v_inst_720_);
lean_dec(v_pat_719_);
return v_res_721_;
}
}
static lean_object* _init_l_String_trimAsciiEnd___closed__1(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = ((lean_object*)(l_String_trimAsciiEnd___closed__0));
v___x_724_ = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool(v___x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_String_trimAsciiEnd(lean_object* v_s_725_){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_726_ = lean_unsigned_to_nat(0u);
v___x_727_ = lean_string_utf8_byte_size(v_s_725_);
lean_inc_ref(v_s_725_);
v___x_728_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_728_, 0, v_s_725_);
lean_ctor_set(v___x_728_, 1, v___x_726_);
lean_ctor_set(v___x_728_, 2, v___x_727_);
v___x_729_ = lean_obj_once(&l_String_trimAsciiEnd___closed__1, &l_String_trimAsciiEnd___closed__1_once, _init_l_String_trimAsciiEnd___closed__1);
v___x_730_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_728_, v___x_727_, v___x_729_);
lean_dec_ref(v___x_728_);
v___x_731_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_731_, 0, v_s_725_);
lean_ctor_set(v___x_731_, 1, v___x_726_);
lean_ctor_set(v___x_731_, 2, v___x_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_trimRight_spec__0(lean_object* v_s_732_, lean_object* v_pos_733_){
_start:
{
lean_object* v_str_734_; lean_object* v_startInclusive_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v_str_734_ = lean_ctor_get(v_s_732_, 0);
v_startInclusive_735_ = lean_ctor_get(v_s_732_, 1);
v___x_736_ = lean_nat_add(v_startInclusive_735_, v_pos_733_);
v___x_737_ = lean_nat_sub(v___x_736_, v_startInclusive_735_);
v___x_738_ = lean_unsigned_to_nat(0u);
v___x_739_ = lean_nat_dec_eq(v___x_737_, v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___y_748_; lean_object* v___x_749_; uint32_t v___x_750_; uint8_t v___y_752_; uint32_t v___x_757_; uint8_t v___x_758_; 
lean_inc(v_startInclusive_735_);
lean_inc_ref(v_str_734_);
v___x_740_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_740_, 0, v_str_734_);
lean_ctor_set(v___x_740_, 1, v_startInclusive_735_);
lean_ctor_set(v___x_740_, 2, v___x_736_);
v___x_741_ = lean_unsigned_to_nat(1u);
v___x_742_ = lean_nat_sub(v___x_737_, v___x_741_);
lean_dec(v___x_737_);
v___x_743_ = l_String_Slice_posLE(v___x_740_, v___x_742_);
lean_dec_ref(v___x_740_);
v___x_749_ = lean_nat_add(v_startInclusive_735_, v___x_743_);
v___x_750_ = lean_string_utf8_get_fast(v_str_734_, v___x_749_);
lean_dec(v___x_749_);
v___x_757_ = 32;
v___x_758_ = lean_uint32_dec_eq(v___x_750_, v___x_757_);
if (v___x_758_ == 0)
{
uint32_t v___x_759_; uint8_t v___x_760_; 
v___x_759_ = 9;
v___x_760_ = lean_uint32_dec_eq(v___x_750_, v___x_759_);
v___y_752_ = v___x_760_;
goto v___jp_751_;
}
else
{
v___y_752_ = v___x_758_;
goto v___jp_751_;
}
v___jp_744_:
{
uint8_t v___x_745_; 
v___x_745_ = lean_nat_dec_lt(v___x_743_, v_pos_733_);
if (v___x_745_ == 0)
{
lean_dec(v___x_743_);
return v_pos_733_;
}
else
{
lean_dec(v_pos_733_);
v_pos_733_ = v___x_743_;
goto _start;
}
}
v___jp_747_:
{
if (v___y_748_ == 0)
{
lean_dec(v___x_743_);
return v_pos_733_;
}
else
{
goto v___jp_744_;
}
}
v___jp_751_:
{
if (v___y_752_ == 0)
{
uint32_t v___x_753_; uint8_t v___x_754_; 
v___x_753_ = 13;
v___x_754_ = lean_uint32_dec_eq(v___x_750_, v___x_753_);
if (v___x_754_ == 0)
{
uint32_t v___x_755_; uint8_t v___x_756_; 
v___x_755_ = 10;
v___x_756_ = lean_uint32_dec_eq(v___x_750_, v___x_755_);
v___y_748_ = v___x_756_;
goto v___jp_747_;
}
else
{
v___y_748_ = v___x_754_;
goto v___jp_747_;
}
}
else
{
goto v___jp_744_;
}
}
}
else
{
lean_dec(v___x_737_);
lean_dec(v___x_736_);
return v_pos_733_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_trimRight_spec__0___boxed(lean_object* v_s_761_, lean_object* v_pos_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_String_Slice_Pos_revSkipWhile___at___00String_trimRight_spec__0(v_s_761_, v_pos_762_);
lean_dec_ref(v_s_761_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_String_trimRight(lean_object* v_s_764_){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_765_ = lean_unsigned_to_nat(0u);
v___x_766_ = lean_string_utf8_byte_size(v_s_764_);
lean_inc_ref(v_s_764_);
v___x_767_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_767_, 0, v_s_764_);
lean_ctor_set(v___x_767_, 1, v___x_765_);
lean_ctor_set(v___x_767_, 2, v___x_766_);
v___x_768_ = l_String_Slice_Pos_revSkipWhile___at___00String_trimRight_spec__0(v___x_767_, v___x_766_);
lean_dec_ref(v___x_767_);
v___x_769_ = lean_string_utf8_extract(v_s_764_, v___x_765_, v___x_768_);
lean_dec(v___x_768_);
lean_dec_ref(v_s_764_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimRight(lean_object* v_s_770_){
_start:
{
lean_object* v_str_771_; lean_object* v_startInclusive_772_; lean_object* v_endExclusive_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_783_; 
v_str_771_ = lean_ctor_get(v_s_770_, 0);
lean_inc_ref(v_str_771_);
v_startInclusive_772_ = lean_ctor_get(v_s_770_, 1);
lean_inc(v_startInclusive_772_);
v_endExclusive_773_ = lean_ctor_get(v_s_770_, 2);
v___x_774_ = lean_nat_sub(v_endExclusive_773_, v_startInclusive_772_);
v___x_775_ = l_String_Slice_Pos_revSkipWhile___at___00String_trimRight_spec__0(v_s_770_, v___x_774_);
v_isSharedCheck_783_ = !lean_is_exclusive(v_s_770_);
if (v_isSharedCheck_783_ == 0)
{
lean_object* v_unused_784_; lean_object* v_unused_785_; lean_object* v_unused_786_; 
v_unused_784_ = lean_ctor_get(v_s_770_, 2);
lean_dec(v_unused_784_);
v_unused_785_ = lean_ctor_get(v_s_770_, 1);
lean_dec(v_unused_785_);
v_unused_786_ = lean_ctor_get(v_s_770_, 0);
lean_dec(v_unused_786_);
v___x_777_ = v_s_770_;
v_isShared_778_ = v_isSharedCheck_783_;
goto v_resetjp_776_;
}
else
{
lean_dec(v_s_770_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_783_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_779_ = lean_nat_add(v_startInclusive_772_, v___x_775_);
lean_dec(v___x_775_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 2, v___x_779_);
v___x_781_ = v___x_777_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_str_771_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_startInclusive_772_);
lean_ctor_set(v_reuseFailAlloc_782_, 2, v___x_779_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
static lean_object* _init_l_String_trimAsciiStart___closed__0(void){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = ((lean_object*)(l_String_trimAsciiEnd___closed__0));
v___x_788_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___x_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_String_trimAsciiStart(lean_object* v_s_789_){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_790_ = lean_unsigned_to_nat(0u);
v___x_791_ = lean_string_utf8_byte_size(v_s_789_);
lean_inc_ref(v_s_789_);
v___x_792_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_792_, 0, v_s_789_);
lean_ctor_set(v___x_792_, 1, v___x_790_);
lean_ctor_set(v___x_792_, 2, v___x_791_);
v___x_793_ = lean_obj_once(&l_String_trimAsciiStart___closed__0, &l_String_trimAsciiStart___closed__0_once, _init_l_String_trimAsciiStart___closed__0);
v___x_794_ = l_String_Slice_Pos_skipWhile___redArg(v___x_792_, v___x_790_, v___x_793_);
lean_dec_ref(v___x_792_);
v___x_795_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_795_, 0, v_s_789_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
lean_ctor_set(v___x_795_, 2, v___x_791_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00String_trimLeft_spec__0(lean_object* v_s_796_, lean_object* v_pos_797_){
_start:
{
lean_object* v_str_798_; lean_object* v_startInclusive_799_; lean_object* v_endExclusive_800_; lean_object* v___x_801_; uint8_t v___y_809_; lean_object* v___x_810_; lean_object* v___x_811_; uint8_t v___x_812_; 
v_str_798_ = lean_ctor_get(v_s_796_, 0);
v_startInclusive_799_ = lean_ctor_get(v_s_796_, 1);
v_endExclusive_800_ = lean_ctor_get(v_s_796_, 2);
v___x_801_ = lean_nat_add(v_startInclusive_799_, v_pos_797_);
v___x_810_ = lean_unsigned_to_nat(0u);
v___x_811_ = lean_nat_sub(v_endExclusive_800_, v___x_801_);
v___x_812_ = lean_nat_dec_eq(v___x_810_, v___x_811_);
lean_dec(v___x_811_);
if (v___x_812_ == 0)
{
uint32_t v___x_813_; uint8_t v___y_815_; uint32_t v___x_820_; uint8_t v___x_821_; 
v___x_813_ = lean_string_utf8_get_fast(v_str_798_, v___x_801_);
v___x_820_ = 32;
v___x_821_ = lean_uint32_dec_eq(v___x_813_, v___x_820_);
if (v___x_821_ == 0)
{
uint32_t v___x_822_; uint8_t v___x_823_; 
v___x_822_ = 9;
v___x_823_ = lean_uint32_dec_eq(v___x_813_, v___x_822_);
v___y_815_ = v___x_823_;
goto v___jp_814_;
}
else
{
v___y_815_ = v___x_821_;
goto v___jp_814_;
}
v___jp_814_:
{
if (v___y_815_ == 0)
{
uint32_t v___x_816_; uint8_t v___x_817_; 
v___x_816_ = 13;
v___x_817_ = lean_uint32_dec_eq(v___x_813_, v___x_816_);
if (v___x_817_ == 0)
{
uint32_t v___x_818_; uint8_t v___x_819_; 
v___x_818_ = 10;
v___x_819_ = lean_uint32_dec_eq(v___x_813_, v___x_818_);
v___y_809_ = v___x_819_;
goto v___jp_808_;
}
else
{
v___y_809_ = v___x_817_;
goto v___jp_808_;
}
}
else
{
goto v___jp_802_;
}
}
}
else
{
lean_dec(v___x_801_);
return v_pos_797_;
}
v___jp_802_:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v___x_803_ = lean_string_utf8_next_fast(v_str_798_, v___x_801_);
v___x_804_ = lean_nat_sub(v___x_803_, v___x_801_);
lean_dec(v___x_801_);
v___x_805_ = lean_nat_add(v_pos_797_, v___x_804_);
lean_dec(v___x_804_);
v___x_806_ = lean_nat_dec_lt(v_pos_797_, v___x_805_);
if (v___x_806_ == 0)
{
lean_dec(v___x_805_);
return v_pos_797_;
}
else
{
lean_dec(v_pos_797_);
v_pos_797_ = v___x_805_;
goto _start;
}
}
v___jp_808_:
{
if (v___y_809_ == 0)
{
lean_dec(v___x_801_);
return v_pos_797_;
}
else
{
goto v___jp_802_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00String_trimLeft_spec__0___boxed(lean_object* v_s_824_, lean_object* v_pos_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_String_Slice_Pos_skipWhile___at___00String_trimLeft_spec__0(v_s_824_, v_pos_825_);
lean_dec_ref(v_s_824_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_String_trimLeft(lean_object* v_s_827_){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_828_ = lean_unsigned_to_nat(0u);
v___x_829_ = lean_string_utf8_byte_size(v_s_827_);
lean_inc_ref(v_s_827_);
v___x_830_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_830_, 0, v_s_827_);
lean_ctor_set(v___x_830_, 1, v___x_828_);
lean_ctor_set(v___x_830_, 2, v___x_829_);
v___x_831_ = l_String_Slice_Pos_skipWhile___at___00String_trimLeft_spec__0(v___x_830_, v___x_828_);
lean_dec_ref(v___x_830_);
v___x_832_ = lean_string_utf8_extract(v_s_827_, v___x_831_, v___x_829_);
lean_dec(v___x_831_);
lean_dec_ref(v_s_827_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimLeft(lean_object* v_s_833_){
_start:
{
lean_object* v_str_834_; lean_object* v_startInclusive_835_; lean_object* v_endExclusive_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_846_; 
v_str_834_ = lean_ctor_get(v_s_833_, 0);
lean_inc_ref(v_str_834_);
v_startInclusive_835_ = lean_ctor_get(v_s_833_, 1);
lean_inc(v_startInclusive_835_);
v_endExclusive_836_ = lean_ctor_get(v_s_833_, 2);
lean_inc(v_endExclusive_836_);
v___x_837_ = lean_unsigned_to_nat(0u);
v___x_838_ = l_String_Slice_Pos_skipWhile___at___00String_trimLeft_spec__0(v_s_833_, v___x_837_);
v_isSharedCheck_846_ = !lean_is_exclusive(v_s_833_);
if (v_isSharedCheck_846_ == 0)
{
lean_object* v_unused_847_; lean_object* v_unused_848_; lean_object* v_unused_849_; 
v_unused_847_ = lean_ctor_get(v_s_833_, 2);
lean_dec(v_unused_847_);
v_unused_848_ = lean_ctor_get(v_s_833_, 1);
lean_dec(v_unused_848_);
v_unused_849_ = lean_ctor_get(v_s_833_, 0);
lean_dec(v_unused_849_);
v___x_840_ = v_s_833_;
v_isShared_841_ = v_isSharedCheck_846_;
goto v_resetjp_839_;
}
else
{
lean_dec(v_s_833_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_846_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_842_; lean_object* v___x_844_; 
v___x_842_ = lean_nat_add(v_startInclusive_835_, v___x_838_);
lean_dec(v___x_838_);
lean_dec(v_startInclusive_835_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 1, v___x_842_);
v___x_844_ = v___x_840_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_str_834_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v___x_842_);
lean_ctor_set(v_reuseFailAlloc_845_, 2, v_endExclusive_836_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_trimAscii(lean_object* v_s_850_){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_851_ = lean_unsigned_to_nat(0u);
v___x_852_ = lean_string_utf8_byte_size(v_s_850_);
v___x_853_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_853_, 0, v_s_850_);
lean_ctor_set(v___x_853_, 1, v___x_851_);
lean_ctor_set(v___x_853_, 2, v___x_852_);
v___x_854_ = l_String_Slice_trimAscii(v___x_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_String_trim(lean_object* v_s_855_){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v_str_860_; lean_object* v_startInclusive_861_; lean_object* v_endExclusive_862_; lean_object* v___x_863_; 
v___x_856_ = lean_unsigned_to_nat(0u);
v___x_857_ = lean_string_utf8_byte_size(v_s_855_);
v___x_858_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_858_, 0, v_s_855_);
lean_ctor_set(v___x_858_, 1, v___x_856_);
lean_ctor_set(v___x_858_, 2, v___x_857_);
v___x_859_ = l_String_Slice_trimAscii(v___x_858_);
v_str_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc_ref(v_str_860_);
v_startInclusive_861_ = lean_ctor_get(v___x_859_, 1);
lean_inc(v_startInclusive_861_);
v_endExclusive_862_ = lean_ctor_get(v___x_859_, 2);
lean_inc(v_endExclusive_862_);
lean_dec_ref(v___x_859_);
v___x_863_ = lean_string_utf8_extract(v_str_860_, v_startInclusive_861_, v_endExclusive_862_);
lean_dec(v_endExclusive_862_);
lean_dec(v_startInclusive_861_);
lean_dec_ref(v_str_860_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trim(lean_object* v_s_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_String_Slice_trimAscii(v_s_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* lean_string_trim(lean_object* v_s_866_){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v_str_871_; lean_object* v_startInclusive_872_; lean_object* v_endExclusive_873_; lean_object* v___x_874_; 
v___x_867_ = lean_unsigned_to_nat(0u);
v___x_868_ = lean_string_utf8_byte_size(v_s_866_);
v___x_869_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_869_, 0, v_s_866_);
lean_ctor_set(v___x_869_, 1, v___x_867_);
lean_ctor_set(v___x_869_, 2, v___x_868_);
v___x_870_ = l_String_Slice_trimAscii(v___x_869_);
v_str_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc_ref(v_str_871_);
v_startInclusive_872_ = lean_ctor_get(v___x_870_, 1);
lean_inc(v_startInclusive_872_);
v_endExclusive_873_ = lean_ctor_get(v___x_870_, 2);
lean_inc(v_endExclusive_873_);
lean_dec_ref(v___x_870_);
v___x_874_ = lean_string_utf8_extract(v_str_871_, v_startInclusive_872_, v_endExclusive_873_);
lean_dec(v_endExclusive_873_);
lean_dec(v_startInclusive_872_);
lean_dec_ref(v_str_871_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextWhile(lean_object* v_s_875_, lean_object* v_p_876_, lean_object* v_i_877_){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = lean_string_utf8_byte_size(v_s_875_);
v___x_879_ = l_Substring_Raw_takeWhileAux(v_s_875_, v___x_878_, v_p_876_, v_i_877_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextWhile___boxed(lean_object* v_s_880_, lean_object* v_p_881_, lean_object* v_i_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_String_Pos_Raw_nextWhile(v_s_880_, v_p_881_, v_i_882_);
lean_dec_ref(v_s_880_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_String_nextWhile(lean_object* v_s_884_, lean_object* v_p_885_, lean_object* v_i_886_){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = lean_string_utf8_byte_size(v_s_884_);
v___x_888_ = l_Substring_Raw_takeWhileAux(v_s_884_, v___x_887_, v_p_885_, v_i_886_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_String_nextWhile___boxed(lean_object* v_s_889_, lean_object* v_p_890_, lean_object* v_i_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_String_nextWhile(v_s_889_, v_p_890_, v_i_891_);
lean_dec_ref(v_s_889_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0(lean_object* v_p_893_, lean_object* v_s_894_, lean_object* v_stopPos_895_, lean_object* v_i_896_){
_start:
{
uint8_t v___x_897_; 
v___x_897_ = lean_nat_dec_lt(v_i_896_, v_stopPos_895_);
if (v___x_897_ == 0)
{
lean_dec_ref(v_p_893_);
return v_i_896_;
}
else
{
uint32_t v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; uint8_t v___x_901_; 
v___x_898_ = lean_string_utf8_get(v_s_894_, v_i_896_);
v___x_899_ = lean_box_uint32(v___x_898_);
lean_inc_ref(v_p_893_);
v___x_900_ = lean_apply_1(v_p_893_, v___x_899_);
v___x_901_ = lean_unbox(v___x_900_);
if (v___x_901_ == 0)
{
lean_dec_ref(v_p_893_);
return v_i_896_;
}
else
{
lean_object* v___x_902_; 
v___x_902_ = lean_string_utf8_next(v_s_894_, v_i_896_);
lean_dec(v_i_896_);
v_i_896_ = v___x_902_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0___boxed(lean_object* v_p_904_, lean_object* v_s_905_, lean_object* v_stopPos_906_, lean_object* v_i_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0(v_p_904_, v_s_905_, v_stopPos_906_, v_i_907_);
lean_dec(v_stopPos_906_);
lean_dec_ref(v_s_905_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* lean_string_nextwhile(lean_object* v_s_909_, lean_object* v_p_910_, lean_object* v_i_911_){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = lean_string_utf8_byte_size(v_s_909_);
v___x_913_ = l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0(v_p_910_, v_s_909_, v___x_912_, v_i_911_);
lean_dec_ref(v_s_909_);
return v___x_913_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_Raw_nextUntil___lam__0(lean_object* v_p_914_, uint32_t v_c_915_){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; uint8_t v___x_918_; 
v___x_916_ = lean_box_uint32(v_c_915_);
v___x_917_ = lean_apply_1(v_p_914_, v___x_916_);
v___x_918_ = lean_unbox(v___x_917_);
if (v___x_918_ == 0)
{
uint8_t v___x_919_; 
v___x_919_ = 1;
return v___x_919_;
}
else
{
uint8_t v___x_920_; 
v___x_920_ = 0;
return v___x_920_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextUntil___lam__0___boxed(lean_object* v_p_921_, lean_object* v_c_922_){
_start:
{
uint32_t v_c_boxed_923_; uint8_t v_res_924_; lean_object* v_r_925_; 
v_c_boxed_923_ = lean_unbox_uint32(v_c_922_);
lean_dec(v_c_922_);
v_res_924_ = l_String_Pos_Raw_nextUntil___lam__0(v_p_921_, v_c_boxed_923_);
v_r_925_ = lean_box(v_res_924_);
return v_r_925_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextUntil(lean_object* v_s_926_, lean_object* v_p_927_, lean_object* v_i_928_){
_start:
{
lean_object* v___f_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___f_929_ = lean_alloc_closure((void*)(l_String_Pos_Raw_nextUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_929_, 0, v_p_927_);
v___x_930_ = lean_string_utf8_byte_size(v_s_926_);
v___x_931_ = l_Substring_Raw_takeWhileAux(v_s_926_, v___x_930_, v___f_929_, v_i_928_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextUntil___boxed(lean_object* v_s_932_, lean_object* v_p_933_, lean_object* v_i_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_String_Pos_Raw_nextUntil(v_s_932_, v_p_933_, v_i_934_);
lean_dec_ref(v_s_932_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0(lean_object* v_p_936_, lean_object* v_s_937_, lean_object* v_stopPos_938_, lean_object* v_i_939_){
_start:
{
uint8_t v___x_940_; 
v___x_940_ = lean_nat_dec_lt(v_i_939_, v_stopPos_938_);
if (v___x_940_ == 0)
{
lean_dec_ref(v_p_936_);
return v_i_939_;
}
else
{
uint32_t v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; uint8_t v___x_944_; 
v___x_941_ = lean_string_utf8_get(v_s_937_, v_i_939_);
v___x_942_ = lean_box_uint32(v___x_941_);
lean_inc_ref(v_p_936_);
v___x_943_ = lean_apply_1(v_p_936_, v___x_942_);
v___x_944_ = lean_unbox(v___x_943_);
if (v___x_944_ == 0)
{
lean_object* v___x_945_; 
v___x_945_ = lean_string_utf8_next(v_s_937_, v_i_939_);
lean_dec(v_i_939_);
v_i_939_ = v___x_945_;
goto _start;
}
else
{
lean_dec_ref(v_p_936_);
return v_i_939_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0___boxed(lean_object* v_p_947_, lean_object* v_s_948_, lean_object* v_stopPos_949_, lean_object* v_i_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0(v_p_947_, v_s_948_, v_stopPos_949_, v_i_950_);
lean_dec(v_stopPos_949_);
lean_dec_ref(v_s_948_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_String_nextUntil(lean_object* v_s_952_, lean_object* v_p_953_, lean_object* v_i_954_){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = lean_string_utf8_byte_size(v_s_952_);
v___x_956_ = l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0(v_p_953_, v_s_952_, v___x_955_, v_i_954_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_String_nextUntil___boxed(lean_object* v_s_957_, lean_object* v_p_958_, lean_object* v_i_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_String_nextUntil(v_s_957_, v_p_958_, v_i_959_);
lean_dec_ref(v_s_957_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___redArg(lean_object* v_s_961_, lean_object* v_inst_962_){
_start:
{
lean_object* v_skipPrefix_x3f_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_983_; 
v_skipPrefix_x3f_963_ = lean_ctor_get(v_inst_962_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v_inst_962_);
if (v_isSharedCheck_983_ == 0)
{
lean_object* v_unused_984_; lean_object* v_unused_985_; 
v_unused_984_ = lean_ctor_get(v_inst_962_, 2);
lean_dec(v_unused_984_);
v_unused_985_ = lean_ctor_get(v_inst_962_, 1);
lean_dec(v_unused_985_);
v___x_965_ = v_inst_962_;
v_isShared_966_ = v_isSharedCheck_983_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_skipPrefix_x3f_963_);
lean_dec(v_inst_962_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_983_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_970_; 
v___x_967_ = lean_string_utf8_byte_size(v_s_961_);
v___x_968_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_s_961_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 2, v___x_967_);
lean_ctor_set(v___x_965_, 1, v___x_968_);
lean_ctor_set(v___x_965_, 0, v_s_961_);
v___x_970_ = v___x_965_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_s_961_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_982_, 2, v___x_967_);
v___x_970_ = v_reuseFailAlloc_982_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
lean_object* v___x_971_; 
v___x_971_ = lean_apply_1(v_skipPrefix_x3f_963_, v___x_970_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v___x_972_; 
lean_dec_ref(v_s_961_);
v___x_972_ = lean_box(0);
return v___x_972_;
}
else
{
lean_object* v_val_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_981_; 
v_val_973_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_981_ == 0)
{
v___x_975_ = v___x_971_;
v_isShared_976_ = v_isSharedCheck_981_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_val_973_);
lean_dec(v___x_971_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_981_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_977_; lean_object* v___x_979_; 
v___x_977_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_977_, 0, v_s_961_);
lean_ctor_set(v___x_977_, 1, v_val_973_);
lean_ctor_set(v___x_977_, 2, v___x_967_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_977_);
v___x_979_ = v___x_975_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v___x_977_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f(lean_object* v_00_u03c1_986_, lean_object* v_s_987_, lean_object* v_pat_988_, lean_object* v_inst_989_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l_String_dropPrefix_x3f___redArg(v_s_987_, v_inst_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___boxed(lean_object* v_00_u03c1_991_, lean_object* v_s_992_, lean_object* v_pat_993_, lean_object* v_inst_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_String_dropPrefix_x3f(v_00_u03c1_991_, v_s_992_, v_pat_993_, v_inst_994_);
lean_dec(v_pat_993_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___redArg(lean_object* v_s_996_, lean_object* v_inst_997_){
_start:
{
lean_object* v_skipSuffix_x3f_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1018_; 
v_skipSuffix_x3f_998_ = lean_ctor_get(v_inst_997_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_inst_997_);
if (v_isSharedCheck_1018_ == 0)
{
lean_object* v_unused_1019_; lean_object* v_unused_1020_; 
v_unused_1019_ = lean_ctor_get(v_inst_997_, 2);
lean_dec(v_unused_1019_);
v_unused_1020_ = lean_ctor_get(v_inst_997_, 1);
lean_dec(v_unused_1020_);
v___x_1000_ = v_inst_997_;
v_isShared_1001_ = v_isSharedCheck_1018_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_skipSuffix_x3f_998_);
lean_dec(v_inst_997_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1018_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_1002_ = lean_string_utf8_byte_size(v_s_996_);
v___x_1003_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_s_996_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 2, v___x_1002_);
lean_ctor_set(v___x_1000_, 1, v___x_1003_);
lean_ctor_set(v___x_1000_, 0, v_s_996_);
v___x_1005_ = v___x_1000_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_s_996_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v___x_1003_);
lean_ctor_set(v_reuseFailAlloc_1017_, 2, v___x_1002_);
v___x_1005_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1006_; 
v___x_1006_ = lean_apply_1(v_skipSuffix_x3f_998_, v___x_1005_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v___x_1007_; 
lean_dec_ref(v_s_996_);
v___x_1007_ = lean_box(0);
return v___x_1007_;
}
else
{
lean_object* v_val_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1016_; 
v_val_1008_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1010_ = v___x_1006_;
v_isShared_1011_ = v_isSharedCheck_1016_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_val_1008_);
lean_dec(v___x_1006_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1016_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1012_; lean_object* v___x_1014_; 
v___x_1012_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1012_, 0, v_s_996_);
lean_ctor_set(v___x_1012_, 1, v___x_1003_);
lean_ctor_set(v___x_1012_, 2, v_val_1008_);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 0, v___x_1012_);
v___x_1014_ = v___x_1010_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1012_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f(lean_object* v_00_u03c1_1021_, lean_object* v_s_1022_, lean_object* v_pat_1023_, lean_object* v_inst_1024_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_String_dropSuffix_x3f___redArg(v_s_1022_, v_inst_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___boxed(lean_object* v_00_u03c1_1026_, lean_object* v_s_1027_, lean_object* v_pat_1028_, lean_object* v_inst_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_String_dropSuffix_x3f(v_00_u03c1_1026_, v_s_1027_, v_pat_1028_, v_inst_1029_);
lean_dec(v_pat_1028_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix___redArg(lean_object* v_s_1031_, lean_object* v_inst_1032_){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1033_ = lean_unsigned_to_nat(0u);
v___x_1034_ = lean_string_utf8_byte_size(v_s_1031_);
v___x_1035_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1035_, 0, v_s_1031_);
lean_ctor_set(v___x_1035_, 1, v___x_1033_);
lean_ctor_set(v___x_1035_, 2, v___x_1034_);
v___x_1036_ = l_String_Slice_dropPrefix___redArg(v___x_1035_, v_inst_1032_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix(lean_object* v_00_u03c1_1037_, lean_object* v_s_1038_, lean_object* v_pat_1039_, lean_object* v_inst_1040_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_String_dropPrefix___redArg(v_s_1038_, v_inst_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix___boxed(lean_object* v_00_u03c1_1042_, lean_object* v_s_1043_, lean_object* v_pat_1044_, lean_object* v_inst_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_String_dropPrefix(v_00_u03c1_1042_, v_s_1043_, v_pat_1044_, v_inst_1045_);
lean_dec(v_pat_1044_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg(lean_object* v_pre_1047_, lean_object* v_s_1048_){
_start:
{
lean_object* v_str_1049_; lean_object* v_startInclusive_1050_; lean_object* v_endExclusive_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; uint8_t v___x_1054_; 
v_str_1049_ = lean_ctor_get(v_s_1048_, 0);
v_startInclusive_1050_ = lean_ctor_get(v_s_1048_, 1);
v_endExclusive_1051_ = lean_ctor_get(v_s_1048_, 2);
v___x_1052_ = lean_string_utf8_byte_size(v_pre_1047_);
v___x_1053_ = lean_nat_sub(v_endExclusive_1051_, v_startInclusive_1050_);
v___x_1054_ = lean_nat_dec_le(v___x_1052_, v___x_1053_);
lean_dec(v___x_1053_);
if (v___x_1054_ == 0)
{
return v_s_1048_;
}
else
{
lean_object* v___x_1055_; uint8_t v___x_1056_; 
v___x_1055_ = lean_unsigned_to_nat(0u);
v___x_1056_ = lean_string_memcmp(v_str_1049_, v_pre_1047_, v_startInclusive_1050_, v___x_1055_, v___x_1052_);
if (v___x_1056_ == 0)
{
return v_s_1048_;
}
else
{
lean_object* v___x_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1065_; 
lean_inc(v_endExclusive_1051_);
lean_inc(v_startInclusive_1050_);
lean_inc_ref(v_str_1049_);
v___x_1057_ = l_String_Slice_pos_x21(v_s_1048_, v___x_1052_);
v_isSharedCheck_1065_ = !lean_is_exclusive(v_s_1048_);
if (v_isSharedCheck_1065_ == 0)
{
lean_object* v_unused_1066_; lean_object* v_unused_1067_; lean_object* v_unused_1068_; 
v_unused_1066_ = lean_ctor_get(v_s_1048_, 2);
lean_dec(v_unused_1066_);
v_unused_1067_ = lean_ctor_get(v_s_1048_, 1);
lean_dec(v_unused_1067_);
v_unused_1068_ = lean_ctor_get(v_s_1048_, 0);
lean_dec(v_unused_1068_);
v___x_1059_ = v_s_1048_;
v_isShared_1060_ = v_isSharedCheck_1065_;
goto v_resetjp_1058_;
}
else
{
lean_dec(v_s_1048_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1065_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1061_; lean_object* v___x_1063_; 
v___x_1061_ = lean_nat_add(v_startInclusive_1050_, v___x_1057_);
lean_dec(v___x_1057_);
lean_dec(v_startInclusive_1050_);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 1, v___x_1061_);
v___x_1063_ = v___x_1059_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_str_1049_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v___x_1061_);
lean_ctor_set(v_reuseFailAlloc_1064_, 2, v_endExclusive_1051_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg___boxed(lean_object* v_pre_1069_, lean_object* v_s_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg(v_pre_1069_, v_s_1070_);
lean_dec_ref(v_pre_1069_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix___at___00String_stripPrefix_spec__0(lean_object* v_pre_1072_, lean_object* v_s_1073_, lean_object* v_pat_1074_){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1075_ = lean_unsigned_to_nat(0u);
v___x_1076_ = lean_string_utf8_byte_size(v_s_1073_);
v___x_1077_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1077_, 0, v_s_1073_);
lean_ctor_set(v___x_1077_, 1, v___x_1075_);
lean_ctor_set(v___x_1077_, 2, v___x_1076_);
v___x_1078_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg(v_pre_1072_, v___x_1077_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix___at___00String_stripPrefix_spec__0___boxed(lean_object* v_pre_1079_, lean_object* v_s_1080_, lean_object* v_pat_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_String_dropPrefix___at___00String_stripPrefix_spec__0(v_pre_1079_, v_s_1080_, v_pat_1081_);
lean_dec_ref(v_pat_1081_);
lean_dec_ref(v_pre_1079_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_String_stripPrefix(lean_object* v_s_1083_, lean_object* v_pre_1084_){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = l_String_dropPrefix___at___00String_stripPrefix_spec__0(v_pre_1084_, v_s_1083_, v_pre_1084_);
v___x_1086_ = l_String_Slice_toString(v___x_1085_);
lean_dec_ref(v___x_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_String_stripPrefix___boxed(lean_object* v_s_1087_, lean_object* v_pre_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_String_stripPrefix(v_s_1087_, v_pre_1088_);
lean_dec_ref(v_pre_1088_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0(lean_object* v_pat_1090_, lean_object* v_pre_1091_, lean_object* v_s_1092_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg(v_pre_1091_, v_s_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___boxed(lean_object* v_pat_1094_, lean_object* v_pre_1095_, lean_object* v_s_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0(v_pat_1094_, v_pre_1095_, v_s_1096_);
lean_dec_ref(v_pre_1095_);
lean_dec_ref(v_pat_1094_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_Slice_stripPrefix_spec__0(lean_object* v_pre_1098_, lean_object* v_s_1099_){
_start:
{
lean_object* v_str_1100_; lean_object* v_startInclusive_1101_; lean_object* v_endExclusive_1102_; lean_object* v_str_1103_; lean_object* v_startInclusive_1104_; lean_object* v_endExclusive_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; uint8_t v___x_1108_; 
v_str_1100_ = lean_ctor_get(v_pre_1098_, 0);
v_startInclusive_1101_ = lean_ctor_get(v_pre_1098_, 1);
v_endExclusive_1102_ = lean_ctor_get(v_pre_1098_, 2);
v_str_1103_ = lean_ctor_get(v_s_1099_, 0);
v_startInclusive_1104_ = lean_ctor_get(v_s_1099_, 1);
v_endExclusive_1105_ = lean_ctor_get(v_s_1099_, 2);
v___x_1106_ = lean_nat_sub(v_endExclusive_1102_, v_startInclusive_1101_);
v___x_1107_ = lean_nat_sub(v_endExclusive_1105_, v_startInclusive_1104_);
v___x_1108_ = lean_nat_dec_le(v___x_1106_, v___x_1107_);
lean_dec(v___x_1107_);
if (v___x_1108_ == 0)
{
lean_dec(v___x_1106_);
return v_s_1099_;
}
else
{
uint8_t v___x_1109_; 
v___x_1109_ = lean_string_memcmp(v_str_1103_, v_str_1100_, v_startInclusive_1104_, v_startInclusive_1101_, v___x_1106_);
if (v___x_1109_ == 0)
{
lean_dec(v___x_1106_);
return v_s_1099_;
}
else
{
lean_object* v___x_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1118_; 
lean_inc(v_endExclusive_1105_);
lean_inc(v_startInclusive_1104_);
lean_inc_ref(v_str_1103_);
v___x_1110_ = l_String_Slice_pos_x21(v_s_1099_, v___x_1106_);
lean_dec(v___x_1106_);
v_isSharedCheck_1118_ = !lean_is_exclusive(v_s_1099_);
if (v_isSharedCheck_1118_ == 0)
{
lean_object* v_unused_1119_; lean_object* v_unused_1120_; lean_object* v_unused_1121_; 
v_unused_1119_ = lean_ctor_get(v_s_1099_, 2);
lean_dec(v_unused_1119_);
v_unused_1120_ = lean_ctor_get(v_s_1099_, 1);
lean_dec(v_unused_1120_);
v_unused_1121_ = lean_ctor_get(v_s_1099_, 0);
lean_dec(v_unused_1121_);
v___x_1112_ = v_s_1099_;
v_isShared_1113_ = v_isSharedCheck_1118_;
goto v_resetjp_1111_;
}
else
{
lean_dec(v_s_1099_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1118_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1114_; lean_object* v___x_1116_; 
v___x_1114_ = lean_nat_add(v_startInclusive_1104_, v___x_1110_);
lean_dec(v___x_1110_);
lean_dec(v_startInclusive_1104_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 1, v___x_1114_);
v___x_1116_ = v___x_1112_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_str_1103_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v___x_1114_);
lean_ctor_set(v_reuseFailAlloc_1117_, 2, v_endExclusive_1105_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_Slice_stripPrefix_spec__0___boxed(lean_object* v_pre_1122_, lean_object* v_s_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_String_Slice_dropPrefix___at___00String_Slice_stripPrefix_spec__0(v_pre_1122_, v_s_1123_);
lean_dec_ref(v_pre_1122_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_stripPrefix(lean_object* v_s_1125_, lean_object* v_pre_1126_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_String_Slice_dropPrefix___at___00String_Slice_stripPrefix_spec__0(v_pre_1126_, v_s_1125_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_stripPrefix___boxed(lean_object* v_s_1128_, lean_object* v_pre_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_String_Slice_stripPrefix(v_s_1128_, v_pre_1129_);
lean_dec_ref(v_pre_1129_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix___redArg(lean_object* v_s_1131_, lean_object* v_inst_1132_){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1133_ = lean_unsigned_to_nat(0u);
v___x_1134_ = lean_string_utf8_byte_size(v_s_1131_);
v___x_1135_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1135_, 0, v_s_1131_);
lean_ctor_set(v___x_1135_, 1, v___x_1133_);
lean_ctor_set(v___x_1135_, 2, v___x_1134_);
v___x_1136_ = l_String_Slice_dropSuffix___redArg(v___x_1135_, v_inst_1132_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix(lean_object* v_00_u03c1_1137_, lean_object* v_s_1138_, lean_object* v_pat_1139_, lean_object* v_inst_1140_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_String_dropSuffix___redArg(v_s_1138_, v_inst_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix___boxed(lean_object* v_00_u03c1_1142_, lean_object* v_s_1143_, lean_object* v_pat_1144_, lean_object* v_inst_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_String_dropSuffix(v_00_u03c1_1142_, v_s_1143_, v_pat_1144_, v_inst_1145_);
lean_dec(v_pat_1144_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0___redArg(lean_object* v_suff_1147_, lean_object* v_s_1148_){
_start:
{
lean_object* v_str_1149_; lean_object* v_startInclusive_1150_; lean_object* v_endExclusive_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; 
v_str_1149_ = lean_ctor_get(v_s_1148_, 0);
v_startInclusive_1150_ = lean_ctor_get(v_s_1148_, 1);
v_endExclusive_1151_ = lean_ctor_get(v_s_1148_, 2);
v___x_1152_ = lean_string_utf8_byte_size(v_suff_1147_);
v___x_1153_ = lean_nat_sub(v_endExclusive_1151_, v_startInclusive_1150_);
v___x_1154_ = lean_nat_dec_le(v___x_1152_, v___x_1153_);
if (v___x_1154_ == 0)
{
lean_dec(v___x_1153_);
return v_s_1148_;
}
else
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; uint8_t v___x_1158_; 
v___x_1155_ = lean_unsigned_to_nat(0u);
v___x_1156_ = lean_nat_sub(v___x_1153_, v___x_1152_);
lean_dec(v___x_1153_);
v___x_1157_ = lean_nat_add(v_startInclusive_1150_, v___x_1156_);
v___x_1158_ = lean_string_memcmp(v_str_1149_, v_suff_1147_, v___x_1157_, v___x_1155_, v___x_1152_);
lean_dec(v___x_1157_);
if (v___x_1158_ == 0)
{
lean_dec(v___x_1156_);
return v_s_1148_;
}
else
{
lean_object* v___x_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1167_; 
lean_inc(v_startInclusive_1150_);
lean_inc_ref(v_str_1149_);
v___x_1159_ = l_String_Slice_pos_x21(v_s_1148_, v___x_1156_);
lean_dec(v___x_1156_);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_s_1148_);
if (v_isSharedCheck_1167_ == 0)
{
lean_object* v_unused_1168_; lean_object* v_unused_1169_; lean_object* v_unused_1170_; 
v_unused_1168_ = lean_ctor_get(v_s_1148_, 2);
lean_dec(v_unused_1168_);
v_unused_1169_ = lean_ctor_get(v_s_1148_, 1);
lean_dec(v_unused_1169_);
v_unused_1170_ = lean_ctor_get(v_s_1148_, 0);
lean_dec(v_unused_1170_);
v___x_1161_ = v_s_1148_;
v_isShared_1162_ = v_isSharedCheck_1167_;
goto v_resetjp_1160_;
}
else
{
lean_dec(v_s_1148_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1167_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1163_; lean_object* v___x_1165_; 
v___x_1163_ = lean_nat_add(v_startInclusive_1150_, v___x_1159_);
lean_dec(v___x_1159_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 2, v___x_1163_);
v___x_1165_ = v___x_1161_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_str_1149_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_startInclusive_1150_);
lean_ctor_set(v_reuseFailAlloc_1166_, 2, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0___redArg___boxed(lean_object* v_suff_1171_, lean_object* v_s_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0___redArg(v_suff_1171_, v_s_1172_);
lean_dec_ref(v_suff_1171_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix___at___00String_stripSuffix_spec__0(lean_object* v_suff_1174_, lean_object* v_s_1175_, lean_object* v_pat_1176_){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1177_ = lean_unsigned_to_nat(0u);
v___x_1178_ = lean_string_utf8_byte_size(v_s_1175_);
v___x_1179_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1179_, 0, v_s_1175_);
lean_ctor_set(v___x_1179_, 1, v___x_1177_);
lean_ctor_set(v___x_1179_, 2, v___x_1178_);
v___x_1180_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0___redArg(v_suff_1174_, v___x_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix___at___00String_stripSuffix_spec__0___boxed(lean_object* v_suff_1181_, lean_object* v_s_1182_, lean_object* v_pat_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_String_dropSuffix___at___00String_stripSuffix_spec__0(v_suff_1181_, v_s_1182_, v_pat_1183_);
lean_dec_ref(v_pat_1183_);
lean_dec_ref(v_suff_1181_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_String_stripSuffix(lean_object* v_s_1185_, lean_object* v_suff_1186_){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = l_String_dropSuffix___at___00String_stripSuffix_spec__0(v_suff_1186_, v_s_1185_, v_suff_1186_);
v___x_1188_ = l_String_Slice_toString(v___x_1187_);
lean_dec_ref(v___x_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_String_stripSuffix___boxed(lean_object* v_s_1189_, lean_object* v_suff_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_String_stripSuffix(v_s_1189_, v_suff_1190_);
lean_dec_ref(v_suff_1190_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0(lean_object* v_pat_1192_, lean_object* v_suff_1193_, lean_object* v_s_1194_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0___redArg(v_suff_1193_, v_s_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0___boxed(lean_object* v_pat_1196_, lean_object* v_suff_1197_, lean_object* v_s_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0(v_pat_1196_, v_suff_1197_, v_s_1198_);
lean_dec_ref(v_suff_1197_);
lean_dec_ref(v_pat_1196_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_Slice_stripSuffix_spec__0(lean_object* v_suff_1200_, lean_object* v_s_1201_){
_start:
{
lean_object* v_str_1202_; lean_object* v_startInclusive_1203_; lean_object* v_endExclusive_1204_; lean_object* v_str_1205_; lean_object* v_startInclusive_1206_; lean_object* v_endExclusive_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; uint8_t v___x_1210_; 
v_str_1202_ = lean_ctor_get(v_suff_1200_, 0);
v_startInclusive_1203_ = lean_ctor_get(v_suff_1200_, 1);
v_endExclusive_1204_ = lean_ctor_get(v_suff_1200_, 2);
v_str_1205_ = lean_ctor_get(v_s_1201_, 0);
v_startInclusive_1206_ = lean_ctor_get(v_s_1201_, 1);
v_endExclusive_1207_ = lean_ctor_get(v_s_1201_, 2);
v___x_1208_ = lean_nat_sub(v_endExclusive_1204_, v_startInclusive_1203_);
v___x_1209_ = lean_nat_sub(v_endExclusive_1207_, v_startInclusive_1206_);
v___x_1210_ = lean_nat_dec_le(v___x_1208_, v___x_1209_);
if (v___x_1210_ == 0)
{
lean_dec(v___x_1209_);
lean_dec(v___x_1208_);
return v_s_1201_;
}
else
{
lean_object* v___x_1211_; lean_object* v___x_1212_; uint8_t v___x_1213_; 
v___x_1211_ = lean_nat_sub(v___x_1209_, v___x_1208_);
lean_dec(v___x_1209_);
v___x_1212_ = lean_nat_add(v_startInclusive_1206_, v___x_1211_);
v___x_1213_ = lean_string_memcmp(v_str_1205_, v_str_1202_, v___x_1212_, v_startInclusive_1203_, v___x_1208_);
lean_dec(v___x_1208_);
lean_dec(v___x_1212_);
if (v___x_1213_ == 0)
{
lean_dec(v___x_1211_);
return v_s_1201_;
}
else
{
lean_object* v___x_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1222_; 
lean_inc(v_startInclusive_1206_);
lean_inc_ref(v_str_1205_);
v___x_1214_ = l_String_Slice_pos_x21(v_s_1201_, v___x_1211_);
lean_dec(v___x_1211_);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_s_1201_);
if (v_isSharedCheck_1222_ == 0)
{
lean_object* v_unused_1223_; lean_object* v_unused_1224_; lean_object* v_unused_1225_; 
v_unused_1223_ = lean_ctor_get(v_s_1201_, 2);
lean_dec(v_unused_1223_);
v_unused_1224_ = lean_ctor_get(v_s_1201_, 1);
lean_dec(v_unused_1224_);
v_unused_1225_ = lean_ctor_get(v_s_1201_, 0);
lean_dec(v_unused_1225_);
v___x_1216_ = v_s_1201_;
v_isShared_1217_ = v_isSharedCheck_1222_;
goto v_resetjp_1215_;
}
else
{
lean_dec(v_s_1201_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1222_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1218_ = lean_nat_add(v_startInclusive_1206_, v___x_1214_);
lean_dec(v___x_1214_);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 2, v___x_1218_);
v___x_1220_ = v___x_1216_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_str_1205_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v_startInclusive_1206_);
lean_ctor_set(v_reuseFailAlloc_1221_, 2, v___x_1218_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_Slice_stripSuffix_spec__0___boxed(lean_object* v_suff_1226_, lean_object* v_s_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_String_Slice_dropSuffix___at___00String_Slice_stripSuffix_spec__0(v_suff_1226_, v_s_1227_);
lean_dec_ref(v_suff_1226_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_stripSuffix(lean_object* v_s_1229_, lean_object* v_suff_1230_){
_start:
{
lean_object* v___x_1231_; 
v___x_1231_ = l_String_Slice_dropSuffix___at___00String_Slice_stripSuffix_spec__0(v_suff_1230_, v_s_1229_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_stripSuffix___boxed(lean_object* v_s_1232_, lean_object* v_suff_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_String_Slice_stripSuffix(v_s_1232_, v_suff_1233_);
lean_dec_ref(v_suff_1233_);
return v_res_1234_;
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

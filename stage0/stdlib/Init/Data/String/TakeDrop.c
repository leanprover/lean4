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
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_Pos_revSkipWhile___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_Raw_takeWhileAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_dropSuffix___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_skipWhile___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l_Char_isWhitespace___boxed(lean_object*);
lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool(lean_object*);
lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_String_Slice_dropPrefix___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
LEAN_EXPORT lean_object* l_String_drop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_string_drop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropRight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_string_dropright(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_takeEnd(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_dropEndWhile___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropEndWhile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropEndWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimRight_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimRight_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_trimRight(lean_object*);
static lean_once_cell_t l_String_trimAsciiStart___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_trimAsciiStart___closed__0;
LEAN_EXPORT lean_object* l_String_trimAsciiStart(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00String_Slice_trimLeft_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00String_Slice_trimLeft_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_trimLeft(lean_object*);
LEAN_EXPORT lean_object* l_String_trimAscii(lean_object*);
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
LEAN_EXPORT lean_object* l_String_dropSuffix___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropSuffix(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropSuffix___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v___x_5_, 3);
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
lean_dec_ref_known(v___x_12_, 3);
v___x_14_ = lean_string_utf8_extract_fast(v_s_8_, v___x_13_, v___x_11_);
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
lean_dec_ref_known(v___x_19_, 3);
v___x_21_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_21_, 0, v_s_15_);
lean_ctor_set(v___x_21_, 1, v___x_17_);
lean_ctor_set(v___x_21_, 2, v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropRight(lean_object* v_s_22_, lean_object* v_n_23_){
_start:
{
lean_object* v_str_24_; lean_object* v_startInclusive_25_; lean_object* v_endExclusive_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_36_; 
v_str_24_ = lean_ctor_get(v_s_22_, 0);
lean_inc_ref(v_str_24_);
v_startInclusive_25_ = lean_ctor_get(v_s_22_, 1);
lean_inc(v_startInclusive_25_);
v_endExclusive_26_ = lean_ctor_get(v_s_22_, 2);
v___x_27_ = lean_nat_sub(v_endExclusive_26_, v_startInclusive_25_);
v___x_28_ = l_String_Slice_Pos_prevn(v_s_22_, v___x_27_, v_n_23_);
v_isSharedCheck_36_ = !lean_is_exclusive(v_s_22_);
if (v_isSharedCheck_36_ == 0)
{
lean_object* v_unused_37_; lean_object* v_unused_38_; lean_object* v_unused_39_; 
v_unused_37_ = lean_ctor_get(v_s_22_, 2);
lean_dec(v_unused_37_);
v_unused_38_ = lean_ctor_get(v_s_22_, 1);
lean_dec(v_unused_38_);
v_unused_39_ = lean_ctor_get(v_s_22_, 0);
lean_dec(v_unused_39_);
v___x_30_ = v_s_22_;
v_isShared_31_ = v_isSharedCheck_36_;
goto v_resetjp_29_;
}
else
{
lean_dec(v_s_22_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_36_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v___x_32_; lean_object* v___x_34_; 
v___x_32_ = lean_nat_add(v_startInclusive_25_, v___x_28_);
lean_dec(v___x_28_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 2, v___x_32_);
v___x_34_ = v___x_30_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v_str_24_);
lean_ctor_set(v_reuseFailAlloc_35_, 1, v_startInclusive_25_);
lean_ctor_set(v_reuseFailAlloc_35_, 2, v___x_32_);
v___x_34_ = v_reuseFailAlloc_35_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
return v___x_34_;
}
}
}
}
LEAN_EXPORT lean_object* lean_string_dropright(lean_object* v_s_40_, lean_object* v_n_41_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_42_ = lean_unsigned_to_nat(0u);
v___x_43_ = lean_string_utf8_byte_size(v_s_40_);
lean_inc_ref(v_s_40_);
v___x_44_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_44_, 0, v_s_40_);
lean_ctor_set(v___x_44_, 1, v___x_42_);
lean_ctor_set(v___x_44_, 2, v___x_43_);
v___x_45_ = l_String_Slice_Pos_prevn(v___x_44_, v___x_43_, v_n_41_);
lean_dec_ref_known(v___x_44_, 3);
v___x_46_ = lean_string_utf8_extract_fast(v_s_40_, v___x_42_, v___x_45_);
lean_dec(v___x_45_);
lean_dec_ref(v_s_40_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_String_take(lean_object* v_s_47_, lean_object* v_n_48_){
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
v___x_52_ = l_String_Slice_Pos_nextn(v___x_51_, v___x_49_, v_n_48_);
lean_dec_ref_known(v___x_51_, 3);
v___x_53_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_53_, 0, v_s_47_);
lean_ctor_set(v___x_53_, 1, v___x_49_);
lean_ctor_set(v___x_53_, 2, v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_String_takeEnd(lean_object* v_s_54_, lean_object* v_n_55_){
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
v___x_59_ = l_String_Slice_Pos_prevn(v___x_58_, v___x_57_, v_n_55_);
lean_dec_ref_known(v___x_58_, 3);
v___x_60_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_60_, 0, v_s_54_);
lean_ctor_set(v___x_60_, 1, v___x_59_);
lean_ctor_set(v___x_60_, 2, v___x_57_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeRight(lean_object* v_s_61_, lean_object* v_n_62_){
_start:
{
lean_object* v_str_63_; lean_object* v_startInclusive_64_; lean_object* v_endExclusive_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_75_; 
v_str_63_ = lean_ctor_get(v_s_61_, 0);
lean_inc_ref(v_str_63_);
v_startInclusive_64_ = lean_ctor_get(v_s_61_, 1);
lean_inc(v_startInclusive_64_);
v_endExclusive_65_ = lean_ctor_get(v_s_61_, 2);
lean_inc(v_endExclusive_65_);
v___x_66_ = lean_nat_sub(v_endExclusive_65_, v_startInclusive_64_);
v___x_67_ = l_String_Slice_Pos_prevn(v_s_61_, v___x_66_, v_n_62_);
v_isSharedCheck_75_ = !lean_is_exclusive(v_s_61_);
if (v_isSharedCheck_75_ == 0)
{
lean_object* v_unused_76_; lean_object* v_unused_77_; lean_object* v_unused_78_; 
v_unused_76_ = lean_ctor_get(v_s_61_, 2);
lean_dec(v_unused_76_);
v_unused_77_ = lean_ctor_get(v_s_61_, 1);
lean_dec(v_unused_77_);
v_unused_78_ = lean_ctor_get(v_s_61_, 0);
lean_dec(v_unused_78_);
v___x_69_ = v_s_61_;
v_isShared_70_ = v_isSharedCheck_75_;
goto v_resetjp_68_;
}
else
{
lean_dec(v_s_61_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_75_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_71_; lean_object* v___x_73_; 
v___x_71_ = lean_nat_add(v_startInclusive_64_, v___x_67_);
lean_dec(v___x_67_);
lean_dec(v_startInclusive_64_);
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 1, v___x_71_);
v___x_73_ = v___x_69_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_str_63_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v___x_71_);
lean_ctor_set(v_reuseFailAlloc_74_, 2, v_endExclusive_65_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_takeWhile___redArg(lean_object* v_s_79_, lean_object* v_inst_80_){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_81_ = lean_unsigned_to_nat(0u);
v___x_82_ = lean_string_utf8_byte_size(v_s_79_);
lean_inc_ref(v_s_79_);
v___x_83_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_83_, 0, v_s_79_);
lean_ctor_set(v___x_83_, 1, v___x_81_);
lean_ctor_set(v___x_83_, 2, v___x_82_);
v___x_84_ = l_String_Slice_Pos_skipWhile___redArg(v___x_83_, v___x_81_, v_inst_80_);
lean_dec_ref_known(v___x_83_, 3);
v___x_85_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_85_, 0, v_s_79_);
lean_ctor_set(v___x_85_, 1, v___x_81_);
lean_ctor_set(v___x_85_, 2, v___x_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_String_takeWhile(lean_object* v_00_u03c1_86_, lean_object* v_s_87_, lean_object* v_pat_88_, lean_object* v_inst_89_){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_90_ = lean_unsigned_to_nat(0u);
v___x_91_ = lean_string_utf8_byte_size(v_s_87_);
lean_inc_ref(v_s_87_);
v___x_92_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_92_, 0, v_s_87_);
lean_ctor_set(v___x_92_, 1, v___x_90_);
lean_ctor_set(v___x_92_, 2, v___x_91_);
v___x_93_ = l_String_Slice_Pos_skipWhile___redArg(v___x_92_, v___x_90_, v_inst_89_);
lean_dec_ref_known(v___x_92_, 3);
v___x_94_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_94_, 0, v_s_87_);
lean_ctor_set(v___x_94_, 1, v___x_90_);
lean_ctor_set(v___x_94_, 2, v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_String_takeWhile___boxed(lean_object* v_00_u03c1_95_, lean_object* v_s_96_, lean_object* v_pat_97_, lean_object* v_inst_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_String_takeWhile(v_00_u03c1_95_, v_s_96_, v_pat_97_, v_inst_98_);
lean_dec(v_pat_97_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_String_dropWhile___redArg(lean_object* v_s_100_, lean_object* v_inst_101_){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_102_ = lean_unsigned_to_nat(0u);
v___x_103_ = lean_string_utf8_byte_size(v_s_100_);
lean_inc_ref(v_s_100_);
v___x_104_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_104_, 0, v_s_100_);
lean_ctor_set(v___x_104_, 1, v___x_102_);
lean_ctor_set(v___x_104_, 2, v___x_103_);
v___x_105_ = l_String_Slice_Pos_skipWhile___redArg(v___x_104_, v___x_102_, v_inst_101_);
lean_dec_ref_known(v___x_104_, 3);
v___x_106_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_106_, 0, v_s_100_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
lean_ctor_set(v___x_106_, 2, v___x_103_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_String_dropWhile(lean_object* v_00_u03c1_107_, lean_object* v_s_108_, lean_object* v_pat_109_, lean_object* v_inst_110_){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_111_ = lean_unsigned_to_nat(0u);
v___x_112_ = lean_string_utf8_byte_size(v_s_108_);
lean_inc_ref(v_s_108_);
v___x_113_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_113_, 0, v_s_108_);
lean_ctor_set(v___x_113_, 1, v___x_111_);
lean_ctor_set(v___x_113_, 2, v___x_112_);
v___x_114_ = l_String_Slice_Pos_skipWhile___redArg(v___x_113_, v___x_111_, v_inst_110_);
lean_dec_ref_known(v___x_113_, 3);
v___x_115_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_115_, 0, v_s_108_);
lean_ctor_set(v___x_115_, 1, v___x_114_);
lean_ctor_set(v___x_115_, 2, v___x_112_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_String_dropWhile___boxed(lean_object* v_00_u03c1_116_, lean_object* v_s_117_, lean_object* v_pat_118_, lean_object* v_inst_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_String_dropWhile(v_00_u03c1_116_, v_s_117_, v_pat_118_, v_inst_119_);
lean_dec(v_pat_118_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_String_takeEndWhile___redArg(lean_object* v_s_121_, lean_object* v_inst_122_){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_123_ = lean_unsigned_to_nat(0u);
v___x_124_ = lean_string_utf8_byte_size(v_s_121_);
lean_inc_ref(v_s_121_);
v___x_125_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_125_, 0, v_s_121_);
lean_ctor_set(v___x_125_, 1, v___x_123_);
lean_ctor_set(v___x_125_, 2, v___x_124_);
v___x_126_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_125_, v___x_124_, v_inst_122_);
lean_dec_ref_known(v___x_125_, 3);
v___x_127_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_127_, 0, v_s_121_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
lean_ctor_set(v___x_127_, 2, v___x_124_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_String_takeEndWhile(lean_object* v_00_u03c1_128_, lean_object* v_s_129_, lean_object* v_pat_130_, lean_object* v_inst_131_){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_132_ = lean_unsigned_to_nat(0u);
v___x_133_ = lean_string_utf8_byte_size(v_s_129_);
lean_inc_ref(v_s_129_);
v___x_134_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_134_, 0, v_s_129_);
lean_ctor_set(v___x_134_, 1, v___x_132_);
lean_ctor_set(v___x_134_, 2, v___x_133_);
v___x_135_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_134_, v___x_133_, v_inst_131_);
lean_dec_ref_known(v___x_134_, 3);
v___x_136_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_136_, 0, v_s_129_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
lean_ctor_set(v___x_136_, 2, v___x_133_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_String_takeEndWhile___boxed(lean_object* v_00_u03c1_137_, lean_object* v_s_138_, lean_object* v_pat_139_, lean_object* v_inst_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_String_takeEndWhile(v_00_u03c1_137_, v_s_138_, v_pat_139_, v_inst_140_);
lean_dec(v_pat_139_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_String_dropEndWhile___redArg(lean_object* v_s_142_, lean_object* v_inst_143_){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = lean_string_utf8_byte_size(v_s_142_);
lean_inc_ref(v_s_142_);
v___x_146_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_146_, 0, v_s_142_);
lean_ctor_set(v___x_146_, 1, v___x_144_);
lean_ctor_set(v___x_146_, 2, v___x_145_);
v___x_147_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_146_, v___x_145_, v_inst_143_);
lean_dec_ref_known(v___x_146_, 3);
v___x_148_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_148_, 0, v_s_142_);
lean_ctor_set(v___x_148_, 1, v___x_144_);
lean_ctor_set(v___x_148_, 2, v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_String_dropEndWhile(lean_object* v_00_u03c1_149_, lean_object* v_s_150_, lean_object* v_pat_151_, lean_object* v_inst_152_){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_153_ = lean_unsigned_to_nat(0u);
v___x_154_ = lean_string_utf8_byte_size(v_s_150_);
lean_inc_ref(v_s_150_);
v___x_155_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_155_, 0, v_s_150_);
lean_ctor_set(v___x_155_, 1, v___x_153_);
lean_ctor_set(v___x_155_, 2, v___x_154_);
v___x_156_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_155_, v___x_154_, v_inst_152_);
lean_dec_ref_known(v___x_155_, 3);
v___x_157_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_157_, 0, v_s_150_);
lean_ctor_set(v___x_157_, 1, v___x_153_);
lean_ctor_set(v___x_157_, 2, v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_String_dropEndWhile___boxed(lean_object* v_00_u03c1_158_, lean_object* v_s_159_, lean_object* v_pat_160_, lean_object* v_inst_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_String_dropEndWhile(v_00_u03c1_158_, v_s_159_, v_pat_160_, v_inst_161_);
lean_dec(v_pat_160_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_String_skipPrefix_x3f___redArg(lean_object* v_s_163_, lean_object* v_inst_164_){
_start:
{
lean_object* v_skipPrefix_x3f_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_184_; 
v_skipPrefix_x3f_165_ = lean_ctor_get(v_inst_164_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v_inst_164_);
if (v_isSharedCheck_184_ == 0)
{
lean_object* v_unused_185_; lean_object* v_unused_186_; 
v_unused_185_ = lean_ctor_get(v_inst_164_, 2);
lean_dec(v_unused_185_);
v_unused_186_ = lean_ctor_get(v_inst_164_, 1);
lean_dec(v_unused_186_);
v___x_167_ = v_inst_164_;
v_isShared_168_ = v_isSharedCheck_184_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_skipPrefix_x3f_165_);
lean_dec(v_inst_164_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_184_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_172_; 
v___x_169_ = lean_string_utf8_byte_size(v_s_163_);
v___x_170_ = lean_unsigned_to_nat(0u);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 2, v___x_169_);
lean_ctor_set(v___x_167_, 1, v___x_170_);
lean_ctor_set(v___x_167_, 0, v_s_163_);
v___x_172_ = v___x_167_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_s_163_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v___x_170_);
lean_ctor_set(v_reuseFailAlloc_183_, 2, v___x_169_);
v___x_172_ = v_reuseFailAlloc_183_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
lean_object* v___x_173_; 
v___x_173_ = lean_apply_1(v_skipPrefix_x3f_165_, v___x_172_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v___x_174_; 
v___x_174_ = lean_box(0);
return v___x_174_;
}
else
{
lean_object* v_val_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_182_; 
v_val_175_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_182_ == 0)
{
v___x_177_ = v___x_173_;
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_val_175_);
lean_dec(v___x_173_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_180_; 
if (v_isShared_178_ == 0)
{
v___x_180_ = v___x_177_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_val_175_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_skipPrefix_x3f(lean_object* v_00_u03c1_187_, lean_object* v_s_188_, lean_object* v_pat_189_, lean_object* v_inst_190_){
_start:
{
lean_object* v_skipPrefix_x3f_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_210_; 
v_skipPrefix_x3f_191_ = lean_ctor_get(v_inst_190_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v_inst_190_);
if (v_isSharedCheck_210_ == 0)
{
lean_object* v_unused_211_; lean_object* v_unused_212_; 
v_unused_211_ = lean_ctor_get(v_inst_190_, 2);
lean_dec(v_unused_211_);
v_unused_212_ = lean_ctor_get(v_inst_190_, 1);
lean_dec(v_unused_212_);
v___x_193_ = v_inst_190_;
v_isShared_194_ = v_isSharedCheck_210_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_skipPrefix_x3f_191_);
lean_dec(v_inst_190_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_210_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_198_; 
v___x_195_ = lean_string_utf8_byte_size(v_s_188_);
v___x_196_ = lean_unsigned_to_nat(0u);
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 2, v___x_195_);
lean_ctor_set(v___x_193_, 1, v___x_196_);
lean_ctor_set(v___x_193_, 0, v_s_188_);
v___x_198_ = v___x_193_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_s_188_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v___x_196_);
lean_ctor_set(v_reuseFailAlloc_209_, 2, v___x_195_);
v___x_198_ = v_reuseFailAlloc_209_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
lean_object* v___x_199_; 
v___x_199_ = lean_apply_1(v_skipPrefix_x3f_191_, v___x_198_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v___x_200_; 
v___x_200_ = lean_box(0);
return v___x_200_;
}
else
{
lean_object* v_val_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
v_val_201_ = lean_ctor_get(v___x_199_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_208_ == 0)
{
v___x_203_ = v___x_199_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_val_201_);
lean_dec(v___x_199_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_val_201_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_skipPrefix_x3f___boxed(lean_object* v_00_u03c1_213_, lean_object* v_s_214_, lean_object* v_pat_215_, lean_object* v_inst_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_String_skipPrefix_x3f(v_00_u03c1_213_, v_s_214_, v_pat_215_, v_inst_216_);
lean_dec(v_pat_215_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_String_skipPrefixWhile___redArg(lean_object* v_s_218_, lean_object* v_inst_219_){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_220_ = lean_unsigned_to_nat(0u);
v___x_221_ = lean_string_utf8_byte_size(v_s_218_);
v___x_222_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_222_, 0, v_s_218_);
lean_ctor_set(v___x_222_, 1, v___x_220_);
lean_ctor_set(v___x_222_, 2, v___x_221_);
v___x_223_ = l_String_Slice_Pos_skipWhile___redArg(v___x_222_, v___x_220_, v_inst_219_);
lean_dec_ref_known(v___x_222_, 3);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_String_skipPrefixWhile(lean_object* v_00_u03c1_224_, lean_object* v_s_225_, lean_object* v_pat_226_, lean_object* v_inst_227_){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_228_ = lean_unsigned_to_nat(0u);
v___x_229_ = lean_string_utf8_byte_size(v_s_225_);
v___x_230_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_230_, 0, v_s_225_);
lean_ctor_set(v___x_230_, 1, v___x_228_);
lean_ctor_set(v___x_230_, 2, v___x_229_);
v___x_231_ = l_String_Slice_Pos_skipWhile___redArg(v___x_230_, v___x_228_, v_inst_227_);
lean_dec_ref_known(v___x_230_, 3);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_String_skipPrefixWhile___boxed(lean_object* v_00_u03c1_232_, lean_object* v_s_233_, lean_object* v_pat_234_, lean_object* v_inst_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_String_skipPrefixWhile(v_00_u03c1_232_, v_s_233_, v_pat_234_, v_inst_235_);
lean_dec(v_pat_234_);
return v_res_236_;
}
}
LEAN_EXPORT uint8_t l_String_all___redArg(lean_object* v_s_237_, lean_object* v_inst_238_){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_239_ = lean_unsigned_to_nat(0u);
v___x_240_ = lean_string_utf8_byte_size(v_s_237_);
v___x_241_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_241_, 0, v_s_237_);
lean_ctor_set(v___x_241_, 1, v___x_239_);
lean_ctor_set(v___x_241_, 2, v___x_240_);
v___x_242_ = l_String_Slice_Pos_skipWhile___redArg(v___x_241_, v___x_239_, v_inst_238_);
lean_dec_ref_known(v___x_241_, 3);
v___x_243_ = lean_nat_dec_eq(v___x_242_, v___x_240_);
lean_dec(v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_String_all___redArg___boxed(lean_object* v_s_244_, lean_object* v_inst_245_){
_start:
{
uint8_t v_res_246_; lean_object* v_r_247_; 
v_res_246_ = l_String_all___redArg(v_s_244_, v_inst_245_);
v_r_247_ = lean_box(v_res_246_);
return v_r_247_;
}
}
LEAN_EXPORT uint8_t l_String_all(lean_object* v_00_u03c1_248_, lean_object* v_s_249_, lean_object* v_pat_250_, lean_object* v_inst_251_){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; 
v___x_252_ = lean_unsigned_to_nat(0u);
v___x_253_ = lean_string_utf8_byte_size(v_s_249_);
v___x_254_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_254_, 0, v_s_249_);
lean_ctor_set(v___x_254_, 1, v___x_252_);
lean_ctor_set(v___x_254_, 2, v___x_253_);
v___x_255_ = l_String_Slice_Pos_skipWhile___redArg(v___x_254_, v___x_252_, v_inst_251_);
lean_dec_ref_known(v___x_254_, 3);
v___x_256_ = lean_nat_dec_eq(v___x_255_, v___x_253_);
lean_dec(v___x_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_String_all___boxed(lean_object* v_00_u03c1_257_, lean_object* v_s_258_, lean_object* v_pat_259_, lean_object* v_inst_260_){
_start:
{
uint8_t v_res_261_; lean_object* v_r_262_; 
v_res_261_ = l_String_all(v_00_u03c1_257_, v_s_258_, v_pat_259_, v_inst_260_);
lean_dec(v_pat_259_);
v_r_262_ = lean_box(v_res_261_);
return v_r_262_;
}
}
LEAN_EXPORT uint8_t l_String_revAll___redArg(lean_object* v_s_263_, lean_object* v_inst_264_){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_265_ = lean_unsigned_to_nat(0u);
v___x_266_ = lean_string_utf8_byte_size(v_s_263_);
v___x_267_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_267_, 0, v_s_263_);
lean_ctor_set(v___x_267_, 1, v___x_265_);
lean_ctor_set(v___x_267_, 2, v___x_266_);
v___x_268_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_267_, v___x_266_, v_inst_264_);
lean_dec_ref_known(v___x_267_, 3);
v___x_269_ = lean_nat_dec_eq(v___x_268_, v___x_265_);
lean_dec(v___x_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_String_revAll___redArg___boxed(lean_object* v_s_270_, lean_object* v_inst_271_){
_start:
{
uint8_t v_res_272_; lean_object* v_r_273_; 
v_res_272_ = l_String_revAll___redArg(v_s_270_, v_inst_271_);
v_r_273_ = lean_box(v_res_272_);
return v_r_273_;
}
}
LEAN_EXPORT uint8_t l_String_revAll(lean_object* v_00_u03c1_274_, lean_object* v_s_275_, lean_object* v_pat_276_, lean_object* v_inst_277_){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_278_ = lean_unsigned_to_nat(0u);
v___x_279_ = lean_string_utf8_byte_size(v_s_275_);
v___x_280_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_280_, 0, v_s_275_);
lean_ctor_set(v___x_280_, 1, v___x_278_);
lean_ctor_set(v___x_280_, 2, v___x_279_);
v___x_281_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_280_, v___x_279_, v_inst_277_);
lean_dec_ref_known(v___x_280_, 3);
v___x_282_ = lean_nat_dec_eq(v___x_281_, v___x_278_);
lean_dec(v___x_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_String_revAll___boxed(lean_object* v_00_u03c1_283_, lean_object* v_s_284_, lean_object* v_pat_285_, lean_object* v_inst_286_){
_start:
{
uint8_t v_res_287_; lean_object* v_r_288_; 
v_res_287_ = l_String_revAll(v_00_u03c1_283_, v_s_284_, v_pat_285_, v_inst_286_);
lean_dec(v_pat_285_);
v_r_288_ = lean_box(v_res_287_);
return v_r_288_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_skip_x3f___redArg(lean_object* v_s_289_, lean_object* v_pos_290_, lean_object* v_inst_291_){
_start:
{
lean_object* v_skipPrefix_x3f_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_311_; 
v_skipPrefix_x3f_292_ = lean_ctor_get(v_inst_291_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v_inst_291_);
if (v_isSharedCheck_311_ == 0)
{
lean_object* v_unused_312_; lean_object* v_unused_313_; 
v_unused_312_ = lean_ctor_get(v_inst_291_, 2);
lean_dec(v_unused_312_);
v_unused_313_ = lean_ctor_get(v_inst_291_, 1);
lean_dec(v_unused_313_);
v___x_294_ = v_inst_291_;
v_isShared_295_ = v_isSharedCheck_311_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_skipPrefix_x3f_292_);
lean_dec(v_inst_291_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_311_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_296_; lean_object* v___x_298_; 
v___x_296_ = lean_string_utf8_byte_size(v_s_289_);
lean_inc(v_pos_290_);
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 2, v___x_296_);
lean_ctor_set(v___x_294_, 1, v_pos_290_);
lean_ctor_set(v___x_294_, 0, v_s_289_);
v___x_298_ = v___x_294_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_s_289_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v_pos_290_);
lean_ctor_set(v_reuseFailAlloc_310_, 2, v___x_296_);
v___x_298_ = v_reuseFailAlloc_310_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
lean_object* v___x_299_; 
v___x_299_ = lean_apply_1(v_skipPrefix_x3f_292_, v___x_298_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v___x_300_; 
lean_dec(v_pos_290_);
v___x_300_ = lean_box(0);
return v___x_300_;
}
else
{
lean_object* v_val_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_309_; 
v_val_301_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_309_ == 0)
{
v___x_303_ = v___x_299_;
v_isShared_304_ = v_isSharedCheck_309_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_val_301_);
lean_dec(v___x_299_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_309_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; lean_object* v___x_307_; 
v___x_305_ = lean_nat_add(v_pos_290_, v_val_301_);
lean_dec(v_val_301_);
lean_dec(v_pos_290_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 0, v___x_305_);
v___x_307_ = v___x_303_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_305_);
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
}
LEAN_EXPORT lean_object* l_String_Pos_skip_x3f(lean_object* v_00_u03c1_314_, lean_object* v_s_315_, lean_object* v_pos_316_, lean_object* v_pat_317_, lean_object* v_inst_318_){
_start:
{
lean_object* v_skipPrefix_x3f_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_338_; 
v_skipPrefix_x3f_319_ = lean_ctor_get(v_inst_318_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v_inst_318_);
if (v_isSharedCheck_338_ == 0)
{
lean_object* v_unused_339_; lean_object* v_unused_340_; 
v_unused_339_ = lean_ctor_get(v_inst_318_, 2);
lean_dec(v_unused_339_);
v_unused_340_ = lean_ctor_get(v_inst_318_, 1);
lean_dec(v_unused_340_);
v___x_321_ = v_inst_318_;
v_isShared_322_ = v_isSharedCheck_338_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_skipPrefix_x3f_319_);
lean_dec(v_inst_318_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_338_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_323_ = lean_string_utf8_byte_size(v_s_315_);
lean_inc(v_pos_316_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 2, v___x_323_);
lean_ctor_set(v___x_321_, 1, v_pos_316_);
lean_ctor_set(v___x_321_, 0, v_s_315_);
v___x_325_ = v___x_321_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_s_315_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_pos_316_);
lean_ctor_set(v_reuseFailAlloc_337_, 2, v___x_323_);
v___x_325_ = v_reuseFailAlloc_337_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_326_; 
v___x_326_ = lean_apply_1(v_skipPrefix_x3f_319_, v___x_325_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v___x_327_; 
lean_dec(v_pos_316_);
v___x_327_ = lean_box(0);
return v___x_327_;
}
else
{
lean_object* v_val_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_336_; 
v_val_328_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_336_ == 0)
{
v___x_330_ = v___x_326_;
v_isShared_331_ = v_isSharedCheck_336_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_val_328_);
lean_dec(v___x_326_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_336_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_332_; lean_object* v___x_334_; 
v___x_332_ = lean_nat_add(v_pos_316_, v_val_328_);
lean_dec(v_val_328_);
lean_dec(v_pos_316_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 0, v___x_332_);
v___x_334_ = v___x_330_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_332_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_skip_x3f___boxed(lean_object* v_00_u03c1_341_, lean_object* v_s_342_, lean_object* v_pos_343_, lean_object* v_pat_344_, lean_object* v_inst_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_String_Pos_skip_x3f(v_00_u03c1_341_, v_s_342_, v_pos_343_, v_pat_344_, v_inst_345_);
lean_dec(v_pat_344_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_skipWhile___redArg(lean_object* v_s_347_, lean_object* v_pos_348_, lean_object* v_inst_349_){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_350_ = lean_unsigned_to_nat(0u);
v___x_351_ = lean_string_utf8_byte_size(v_s_347_);
v___x_352_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_352_, 0, v_s_347_);
lean_ctor_set(v___x_352_, 1, v___x_350_);
lean_ctor_set(v___x_352_, 2, v___x_351_);
v___x_353_ = l_String_Slice_Pos_skipWhile___redArg(v___x_352_, v_pos_348_, v_inst_349_);
lean_dec_ref_known(v___x_352_, 3);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_skipWhile(lean_object* v_00_u03c1_354_, lean_object* v_s_355_, lean_object* v_pos_356_, lean_object* v_pat_357_, lean_object* v_inst_358_){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_359_ = lean_unsigned_to_nat(0u);
v___x_360_ = lean_string_utf8_byte_size(v_s_355_);
v___x_361_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_361_, 0, v_s_355_);
lean_ctor_set(v___x_361_, 1, v___x_359_);
lean_ctor_set(v___x_361_, 2, v___x_360_);
v___x_362_ = l_String_Slice_Pos_skipWhile___redArg(v___x_361_, v_pos_356_, v_inst_358_);
lean_dec_ref_known(v___x_361_, 3);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_skipWhile___boxed(lean_object* v_00_u03c1_363_, lean_object* v_s_364_, lean_object* v_pos_365_, lean_object* v_pat_366_, lean_object* v_inst_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_String_Pos_skipWhile(v_00_u03c1_363_, v_s_364_, v_pos_365_, v_pat_366_, v_inst_367_);
lean_dec(v_pat_366_);
return v_res_368_;
}
}
LEAN_EXPORT uint8_t l_String_startsWith___redArg(lean_object* v_s_369_, lean_object* v_inst_370_){
_start:
{
lean_object* v_startsWith_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_382_; 
v_startsWith_371_ = lean_ctor_get(v_inst_370_, 2);
v_isSharedCheck_382_ = !lean_is_exclusive(v_inst_370_);
if (v_isSharedCheck_382_ == 0)
{
lean_object* v_unused_383_; lean_object* v_unused_384_; 
v_unused_383_ = lean_ctor_get(v_inst_370_, 1);
lean_dec(v_unused_383_);
v_unused_384_ = lean_ctor_get(v_inst_370_, 0);
lean_dec(v_unused_384_);
v___x_373_ = v_inst_370_;
v_isShared_374_ = v_isSharedCheck_382_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_startsWith_371_);
lean_dec(v_inst_370_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_382_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_378_; 
v___x_375_ = lean_string_utf8_byte_size(v_s_369_);
v___x_376_ = lean_unsigned_to_nat(0u);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 2, v___x_375_);
lean_ctor_set(v___x_373_, 1, v___x_376_);
lean_ctor_set(v___x_373_, 0, v_s_369_);
v___x_378_ = v___x_373_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_s_369_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v___x_376_);
lean_ctor_set(v_reuseFailAlloc_381_, 2, v___x_375_);
v___x_378_ = v_reuseFailAlloc_381_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_379_ = lean_apply_1(v_startsWith_371_, v___x_378_);
v___x_380_ = lean_unbox(v___x_379_);
return v___x_380_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_startsWith___redArg___boxed(lean_object* v_s_385_, lean_object* v_inst_386_){
_start:
{
uint8_t v_res_387_; lean_object* v_r_388_; 
v_res_387_ = l_String_startsWith___redArg(v_s_385_, v_inst_386_);
v_r_388_ = lean_box(v_res_387_);
return v_r_388_;
}
}
LEAN_EXPORT uint8_t l_String_startsWith(lean_object* v_00_u03c1_389_, lean_object* v_s_390_, lean_object* v_pat_391_, lean_object* v_inst_392_){
_start:
{
lean_object* v_startsWith_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_404_; 
v_startsWith_393_ = lean_ctor_get(v_inst_392_, 2);
v_isSharedCheck_404_ = !lean_is_exclusive(v_inst_392_);
if (v_isSharedCheck_404_ == 0)
{
lean_object* v_unused_405_; lean_object* v_unused_406_; 
v_unused_405_ = lean_ctor_get(v_inst_392_, 1);
lean_dec(v_unused_405_);
v_unused_406_ = lean_ctor_get(v_inst_392_, 0);
lean_dec(v_unused_406_);
v___x_395_ = v_inst_392_;
v_isShared_396_ = v_isSharedCheck_404_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_startsWith_393_);
lean_dec(v_inst_392_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_404_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_400_; 
v___x_397_ = lean_string_utf8_byte_size(v_s_390_);
v___x_398_ = lean_unsigned_to_nat(0u);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 2, v___x_397_);
lean_ctor_set(v___x_395_, 1, v___x_398_);
lean_ctor_set(v___x_395_, 0, v_s_390_);
v___x_400_ = v___x_395_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_s_390_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v___x_398_);
lean_ctor_set(v_reuseFailAlloc_403_, 2, v___x_397_);
v___x_400_ = v_reuseFailAlloc_403_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_401_ = lean_apply_1(v_startsWith_393_, v___x_400_);
v___x_402_ = lean_unbox(v___x_401_);
return v___x_402_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_startsWith___boxed(lean_object* v_00_u03c1_407_, lean_object* v_s_408_, lean_object* v_pat_409_, lean_object* v_inst_410_){
_start:
{
uint8_t v_res_411_; lean_object* v_r_412_; 
v_res_411_ = l_String_startsWith(v_00_u03c1_407_, v_s_408_, v_pat_409_, v_inst_410_);
lean_dec(v_pat_409_);
v_r_412_ = lean_box(v_res_411_);
return v_r_412_;
}
}
LEAN_EXPORT uint8_t l_String_isPrefixOf(lean_object* v_p_413_, lean_object* v_s_414_){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_415_ = lean_string_utf8_byte_size(v_s_414_);
v___x_416_ = lean_string_utf8_byte_size(v_p_413_);
v___x_417_ = lean_nat_dec_le(v___x_416_, v___x_415_);
if (v___x_417_ == 0)
{
return v___x_417_;
}
else
{
lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_418_ = lean_unsigned_to_nat(0u);
v___x_419_ = lean_string_memcmp(v_s_414_, v_p_413_, v___x_418_, v___x_418_, v___x_416_);
return v___x_419_;
}
}
}
LEAN_EXPORT lean_object* l_String_isPrefixOf___boxed(lean_object* v_p_420_, lean_object* v_s_421_){
_start:
{
uint8_t v_res_422_; lean_object* v_r_423_; 
v_res_422_ = l_String_isPrefixOf(v_p_420_, v_s_421_);
lean_dec_ref(v_s_421_);
lean_dec_ref(v_p_420_);
v_r_423_ = lean_box(v_res_422_);
return v_r_423_;
}
}
LEAN_EXPORT uint8_t lean_string_isprefixof(lean_object* v_p_424_, lean_object* v_s_425_){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_426_ = lean_string_utf8_byte_size(v_s_425_);
v___x_427_ = lean_string_utf8_byte_size(v_p_424_);
v___x_428_ = lean_nat_dec_le(v___x_427_, v___x_426_);
if (v___x_428_ == 0)
{
lean_dec_ref(v_s_425_);
lean_dec_ref(v_p_424_);
return v___x_428_;
}
else
{
lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_429_ = lean_unsigned_to_nat(0u);
v___x_430_ = lean_string_memcmp(v_s_425_, v_p_424_, v___x_429_, v___x_429_, v___x_427_);
lean_dec_ref(v_p_424_);
lean_dec_ref(v_s_425_);
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l_String_Internal_isPrefixOfImpl___boxed(lean_object* v_p_431_, lean_object* v_s_432_){
_start:
{
uint8_t v_res_433_; lean_object* v_r_434_; 
v_res_433_ = lean_string_isprefixof(v_p_431_, v_s_432_);
v_r_434_ = lean_box(v_res_433_);
return v_r_434_;
}
}
LEAN_EXPORT uint8_t l_String_endsWith___redArg(lean_object* v_s_435_, lean_object* v_inst_436_){
_start:
{
lean_object* v_endsWith_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_448_; 
v_endsWith_437_ = lean_ctor_get(v_inst_436_, 2);
v_isSharedCheck_448_ = !lean_is_exclusive(v_inst_436_);
if (v_isSharedCheck_448_ == 0)
{
lean_object* v_unused_449_; lean_object* v_unused_450_; 
v_unused_449_ = lean_ctor_get(v_inst_436_, 1);
lean_dec(v_unused_449_);
v_unused_450_ = lean_ctor_get(v_inst_436_, 0);
lean_dec(v_unused_450_);
v___x_439_ = v_inst_436_;
v_isShared_440_ = v_isSharedCheck_448_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_endsWith_437_);
lean_dec(v_inst_436_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_448_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_441_ = lean_string_utf8_byte_size(v_s_435_);
v___x_442_ = lean_unsigned_to_nat(0u);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 2, v___x_441_);
lean_ctor_set(v___x_439_, 1, v___x_442_);
lean_ctor_set(v___x_439_, 0, v_s_435_);
v___x_444_ = v___x_439_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_s_435_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_447_, 2, v___x_441_);
v___x_444_ = v_reuseFailAlloc_447_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_445_ = lean_apply_1(v_endsWith_437_, v___x_444_);
v___x_446_ = lean_unbox(v___x_445_);
return v___x_446_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_endsWith___redArg___boxed(lean_object* v_s_451_, lean_object* v_inst_452_){
_start:
{
uint8_t v_res_453_; lean_object* v_r_454_; 
v_res_453_ = l_String_endsWith___redArg(v_s_451_, v_inst_452_);
v_r_454_ = lean_box(v_res_453_);
return v_r_454_;
}
}
LEAN_EXPORT uint8_t l_String_endsWith(lean_object* v_00_u03c1_455_, lean_object* v_s_456_, lean_object* v_pat_457_, lean_object* v_inst_458_){
_start:
{
lean_object* v_endsWith_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_470_; 
v_endsWith_459_ = lean_ctor_get(v_inst_458_, 2);
v_isSharedCheck_470_ = !lean_is_exclusive(v_inst_458_);
if (v_isSharedCheck_470_ == 0)
{
lean_object* v_unused_471_; lean_object* v_unused_472_; 
v_unused_471_ = lean_ctor_get(v_inst_458_, 1);
lean_dec(v_unused_471_);
v_unused_472_ = lean_ctor_get(v_inst_458_, 0);
lean_dec(v_unused_472_);
v___x_461_ = v_inst_458_;
v_isShared_462_ = v_isSharedCheck_470_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_endsWith_459_);
lean_dec(v_inst_458_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_470_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_463_ = lean_string_utf8_byte_size(v_s_456_);
v___x_464_ = lean_unsigned_to_nat(0u);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 2, v___x_463_);
lean_ctor_set(v___x_461_, 1, v___x_464_);
lean_ctor_set(v___x_461_, 0, v_s_456_);
v___x_466_ = v___x_461_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_s_456_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v___x_464_);
lean_ctor_set(v_reuseFailAlloc_469_, 2, v___x_463_);
v___x_466_ = v_reuseFailAlloc_469_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_467_ = lean_apply_1(v_endsWith_459_, v___x_466_);
v___x_468_ = lean_unbox(v___x_467_);
return v___x_468_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_endsWith___boxed(lean_object* v_00_u03c1_473_, lean_object* v_s_474_, lean_object* v_pat_475_, lean_object* v_inst_476_){
_start:
{
uint8_t v_res_477_; lean_object* v_r_478_; 
v_res_477_ = l_String_endsWith(v_00_u03c1_473_, v_s_474_, v_pat_475_, v_inst_476_);
lean_dec(v_pat_475_);
v_r_478_ = lean_box(v_res_477_);
return v_r_478_;
}
}
LEAN_EXPORT lean_object* l_String_skipSuffix_x3f___redArg(lean_object* v_s_479_, lean_object* v_inst_480_){
_start:
{
lean_object* v_skipSuffix_x3f_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_500_; 
v_skipSuffix_x3f_481_ = lean_ctor_get(v_inst_480_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v_inst_480_);
if (v_isSharedCheck_500_ == 0)
{
lean_object* v_unused_501_; lean_object* v_unused_502_; 
v_unused_501_ = lean_ctor_get(v_inst_480_, 2);
lean_dec(v_unused_501_);
v_unused_502_ = lean_ctor_get(v_inst_480_, 1);
lean_dec(v_unused_502_);
v___x_483_ = v_inst_480_;
v_isShared_484_ = v_isSharedCheck_500_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_skipSuffix_x3f_481_);
lean_dec(v_inst_480_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_500_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_488_; 
v___x_485_ = lean_string_utf8_byte_size(v_s_479_);
v___x_486_ = lean_unsigned_to_nat(0u);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 2, v___x_485_);
lean_ctor_set(v___x_483_, 1, v___x_486_);
lean_ctor_set(v___x_483_, 0, v_s_479_);
v___x_488_ = v___x_483_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_s_479_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_499_, 2, v___x_485_);
v___x_488_ = v_reuseFailAlloc_499_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_489_; 
v___x_489_ = lean_apply_1(v_skipSuffix_x3f_481_, v___x_488_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v___x_490_; 
v___x_490_ = lean_box(0);
return v___x_490_;
}
else
{
lean_object* v_val_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
v_val_491_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_489_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_val_491_);
lean_dec(v___x_489_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_val_491_);
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
}
LEAN_EXPORT lean_object* l_String_skipSuffix_x3f(lean_object* v_00_u03c1_503_, lean_object* v_s_504_, lean_object* v_pat_505_, lean_object* v_inst_506_){
_start:
{
lean_object* v_skipSuffix_x3f_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_526_; 
v_skipSuffix_x3f_507_ = lean_ctor_get(v_inst_506_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v_inst_506_);
if (v_isSharedCheck_526_ == 0)
{
lean_object* v_unused_527_; lean_object* v_unused_528_; 
v_unused_527_ = lean_ctor_get(v_inst_506_, 2);
lean_dec(v_unused_527_);
v_unused_528_ = lean_ctor_get(v_inst_506_, 1);
lean_dec(v_unused_528_);
v___x_509_ = v_inst_506_;
v_isShared_510_ = v_isSharedCheck_526_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_skipSuffix_x3f_507_);
lean_dec(v_inst_506_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_526_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_514_; 
v___x_511_ = lean_string_utf8_byte_size(v_s_504_);
v___x_512_ = lean_unsigned_to_nat(0u);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 2, v___x_511_);
lean_ctor_set(v___x_509_, 1, v___x_512_);
lean_ctor_set(v___x_509_, 0, v_s_504_);
v___x_514_ = v___x_509_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_s_504_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_525_, 2, v___x_511_);
v___x_514_ = v_reuseFailAlloc_525_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v___x_515_; 
v___x_515_ = lean_apply_1(v_skipSuffix_x3f_507_, v___x_514_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v___x_516_; 
v___x_516_ = lean_box(0);
return v___x_516_;
}
else
{
lean_object* v_val_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
v_val_517_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v___x_515_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_val_517_);
lean_dec(v___x_515_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_val_517_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_skipSuffix_x3f___boxed(lean_object* v_00_u03c1_529_, lean_object* v_s_530_, lean_object* v_pat_531_, lean_object* v_inst_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_String_skipSuffix_x3f(v_00_u03c1_529_, v_s_530_, v_pat_531_, v_inst_532_);
lean_dec(v_pat_531_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_String_skipSuffixWhile___redArg(lean_object* v_s_534_, lean_object* v_inst_535_){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_536_ = lean_unsigned_to_nat(0u);
v___x_537_ = lean_string_utf8_byte_size(v_s_534_);
v___x_538_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_538_, 0, v_s_534_);
lean_ctor_set(v___x_538_, 1, v___x_536_);
lean_ctor_set(v___x_538_, 2, v___x_537_);
v___x_539_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_538_, v___x_537_, v_inst_535_);
lean_dec_ref_known(v___x_538_, 3);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_String_skipSuffixWhile(lean_object* v_00_u03c1_540_, lean_object* v_s_541_, lean_object* v_pat_542_, lean_object* v_inst_543_){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = lean_string_utf8_byte_size(v_s_541_);
v___x_546_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_546_, 0, v_s_541_);
lean_ctor_set(v___x_546_, 1, v___x_544_);
lean_ctor_set(v___x_546_, 2, v___x_545_);
v___x_547_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_546_, v___x_545_, v_inst_543_);
lean_dec_ref_known(v___x_546_, 3);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_String_skipSuffixWhile___boxed(lean_object* v_00_u03c1_548_, lean_object* v_s_549_, lean_object* v_pat_550_, lean_object* v_inst_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_String_skipSuffixWhile(v_00_u03c1_548_, v_s_549_, v_pat_550_, v_inst_551_);
lean_dec(v_pat_550_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_revSkip_x3f___redArg(lean_object* v_s_553_, lean_object* v_pos_554_, lean_object* v_inst_555_){
_start:
{
lean_object* v_skipSuffix_x3f_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_574_; 
v_skipSuffix_x3f_556_ = lean_ctor_get(v_inst_555_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v_inst_555_);
if (v_isSharedCheck_574_ == 0)
{
lean_object* v_unused_575_; lean_object* v_unused_576_; 
v_unused_575_ = lean_ctor_get(v_inst_555_, 2);
lean_dec(v_unused_575_);
v_unused_576_ = lean_ctor_get(v_inst_555_, 1);
lean_dec(v_unused_576_);
v___x_558_ = v_inst_555_;
v_isShared_559_ = v_isSharedCheck_574_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_skipSuffix_x3f_556_);
lean_dec(v_inst_555_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_574_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; lean_object* v___x_562_; 
v___x_560_ = lean_unsigned_to_nat(0u);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 2, v_pos_554_);
lean_ctor_set(v___x_558_, 1, v___x_560_);
lean_ctor_set(v___x_558_, 0, v_s_553_);
v___x_562_ = v___x_558_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_s_553_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_573_, 2, v_pos_554_);
v___x_562_ = v_reuseFailAlloc_573_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_object* v___x_563_; 
v___x_563_ = lean_apply_1(v_skipSuffix_x3f_556_, v___x_562_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v___x_564_; 
v___x_564_ = lean_box(0);
return v___x_564_;
}
else
{
lean_object* v_val_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
v_val_565_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_563_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_val_565_);
lean_dec(v___x_563_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_val_565_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_revSkip_x3f(lean_object* v_00_u03c1_577_, lean_object* v_s_578_, lean_object* v_pos_579_, lean_object* v_pat_580_, lean_object* v_inst_581_){
_start:
{
lean_object* v_skipSuffix_x3f_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_600_; 
v_skipSuffix_x3f_582_ = lean_ctor_get(v_inst_581_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v_inst_581_);
if (v_isSharedCheck_600_ == 0)
{
lean_object* v_unused_601_; lean_object* v_unused_602_; 
v_unused_601_ = lean_ctor_get(v_inst_581_, 2);
lean_dec(v_unused_601_);
v_unused_602_ = lean_ctor_get(v_inst_581_, 1);
lean_dec(v_unused_602_);
v___x_584_ = v_inst_581_;
v_isShared_585_ = v_isSharedCheck_600_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_skipSuffix_x3f_582_);
lean_dec(v_inst_581_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_600_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_586_ = lean_unsigned_to_nat(0u);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 2, v_pos_579_);
lean_ctor_set(v___x_584_, 1, v___x_586_);
lean_ctor_set(v___x_584_, 0, v_s_578_);
v___x_588_ = v___x_584_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_s_578_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v___x_586_);
lean_ctor_set(v_reuseFailAlloc_599_, 2, v_pos_579_);
v___x_588_ = v_reuseFailAlloc_599_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
lean_object* v___x_589_; 
v___x_589_ = lean_apply_1(v_skipSuffix_x3f_582_, v___x_588_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v___x_590_; 
v___x_590_ = lean_box(0);
return v___x_590_;
}
else
{
lean_object* v_val_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_598_; 
v_val_591_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_598_ == 0)
{
v___x_593_ = v___x_589_;
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_val_591_);
lean_dec(v___x_589_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_val_591_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_revSkip_x3f___boxed(lean_object* v_00_u03c1_603_, lean_object* v_s_604_, lean_object* v_pos_605_, lean_object* v_pat_606_, lean_object* v_inst_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_String_Pos_revSkip_x3f(v_00_u03c1_603_, v_s_604_, v_pos_605_, v_pat_606_, v_inst_607_);
lean_dec(v_pat_606_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_revSkipWhile___redArg(lean_object* v_s_609_, lean_object* v_pos_610_, lean_object* v_inst_611_){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_612_ = lean_unsigned_to_nat(0u);
v___x_613_ = lean_string_utf8_byte_size(v_s_609_);
v___x_614_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_614_, 0, v_s_609_);
lean_ctor_set(v___x_614_, 1, v___x_612_);
lean_ctor_set(v___x_614_, 2, v___x_613_);
v___x_615_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_614_, v_pos_610_, v_inst_611_);
lean_dec_ref_known(v___x_614_, 3);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_revSkipWhile(lean_object* v_00_u03c1_616_, lean_object* v_s_617_, lean_object* v_pos_618_, lean_object* v_pat_619_, lean_object* v_inst_620_){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_621_ = lean_unsigned_to_nat(0u);
v___x_622_ = lean_string_utf8_byte_size(v_s_617_);
v___x_623_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_623_, 0, v_s_617_);
lean_ctor_set(v___x_623_, 1, v___x_621_);
lean_ctor_set(v___x_623_, 2, v___x_622_);
v___x_624_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_623_, v_pos_618_, v_inst_620_);
lean_dec_ref_known(v___x_623_, 3);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_revSkipWhile___boxed(lean_object* v_00_u03c1_625_, lean_object* v_s_626_, lean_object* v_pos_627_, lean_object* v_pat_628_, lean_object* v_inst_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_String_Pos_revSkipWhile(v_00_u03c1_625_, v_s_626_, v_pos_627_, v_pat_628_, v_inst_629_);
lean_dec(v_pat_628_);
return v_res_630_;
}
}
static lean_object* _init_l_String_trimAsciiEnd___closed__1(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = ((lean_object*)(l_String_trimAsciiEnd___closed__0));
v___x_633_ = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool(v___x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_String_trimAsciiEnd(lean_object* v_s_634_){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_635_ = lean_unsigned_to_nat(0u);
v___x_636_ = lean_string_utf8_byte_size(v_s_634_);
lean_inc_ref(v_s_634_);
v___x_637_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_637_, 0, v_s_634_);
lean_ctor_set(v___x_637_, 1, v___x_635_);
lean_ctor_set(v___x_637_, 2, v___x_636_);
v___x_638_ = lean_obj_once(&l_String_trimAsciiEnd___closed__1, &l_String_trimAsciiEnd___closed__1_once, _init_l_String_trimAsciiEnd___closed__1);
v___x_639_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_637_, v___x_636_, v___x_638_);
lean_dec_ref_known(v___x_637_, 3);
v___x_640_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_640_, 0, v_s_634_);
lean_ctor_set(v___x_640_, 1, v___x_635_);
lean_ctor_set(v___x_640_, 2, v___x_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimRight_spec__0(lean_object* v_s_641_, lean_object* v_pos_642_){
_start:
{
lean_object* v_str_643_; lean_object* v_startInclusive_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v_str_643_ = lean_ctor_get(v_s_641_, 0);
v_startInclusive_644_ = lean_ctor_get(v_s_641_, 1);
v___x_645_ = lean_nat_add(v_startInclusive_644_, v_pos_642_);
v___x_646_ = lean_nat_sub(v___x_645_, v_startInclusive_644_);
v___x_647_ = lean_unsigned_to_nat(0u);
v___x_648_ = lean_nat_dec_eq(v___x_646_, v___x_647_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; uint8_t v___y_657_; lean_object* v___x_658_; uint32_t v___x_659_; uint8_t v___y_661_; uint32_t v___x_666_; uint8_t v___x_667_; 
lean_inc(v_startInclusive_644_);
lean_inc_ref(v_str_643_);
v___x_649_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_649_, 0, v_str_643_);
lean_ctor_set(v___x_649_, 1, v_startInclusive_644_);
lean_ctor_set(v___x_649_, 2, v___x_645_);
v___x_650_ = lean_unsigned_to_nat(1u);
v___x_651_ = lean_nat_sub(v___x_646_, v___x_650_);
lean_dec(v___x_646_);
v___x_652_ = l_String_Slice_posLE(v___x_649_, v___x_651_);
lean_dec_ref_known(v___x_649_, 3);
v___x_658_ = lean_nat_add(v_startInclusive_644_, v___x_652_);
v___x_659_ = lean_string_utf8_get_fast(v_str_643_, v___x_658_);
lean_dec(v___x_658_);
v___x_666_ = 32;
v___x_667_ = lean_uint32_dec_eq(v___x_659_, v___x_666_);
if (v___x_667_ == 0)
{
uint32_t v___x_668_; uint8_t v___x_669_; 
v___x_668_ = 9;
v___x_669_ = lean_uint32_dec_eq(v___x_659_, v___x_668_);
v___y_661_ = v___x_669_;
goto v___jp_660_;
}
else
{
v___y_661_ = v___x_667_;
goto v___jp_660_;
}
v___jp_653_:
{
uint8_t v___x_654_; 
v___x_654_ = lean_nat_dec_lt(v___x_652_, v_pos_642_);
if (v___x_654_ == 0)
{
lean_dec(v___x_652_);
return v_pos_642_;
}
else
{
lean_dec(v_pos_642_);
v_pos_642_ = v___x_652_;
goto _start;
}
}
v___jp_656_:
{
if (v___y_657_ == 0)
{
lean_dec(v___x_652_);
return v_pos_642_;
}
else
{
goto v___jp_653_;
}
}
v___jp_660_:
{
if (v___y_661_ == 0)
{
uint32_t v___x_662_; uint8_t v___x_663_; 
v___x_662_ = 13;
v___x_663_ = lean_uint32_dec_eq(v___x_659_, v___x_662_);
if (v___x_663_ == 0)
{
uint32_t v___x_664_; uint8_t v___x_665_; 
v___x_664_ = 10;
v___x_665_ = lean_uint32_dec_eq(v___x_659_, v___x_664_);
v___y_657_ = v___x_665_;
goto v___jp_656_;
}
else
{
v___y_657_ = v___x_663_;
goto v___jp_656_;
}
}
else
{
goto v___jp_653_;
}
}
}
else
{
lean_dec(v___x_646_);
lean_dec(v___x_645_);
return v_pos_642_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimRight_spec__0___boxed(lean_object* v_s_670_, lean_object* v_pos_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimRight_spec__0(v_s_670_, v_pos_671_);
lean_dec_ref(v_s_670_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimRight(lean_object* v_s_673_){
_start:
{
lean_object* v_str_674_; lean_object* v_startInclusive_675_; lean_object* v_endExclusive_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_686_; 
v_str_674_ = lean_ctor_get(v_s_673_, 0);
lean_inc_ref(v_str_674_);
v_startInclusive_675_ = lean_ctor_get(v_s_673_, 1);
lean_inc(v_startInclusive_675_);
v_endExclusive_676_ = lean_ctor_get(v_s_673_, 2);
v___x_677_ = lean_nat_sub(v_endExclusive_676_, v_startInclusive_675_);
v___x_678_ = l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimRight_spec__0(v_s_673_, v___x_677_);
v_isSharedCheck_686_ = !lean_is_exclusive(v_s_673_);
if (v_isSharedCheck_686_ == 0)
{
lean_object* v_unused_687_; lean_object* v_unused_688_; lean_object* v_unused_689_; 
v_unused_687_ = lean_ctor_get(v_s_673_, 2);
lean_dec(v_unused_687_);
v_unused_688_ = lean_ctor_get(v_s_673_, 1);
lean_dec(v_unused_688_);
v_unused_689_ = lean_ctor_get(v_s_673_, 0);
lean_dec(v_unused_689_);
v___x_680_ = v_s_673_;
v_isShared_681_ = v_isSharedCheck_686_;
goto v_resetjp_679_;
}
else
{
lean_dec(v_s_673_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_686_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_682_; lean_object* v___x_684_; 
v___x_682_ = lean_nat_add(v_startInclusive_675_, v___x_678_);
lean_dec(v___x_678_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 2, v___x_682_);
v___x_684_ = v___x_680_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_str_674_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_startInclusive_675_);
lean_ctor_set(v_reuseFailAlloc_685_, 2, v___x_682_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
static lean_object* _init_l_String_trimAsciiStart___closed__0(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = ((lean_object*)(l_String_trimAsciiEnd___closed__0));
v___x_691_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_String_trimAsciiStart(lean_object* v_s_692_){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_693_ = lean_unsigned_to_nat(0u);
v___x_694_ = lean_string_utf8_byte_size(v_s_692_);
lean_inc_ref(v_s_692_);
v___x_695_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_695_, 0, v_s_692_);
lean_ctor_set(v___x_695_, 1, v___x_693_);
lean_ctor_set(v___x_695_, 2, v___x_694_);
v___x_696_ = lean_obj_once(&l_String_trimAsciiStart___closed__0, &l_String_trimAsciiStart___closed__0_once, _init_l_String_trimAsciiStart___closed__0);
v___x_697_ = l_String_Slice_Pos_skipWhile___redArg(v___x_695_, v___x_693_, v___x_696_);
lean_dec_ref_known(v___x_695_, 3);
v___x_698_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_698_, 0, v_s_692_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
lean_ctor_set(v___x_698_, 2, v___x_694_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00String_Slice_trimLeft_spec__0(lean_object* v_s_699_, lean_object* v_pos_700_){
_start:
{
lean_object* v_str_701_; lean_object* v_startInclusive_702_; lean_object* v_endExclusive_703_; lean_object* v___x_704_; uint8_t v___y_712_; lean_object* v___x_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
v_str_701_ = lean_ctor_get(v_s_699_, 0);
v_startInclusive_702_ = lean_ctor_get(v_s_699_, 1);
v_endExclusive_703_ = lean_ctor_get(v_s_699_, 2);
v___x_704_ = lean_nat_add(v_startInclusive_702_, v_pos_700_);
v___x_713_ = lean_unsigned_to_nat(0u);
v___x_714_ = lean_nat_sub(v_endExclusive_703_, v___x_704_);
v___x_715_ = lean_nat_dec_eq(v___x_713_, v___x_714_);
lean_dec(v___x_714_);
if (v___x_715_ == 0)
{
uint32_t v___x_716_; uint8_t v___y_718_; uint32_t v___x_723_; uint8_t v___x_724_; 
v___x_716_ = lean_string_utf8_get_fast(v_str_701_, v___x_704_);
v___x_723_ = 32;
v___x_724_ = lean_uint32_dec_eq(v___x_716_, v___x_723_);
if (v___x_724_ == 0)
{
uint32_t v___x_725_; uint8_t v___x_726_; 
v___x_725_ = 9;
v___x_726_ = lean_uint32_dec_eq(v___x_716_, v___x_725_);
v___y_718_ = v___x_726_;
goto v___jp_717_;
}
else
{
v___y_718_ = v___x_724_;
goto v___jp_717_;
}
v___jp_717_:
{
if (v___y_718_ == 0)
{
uint32_t v___x_719_; uint8_t v___x_720_; 
v___x_719_ = 13;
v___x_720_ = lean_uint32_dec_eq(v___x_716_, v___x_719_);
if (v___x_720_ == 0)
{
uint32_t v___x_721_; uint8_t v___x_722_; 
v___x_721_ = 10;
v___x_722_ = lean_uint32_dec_eq(v___x_716_, v___x_721_);
v___y_712_ = v___x_722_;
goto v___jp_711_;
}
else
{
v___y_712_ = v___x_720_;
goto v___jp_711_;
}
}
else
{
goto v___jp_705_;
}
}
}
else
{
lean_dec(v___x_704_);
return v_pos_700_;
}
v___jp_705_:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
v___x_706_ = lean_string_utf8_next_fast(v_str_701_, v___x_704_);
v___x_707_ = lean_nat_sub(v___x_706_, v___x_704_);
lean_dec(v___x_704_);
v___x_708_ = lean_nat_add(v_pos_700_, v___x_707_);
lean_dec(v___x_707_);
v___x_709_ = lean_nat_dec_lt(v_pos_700_, v___x_708_);
if (v___x_709_ == 0)
{
lean_dec(v___x_708_);
return v_pos_700_;
}
else
{
lean_dec(v_pos_700_);
v_pos_700_ = v___x_708_;
goto _start;
}
}
v___jp_711_:
{
if (v___y_712_ == 0)
{
lean_dec(v___x_704_);
return v_pos_700_;
}
else
{
goto v___jp_705_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00String_Slice_trimLeft_spec__0___boxed(lean_object* v_s_727_, lean_object* v_pos_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_String_Slice_Pos_skipWhile___at___00String_Slice_trimLeft_spec__0(v_s_727_, v_pos_728_);
lean_dec_ref(v_s_727_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimLeft(lean_object* v_s_730_){
_start:
{
lean_object* v_str_731_; lean_object* v_startInclusive_732_; lean_object* v_endExclusive_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_743_; 
v_str_731_ = lean_ctor_get(v_s_730_, 0);
lean_inc_ref(v_str_731_);
v_startInclusive_732_ = lean_ctor_get(v_s_730_, 1);
lean_inc(v_startInclusive_732_);
v_endExclusive_733_ = lean_ctor_get(v_s_730_, 2);
lean_inc(v_endExclusive_733_);
v___x_734_ = lean_unsigned_to_nat(0u);
v___x_735_ = l_String_Slice_Pos_skipWhile___at___00String_Slice_trimLeft_spec__0(v_s_730_, v___x_734_);
v_isSharedCheck_743_ = !lean_is_exclusive(v_s_730_);
if (v_isSharedCheck_743_ == 0)
{
lean_object* v_unused_744_; lean_object* v_unused_745_; lean_object* v_unused_746_; 
v_unused_744_ = lean_ctor_get(v_s_730_, 2);
lean_dec(v_unused_744_);
v_unused_745_ = lean_ctor_get(v_s_730_, 1);
lean_dec(v_unused_745_);
v_unused_746_ = lean_ctor_get(v_s_730_, 0);
lean_dec(v_unused_746_);
v___x_737_ = v_s_730_;
v_isShared_738_ = v_isSharedCheck_743_;
goto v_resetjp_736_;
}
else
{
lean_dec(v_s_730_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_743_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; lean_object* v___x_741_; 
v___x_739_ = lean_nat_add(v_startInclusive_732_, v___x_735_);
lean_dec(v___x_735_);
lean_dec(v_startInclusive_732_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 1, v___x_739_);
v___x_741_ = v___x_737_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_str_731_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v___x_739_);
lean_ctor_set(v_reuseFailAlloc_742_, 2, v_endExclusive_733_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_trimAscii(lean_object* v_s_747_){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_748_ = lean_unsigned_to_nat(0u);
v___x_749_ = lean_string_utf8_byte_size(v_s_747_);
v___x_750_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_750_, 0, v_s_747_);
lean_ctor_set(v___x_750_, 1, v___x_748_);
lean_ctor_set(v___x_750_, 2, v___x_749_);
v___x_751_ = l_String_Slice_trimAscii(v___x_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trim(lean_object* v_s_752_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_String_Slice_trimAscii(v_s_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* lean_string_trim(lean_object* v_s_754_){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v_str_759_; lean_object* v_startInclusive_760_; lean_object* v_endExclusive_761_; lean_object* v___x_762_; 
v___x_755_ = lean_unsigned_to_nat(0u);
v___x_756_ = lean_string_utf8_byte_size(v_s_754_);
v___x_757_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_757_, 0, v_s_754_);
lean_ctor_set(v___x_757_, 1, v___x_755_);
lean_ctor_set(v___x_757_, 2, v___x_756_);
v___x_758_ = l_String_Slice_trimAscii(v___x_757_);
v_str_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc_ref(v_str_759_);
v_startInclusive_760_ = lean_ctor_get(v___x_758_, 1);
lean_inc(v_startInclusive_760_);
v_endExclusive_761_ = lean_ctor_get(v___x_758_, 2);
lean_inc(v_endExclusive_761_);
lean_dec_ref(v___x_758_);
v___x_762_ = lean_string_utf8_extract_fast(v_str_759_, v_startInclusive_760_, v_endExclusive_761_);
lean_dec(v_endExclusive_761_);
lean_dec(v_startInclusive_760_);
lean_dec_ref(v_str_759_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextWhile(lean_object* v_s_763_, lean_object* v_p_764_, lean_object* v_i_765_){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = lean_string_utf8_byte_size(v_s_763_);
v___x_767_ = l_Substring_Raw_takeWhileAux(v_s_763_, v___x_766_, v_p_764_, v_i_765_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextWhile___boxed(lean_object* v_s_768_, lean_object* v_p_769_, lean_object* v_i_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_String_Pos_Raw_nextWhile(v_s_768_, v_p_769_, v_i_770_);
lean_dec_ref(v_s_768_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_String_nextWhile(lean_object* v_s_772_, lean_object* v_p_773_, lean_object* v_i_774_){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = lean_string_utf8_byte_size(v_s_772_);
v___x_776_ = l_Substring_Raw_takeWhileAux(v_s_772_, v___x_775_, v_p_773_, v_i_774_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_String_nextWhile___boxed(lean_object* v_s_777_, lean_object* v_p_778_, lean_object* v_i_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_String_nextWhile(v_s_777_, v_p_778_, v_i_779_);
lean_dec_ref(v_s_777_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0(lean_object* v_p_781_, lean_object* v_s_782_, lean_object* v_stopPos_783_, lean_object* v_i_784_){
_start:
{
uint8_t v___x_785_; 
v___x_785_ = lean_nat_dec_lt(v_i_784_, v_stopPos_783_);
if (v___x_785_ == 0)
{
lean_dec_ref(v_p_781_);
return v_i_784_;
}
else
{
uint32_t v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_786_ = lean_string_utf8_get(v_s_782_, v_i_784_);
v___x_787_ = lean_box_uint32(v___x_786_);
lean_inc_ref(v_p_781_);
v___x_788_ = lean_apply_1(v_p_781_, v___x_787_);
v___x_789_ = lean_unbox(v___x_788_);
if (v___x_789_ == 0)
{
lean_dec_ref(v_p_781_);
return v_i_784_;
}
else
{
lean_object* v___x_790_; 
v___x_790_ = lean_string_utf8_next(v_s_782_, v_i_784_);
lean_dec(v_i_784_);
v_i_784_ = v___x_790_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0___boxed(lean_object* v_p_792_, lean_object* v_s_793_, lean_object* v_stopPos_794_, lean_object* v_i_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0(v_p_792_, v_s_793_, v_stopPos_794_, v_i_795_);
lean_dec(v_stopPos_794_);
lean_dec_ref(v_s_793_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* lean_string_nextwhile(lean_object* v_s_797_, lean_object* v_p_798_, lean_object* v_i_799_){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = lean_string_utf8_byte_size(v_s_797_);
v___x_801_ = l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0(v_p_798_, v_s_797_, v___x_800_, v_i_799_);
lean_dec_ref(v_s_797_);
return v___x_801_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_Raw_nextUntil___lam__0(lean_object* v_p_802_, uint32_t v_c_803_){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v___x_804_ = lean_box_uint32(v_c_803_);
v___x_805_ = lean_apply_1(v_p_802_, v___x_804_);
v___x_806_ = lean_unbox(v___x_805_);
if (v___x_806_ == 0)
{
uint8_t v___x_807_; 
v___x_807_ = 1;
return v___x_807_;
}
else
{
uint8_t v___x_808_; 
v___x_808_ = 0;
return v___x_808_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextUntil___lam__0___boxed(lean_object* v_p_809_, lean_object* v_c_810_){
_start:
{
uint32_t v_c_boxed_811_; uint8_t v_res_812_; lean_object* v_r_813_; 
v_c_boxed_811_ = lean_unbox_uint32(v_c_810_);
lean_dec(v_c_810_);
v_res_812_ = l_String_Pos_Raw_nextUntil___lam__0(v_p_809_, v_c_boxed_811_);
v_r_813_ = lean_box(v_res_812_);
return v_r_813_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextUntil(lean_object* v_s_814_, lean_object* v_p_815_, lean_object* v_i_816_){
_start:
{
lean_object* v___f_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___f_817_ = lean_alloc_closure((void*)(l_String_Pos_Raw_nextUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_817_, 0, v_p_815_);
v___x_818_ = lean_string_utf8_byte_size(v_s_814_);
v___x_819_ = l_Substring_Raw_takeWhileAux(v_s_814_, v___x_818_, v___f_817_, v_i_816_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextUntil___boxed(lean_object* v_s_820_, lean_object* v_p_821_, lean_object* v_i_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_String_Pos_Raw_nextUntil(v_s_820_, v_p_821_, v_i_822_);
lean_dec_ref(v_s_820_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0(lean_object* v_p_824_, lean_object* v_s_825_, lean_object* v_stopPos_826_, lean_object* v_i_827_){
_start:
{
uint8_t v___x_828_; 
v___x_828_ = lean_nat_dec_lt(v_i_827_, v_stopPos_826_);
if (v___x_828_ == 0)
{
lean_dec_ref(v_p_824_);
return v_i_827_;
}
else
{
uint32_t v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; uint8_t v___x_832_; 
v___x_829_ = lean_string_utf8_get(v_s_825_, v_i_827_);
v___x_830_ = lean_box_uint32(v___x_829_);
lean_inc_ref(v_p_824_);
v___x_831_ = lean_apply_1(v_p_824_, v___x_830_);
v___x_832_ = lean_unbox(v___x_831_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; 
v___x_833_ = lean_string_utf8_next(v_s_825_, v_i_827_);
lean_dec(v_i_827_);
v_i_827_ = v___x_833_;
goto _start;
}
else
{
lean_dec_ref(v_p_824_);
return v_i_827_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0___boxed(lean_object* v_p_835_, lean_object* v_s_836_, lean_object* v_stopPos_837_, lean_object* v_i_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0(v_p_835_, v_s_836_, v_stopPos_837_, v_i_838_);
lean_dec(v_stopPos_837_);
lean_dec_ref(v_s_836_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_String_nextUntil(lean_object* v_s_840_, lean_object* v_p_841_, lean_object* v_i_842_){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_843_ = lean_string_utf8_byte_size(v_s_840_);
v___x_844_ = l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0(v_p_841_, v_s_840_, v___x_843_, v_i_842_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_String_nextUntil___boxed(lean_object* v_s_845_, lean_object* v_p_846_, lean_object* v_i_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_String_nextUntil(v_s_845_, v_p_846_, v_i_847_);
lean_dec_ref(v_s_845_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___redArg(lean_object* v_s_849_, lean_object* v_inst_850_){
_start:
{
lean_object* v_skipPrefix_x3f_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_871_; 
v_skipPrefix_x3f_851_ = lean_ctor_get(v_inst_850_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v_inst_850_);
if (v_isSharedCheck_871_ == 0)
{
lean_object* v_unused_872_; lean_object* v_unused_873_; 
v_unused_872_ = lean_ctor_get(v_inst_850_, 2);
lean_dec(v_unused_872_);
v_unused_873_ = lean_ctor_get(v_inst_850_, 1);
lean_dec(v_unused_873_);
v___x_853_ = v_inst_850_;
v_isShared_854_ = v_isSharedCheck_871_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_skipPrefix_x3f_851_);
lean_dec(v_inst_850_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_871_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_855_ = lean_string_utf8_byte_size(v_s_849_);
v___x_856_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_s_849_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 2, v___x_855_);
lean_ctor_set(v___x_853_, 1, v___x_856_);
lean_ctor_set(v___x_853_, 0, v_s_849_);
v___x_858_ = v___x_853_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_s_849_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v___x_856_);
lean_ctor_set(v_reuseFailAlloc_870_, 2, v___x_855_);
v___x_858_ = v_reuseFailAlloc_870_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
lean_object* v___x_859_; 
v___x_859_ = lean_apply_1(v_skipPrefix_x3f_851_, v___x_858_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v___x_860_; 
lean_dec_ref(v_s_849_);
v___x_860_ = lean_box(0);
return v___x_860_;
}
else
{
lean_object* v_val_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_869_; 
v_val_861_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_869_ == 0)
{
v___x_863_ = v___x_859_;
v_isShared_864_ = v_isSharedCheck_869_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_val_861_);
lean_dec(v___x_859_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_869_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; lean_object* v___x_867_; 
v___x_865_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_865_, 0, v_s_849_);
lean_ctor_set(v___x_865_, 1, v_val_861_);
lean_ctor_set(v___x_865_, 2, v___x_855_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_865_);
v___x_867_ = v___x_863_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_865_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f(lean_object* v_00_u03c1_874_, lean_object* v_s_875_, lean_object* v_pat_876_, lean_object* v_inst_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_String_dropPrefix_x3f___redArg(v_s_875_, v_inst_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___boxed(lean_object* v_00_u03c1_879_, lean_object* v_s_880_, lean_object* v_pat_881_, lean_object* v_inst_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_String_dropPrefix_x3f(v_00_u03c1_879_, v_s_880_, v_pat_881_, v_inst_882_);
lean_dec(v_pat_881_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___redArg(lean_object* v_s_884_, lean_object* v_inst_885_){
_start:
{
lean_object* v_skipSuffix_x3f_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_906_; 
v_skipSuffix_x3f_886_ = lean_ctor_get(v_inst_885_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v_inst_885_);
if (v_isSharedCheck_906_ == 0)
{
lean_object* v_unused_907_; lean_object* v_unused_908_; 
v_unused_907_ = lean_ctor_get(v_inst_885_, 2);
lean_dec(v_unused_907_);
v_unused_908_ = lean_ctor_get(v_inst_885_, 1);
lean_dec(v_unused_908_);
v___x_888_ = v_inst_885_;
v_isShared_889_ = v_isSharedCheck_906_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_skipSuffix_x3f_886_);
lean_dec(v_inst_885_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_906_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_893_; 
v___x_890_ = lean_string_utf8_byte_size(v_s_884_);
v___x_891_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_s_884_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 2, v___x_890_);
lean_ctor_set(v___x_888_, 1, v___x_891_);
lean_ctor_set(v___x_888_, 0, v_s_884_);
v___x_893_ = v___x_888_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_s_884_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v___x_891_);
lean_ctor_set(v_reuseFailAlloc_905_, 2, v___x_890_);
v___x_893_ = v_reuseFailAlloc_905_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
lean_object* v___x_894_; 
v___x_894_ = lean_apply_1(v_skipSuffix_x3f_886_, v___x_893_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v___x_895_; 
lean_dec_ref(v_s_884_);
v___x_895_ = lean_box(0);
return v___x_895_;
}
else
{
lean_object* v_val_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_904_; 
v_val_896_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_904_ == 0)
{
v___x_898_ = v___x_894_;
v_isShared_899_ = v_isSharedCheck_904_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_val_896_);
lean_dec(v___x_894_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_904_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_900_; lean_object* v___x_902_; 
v___x_900_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_900_, 0, v_s_884_);
lean_ctor_set(v___x_900_, 1, v___x_891_);
lean_ctor_set(v___x_900_, 2, v_val_896_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 0, v___x_900_);
v___x_902_ = v___x_898_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_900_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f(lean_object* v_00_u03c1_909_, lean_object* v_s_910_, lean_object* v_pat_911_, lean_object* v_inst_912_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = l_String_dropSuffix_x3f___redArg(v_s_910_, v_inst_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___boxed(lean_object* v_00_u03c1_914_, lean_object* v_s_915_, lean_object* v_pat_916_, lean_object* v_inst_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_String_dropSuffix_x3f(v_00_u03c1_914_, v_s_915_, v_pat_916_, v_inst_917_);
lean_dec(v_pat_916_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix___redArg(lean_object* v_s_919_, lean_object* v_inst_920_){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_921_ = lean_unsigned_to_nat(0u);
v___x_922_ = lean_string_utf8_byte_size(v_s_919_);
v___x_923_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_923_, 0, v_s_919_);
lean_ctor_set(v___x_923_, 1, v___x_921_);
lean_ctor_set(v___x_923_, 2, v___x_922_);
v___x_924_ = l_String_Slice_dropPrefix___redArg(v___x_923_, v_inst_920_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix(lean_object* v_00_u03c1_925_, lean_object* v_s_926_, lean_object* v_pat_927_, lean_object* v_inst_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_String_dropPrefix___redArg(v_s_926_, v_inst_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix___boxed(lean_object* v_00_u03c1_930_, lean_object* v_s_931_, lean_object* v_pat_932_, lean_object* v_inst_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_String_dropPrefix(v_00_u03c1_930_, v_s_931_, v_pat_932_, v_inst_933_);
lean_dec(v_pat_932_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg(lean_object* v_pre_935_, lean_object* v_s_936_){
_start:
{
lean_object* v_str_937_; lean_object* v_startInclusive_938_; lean_object* v_endExclusive_939_; lean_object* v___x_940_; lean_object* v___x_941_; uint8_t v___x_942_; 
v_str_937_ = lean_ctor_get(v_s_936_, 0);
v_startInclusive_938_ = lean_ctor_get(v_s_936_, 1);
v_endExclusive_939_ = lean_ctor_get(v_s_936_, 2);
v___x_940_ = lean_string_utf8_byte_size(v_pre_935_);
v___x_941_ = lean_nat_sub(v_endExclusive_939_, v_startInclusive_938_);
v___x_942_ = lean_nat_dec_le(v___x_940_, v___x_941_);
lean_dec(v___x_941_);
if (v___x_942_ == 0)
{
return v_s_936_;
}
else
{
lean_object* v___x_943_; uint8_t v___x_944_; 
v___x_943_ = lean_unsigned_to_nat(0u);
v___x_944_ = lean_string_memcmp(v_str_937_, v_pre_935_, v_startInclusive_938_, v___x_943_, v___x_940_);
if (v___x_944_ == 0)
{
return v_s_936_;
}
else
{
lean_object* v___x_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_953_; 
lean_inc(v_endExclusive_939_);
lean_inc(v_startInclusive_938_);
lean_inc_ref(v_str_937_);
v___x_945_ = l_String_Slice_pos_x21(v_s_936_, v___x_940_);
v_isSharedCheck_953_ = !lean_is_exclusive(v_s_936_);
if (v_isSharedCheck_953_ == 0)
{
lean_object* v_unused_954_; lean_object* v_unused_955_; lean_object* v_unused_956_; 
v_unused_954_ = lean_ctor_get(v_s_936_, 2);
lean_dec(v_unused_954_);
v_unused_955_ = lean_ctor_get(v_s_936_, 1);
lean_dec(v_unused_955_);
v_unused_956_ = lean_ctor_get(v_s_936_, 0);
lean_dec(v_unused_956_);
v___x_947_ = v_s_936_;
v_isShared_948_ = v_isSharedCheck_953_;
goto v_resetjp_946_;
}
else
{
lean_dec(v_s_936_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_953_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_949_; lean_object* v___x_951_; 
v___x_949_ = lean_nat_add(v_startInclusive_938_, v___x_945_);
lean_dec(v___x_945_);
lean_dec(v_startInclusive_938_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 1, v___x_949_);
v___x_951_ = v___x_947_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_str_937_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v___x_949_);
lean_ctor_set(v_reuseFailAlloc_952_, 2, v_endExclusive_939_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg___boxed(lean_object* v_pre_957_, lean_object* v_s_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg(v_pre_957_, v_s_958_);
lean_dec_ref(v_pre_957_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix___at___00String_stripPrefix_spec__0(lean_object* v_pre_960_, lean_object* v_s_961_, lean_object* v_pat_962_){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_963_ = lean_unsigned_to_nat(0u);
v___x_964_ = lean_string_utf8_byte_size(v_s_961_);
v___x_965_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_965_, 0, v_s_961_);
lean_ctor_set(v___x_965_, 1, v___x_963_);
lean_ctor_set(v___x_965_, 2, v___x_964_);
v___x_966_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg(v_pre_960_, v___x_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix___at___00String_stripPrefix_spec__0___boxed(lean_object* v_pre_967_, lean_object* v_s_968_, lean_object* v_pat_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_String_dropPrefix___at___00String_stripPrefix_spec__0(v_pre_967_, v_s_968_, v_pat_969_);
lean_dec_ref(v_pat_969_);
lean_dec_ref(v_pre_967_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_String_stripPrefix(lean_object* v_s_971_, lean_object* v_pre_972_){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = l_String_dropPrefix___at___00String_stripPrefix_spec__0(v_pre_972_, v_s_971_, v_pre_972_);
v___x_974_ = l_String_Slice_toString(v___x_973_);
lean_dec_ref(v___x_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_String_stripPrefix___boxed(lean_object* v_s_975_, lean_object* v_pre_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_String_stripPrefix(v_s_975_, v_pre_976_);
lean_dec_ref(v_pre_976_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0(lean_object* v_pat_978_, lean_object* v_pre_979_, lean_object* v_s_980_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg(v_pre_979_, v_s_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___boxed(lean_object* v_pat_982_, lean_object* v_pre_983_, lean_object* v_s_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0(v_pat_982_, v_pre_983_, v_s_984_);
lean_dec_ref(v_pre_983_);
lean_dec_ref(v_pat_982_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix___redArg(lean_object* v_s_986_, lean_object* v_inst_987_){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_988_ = lean_unsigned_to_nat(0u);
v___x_989_ = lean_string_utf8_byte_size(v_s_986_);
v___x_990_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_990_, 0, v_s_986_);
lean_ctor_set(v___x_990_, 1, v___x_988_);
lean_ctor_set(v___x_990_, 2, v___x_989_);
v___x_991_ = l_String_Slice_dropSuffix___redArg(v___x_990_, v_inst_987_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix(lean_object* v_00_u03c1_992_, lean_object* v_s_993_, lean_object* v_pat_994_, lean_object* v_inst_995_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l_String_dropSuffix___redArg(v_s_993_, v_inst_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix___boxed(lean_object* v_00_u03c1_997_, lean_object* v_s_998_, lean_object* v_pat_999_, lean_object* v_inst_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_String_dropSuffix(v_00_u03c1_997_, v_s_998_, v_pat_999_, v_inst_1000_);
lean_dec(v_pat_999_);
return v_res_1001_;
}
}
lean_object* runtime_initialize_Init_Data_String_Substring(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

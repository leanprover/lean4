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
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
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
uint8_t l_String_all___redArg(lean_object* v_s_237_, lean_object* v_inst_238_){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; uint8_t v_decide_243_; 
v___x_239_ = lean_unsigned_to_nat(0u);
v___x_240_ = lean_string_utf8_byte_size(v_s_237_);
v___x_241_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_241_, 0, v_s_237_);
lean_ctor_set(v___x_241_, 1, v___x_239_);
lean_ctor_set(v___x_241_, 2, v___x_240_);
v___x_242_ = l_String_Slice_Pos_skipWhile___redArg(v___x_241_, v___x_239_, v_inst_238_);
lean_dec_ref_known(v___x_241_, 3);
v_decide_243_ = lean_nat_dec_eq(v___x_242_, v___x_240_);
lean_dec(v___x_242_);
return v_decide_243_;
}
}
LEAN_EXPORT void l_String_all___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_237_ = stack[0].m_obj;
lean_object* v_inst_238_ = stack[1].m_obj;
uint8_t v_res_244_;
v_res_244_ = l_String_all___redArg(v_s_237_, v_inst_238_);
stack->m_num = v_res_244_;
}
LEAN_EXPORT lean_object* l_String_all___redArg___boxed(lean_object* v_s_245_, lean_object* v_inst_246_){
_start:
{
uint8_t v_res_247_; lean_object* v_r_248_; 
v_res_247_ = l_String_all___redArg(v_s_245_, v_inst_246_);
v_r_248_ = lean_box(v_res_247_);
return v_r_248_;
}
}
uint8_t l_String_all(lean_object* v_00_u03c1_249_, lean_object* v_s_250_, lean_object* v_pat_251_, lean_object* v_inst_252_){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v_decide_257_; 
v___x_253_ = lean_unsigned_to_nat(0u);
v___x_254_ = lean_string_utf8_byte_size(v_s_250_);
v___x_255_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_255_, 0, v_s_250_);
lean_ctor_set(v___x_255_, 1, v___x_253_);
lean_ctor_set(v___x_255_, 2, v___x_254_);
v___x_256_ = l_String_Slice_Pos_skipWhile___redArg(v___x_255_, v___x_253_, v_inst_252_);
lean_dec_ref_known(v___x_255_, 3);
v_decide_257_ = lean_nat_dec_eq(v___x_256_, v___x_254_);
lean_dec(v___x_256_);
return v_decide_257_;
}
}
LEAN_EXPORT void l_String_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_250_ = stack[1].m_obj;
lean_object* v_pat_251_ = stack[2].m_obj;
lean_object* v_inst_252_ = stack[3].m_obj;
uint8_t v_res_258_;
v_res_258_ = l_String_all(lean_box(0), v_s_250_, v_pat_251_, v_inst_252_);
stack->m_num = v_res_258_;
}
LEAN_EXPORT lean_object* l_String_all___boxed(lean_object* v_00_u03c1_259_, lean_object* v_s_260_, lean_object* v_pat_261_, lean_object* v_inst_262_){
_start:
{
uint8_t v_res_263_; lean_object* v_r_264_; 
v_res_263_ = l_String_all(v_00_u03c1_259_, v_s_260_, v_pat_261_, v_inst_262_);
lean_dec(v_pat_261_);
v_r_264_ = lean_box(v_res_263_);
return v_r_264_;
}
}
uint8_t l_String_revAll___redArg(lean_object* v_s_265_, lean_object* v_inst_266_){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v_decide_271_; 
v___x_267_ = lean_unsigned_to_nat(0u);
v___x_268_ = lean_string_utf8_byte_size(v_s_265_);
v___x_269_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_269_, 0, v_s_265_);
lean_ctor_set(v___x_269_, 1, v___x_267_);
lean_ctor_set(v___x_269_, 2, v___x_268_);
v___x_270_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_269_, v___x_268_, v_inst_266_);
lean_dec_ref_known(v___x_269_, 3);
v_decide_271_ = lean_nat_dec_eq(v___x_270_, v___x_267_);
lean_dec(v___x_270_);
return v_decide_271_;
}
}
LEAN_EXPORT void l_String_revAll___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_265_ = stack[0].m_obj;
lean_object* v_inst_266_ = stack[1].m_obj;
uint8_t v_res_272_;
v_res_272_ = l_String_revAll___redArg(v_s_265_, v_inst_266_);
stack->m_num = v_res_272_;
}
LEAN_EXPORT lean_object* l_String_revAll___redArg___boxed(lean_object* v_s_273_, lean_object* v_inst_274_){
_start:
{
uint8_t v_res_275_; lean_object* v_r_276_; 
v_res_275_ = l_String_revAll___redArg(v_s_273_, v_inst_274_);
v_r_276_ = lean_box(v_res_275_);
return v_r_276_;
}
}
uint8_t l_String_revAll(lean_object* v_00_u03c1_277_, lean_object* v_s_278_, lean_object* v_pat_279_, lean_object* v_inst_280_){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v_decide_285_; 
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = lean_string_utf8_byte_size(v_s_278_);
v___x_283_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_283_, 0, v_s_278_);
lean_ctor_set(v___x_283_, 1, v___x_281_);
lean_ctor_set(v___x_283_, 2, v___x_282_);
v___x_284_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_283_, v___x_282_, v_inst_280_);
lean_dec_ref_known(v___x_283_, 3);
v_decide_285_ = lean_nat_dec_eq(v___x_284_, v___x_281_);
lean_dec(v___x_284_);
return v_decide_285_;
}
}
LEAN_EXPORT void l_String_revAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_278_ = stack[1].m_obj;
lean_object* v_pat_279_ = stack[2].m_obj;
lean_object* v_inst_280_ = stack[3].m_obj;
uint8_t v_res_286_;
v_res_286_ = l_String_revAll(lean_box(0), v_s_278_, v_pat_279_, v_inst_280_);
stack->m_num = v_res_286_;
}
LEAN_EXPORT lean_object* l_String_revAll___boxed(lean_object* v_00_u03c1_287_, lean_object* v_s_288_, lean_object* v_pat_289_, lean_object* v_inst_290_){
_start:
{
uint8_t v_res_291_; lean_object* v_r_292_; 
v_res_291_ = l_String_revAll(v_00_u03c1_287_, v_s_288_, v_pat_289_, v_inst_290_);
lean_dec(v_pat_289_);
v_r_292_ = lean_box(v_res_291_);
return v_r_292_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_skip_x3f___redArg(lean_object* v_s_293_, lean_object* v_pos_294_, lean_object* v_inst_295_){
_start:
{
lean_object* v_skipPrefix_x3f_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_315_; 
v_skipPrefix_x3f_296_ = lean_ctor_get(v_inst_295_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v_inst_295_);
if (v_isSharedCheck_315_ == 0)
{
lean_object* v_unused_316_; lean_object* v_unused_317_; 
v_unused_316_ = lean_ctor_get(v_inst_295_, 2);
lean_dec(v_unused_316_);
v_unused_317_ = lean_ctor_get(v_inst_295_, 1);
lean_dec(v_unused_317_);
v___x_298_ = v_inst_295_;
v_isShared_299_ = v_isSharedCheck_315_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_skipPrefix_x3f_296_);
lean_dec(v_inst_295_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_315_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_300_; lean_object* v___x_302_; 
v___x_300_ = lean_string_utf8_byte_size(v_s_293_);
lean_inc(v_pos_294_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 2, v___x_300_);
lean_ctor_set(v___x_298_, 1, v_pos_294_);
lean_ctor_set(v___x_298_, 0, v_s_293_);
v___x_302_ = v___x_298_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_s_293_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v_pos_294_);
lean_ctor_set(v_reuseFailAlloc_314_, 2, v___x_300_);
v___x_302_ = v_reuseFailAlloc_314_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
lean_object* v___x_303_; 
v___x_303_ = lean_apply_1(v_skipPrefix_x3f_296_, v___x_302_);
if (lean_obj_tag(v___x_303_) == 0)
{
lean_object* v___x_304_; 
lean_dec(v_pos_294_);
v___x_304_ = lean_box(0);
return v___x_304_;
}
else
{
lean_object* v_val_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_313_; 
v_val_305_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_313_ == 0)
{
v___x_307_ = v___x_303_;
v_isShared_308_ = v_isSharedCheck_313_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_val_305_);
lean_dec(v___x_303_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_313_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_309_; lean_object* v___x_311_; 
v___x_309_ = lean_nat_add(v_pos_294_, v_val_305_);
lean_dec(v_val_305_);
lean_dec(v_pos_294_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v___x_309_);
v___x_311_ = v___x_307_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_309_);
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
}
LEAN_EXPORT lean_object* l_String_Pos_skip_x3f(lean_object* v_00_u03c1_318_, lean_object* v_s_319_, lean_object* v_pos_320_, lean_object* v_pat_321_, lean_object* v_inst_322_){
_start:
{
lean_object* v_skipPrefix_x3f_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_342_; 
v_skipPrefix_x3f_323_ = lean_ctor_get(v_inst_322_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v_inst_322_);
if (v_isSharedCheck_342_ == 0)
{
lean_object* v_unused_343_; lean_object* v_unused_344_; 
v_unused_343_ = lean_ctor_get(v_inst_322_, 2);
lean_dec(v_unused_343_);
v_unused_344_ = lean_ctor_get(v_inst_322_, 1);
lean_dec(v_unused_344_);
v___x_325_ = v_inst_322_;
v_isShared_326_ = v_isSharedCheck_342_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_skipPrefix_x3f_323_);
lean_dec(v_inst_322_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_342_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_327_; lean_object* v___x_329_; 
v___x_327_ = lean_string_utf8_byte_size(v_s_319_);
lean_inc(v_pos_320_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 2, v___x_327_);
lean_ctor_set(v___x_325_, 1, v_pos_320_);
lean_ctor_set(v___x_325_, 0, v_s_319_);
v___x_329_ = v___x_325_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_s_319_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_pos_320_);
lean_ctor_set(v_reuseFailAlloc_341_, 2, v___x_327_);
v___x_329_ = v_reuseFailAlloc_341_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
lean_object* v___x_330_; 
v___x_330_ = lean_apply_1(v_skipPrefix_x3f_323_, v___x_329_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v___x_331_; 
lean_dec(v_pos_320_);
v___x_331_ = lean_box(0);
return v___x_331_;
}
else
{
lean_object* v_val_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_340_; 
v_val_332_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_340_ == 0)
{
v___x_334_ = v___x_330_;
v_isShared_335_ = v_isSharedCheck_340_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_val_332_);
lean_dec(v___x_330_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_340_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_336_; lean_object* v___x_338_; 
v___x_336_ = lean_nat_add(v_pos_320_, v_val_332_);
lean_dec(v_val_332_);
lean_dec(v_pos_320_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_336_);
v___x_338_ = v___x_334_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_336_);
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
LEAN_EXPORT lean_object* l_String_Pos_skip_x3f___boxed(lean_object* v_00_u03c1_345_, lean_object* v_s_346_, lean_object* v_pos_347_, lean_object* v_pat_348_, lean_object* v_inst_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_String_Pos_skip_x3f(v_00_u03c1_345_, v_s_346_, v_pos_347_, v_pat_348_, v_inst_349_);
lean_dec(v_pat_348_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_skipWhile___redArg(lean_object* v_s_351_, lean_object* v_pos_352_, lean_object* v_inst_353_){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_354_ = lean_unsigned_to_nat(0u);
v___x_355_ = lean_string_utf8_byte_size(v_s_351_);
v___x_356_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_356_, 0, v_s_351_);
lean_ctor_set(v___x_356_, 1, v___x_354_);
lean_ctor_set(v___x_356_, 2, v___x_355_);
v___x_357_ = l_String_Slice_Pos_skipWhile___redArg(v___x_356_, v_pos_352_, v_inst_353_);
lean_dec_ref_known(v___x_356_, 3);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_skipWhile(lean_object* v_00_u03c1_358_, lean_object* v_s_359_, lean_object* v_pos_360_, lean_object* v_pat_361_, lean_object* v_inst_362_){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_363_ = lean_unsigned_to_nat(0u);
v___x_364_ = lean_string_utf8_byte_size(v_s_359_);
v___x_365_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_365_, 0, v_s_359_);
lean_ctor_set(v___x_365_, 1, v___x_363_);
lean_ctor_set(v___x_365_, 2, v___x_364_);
v___x_366_ = l_String_Slice_Pos_skipWhile___redArg(v___x_365_, v_pos_360_, v_inst_362_);
lean_dec_ref_known(v___x_365_, 3);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_skipWhile___boxed(lean_object* v_00_u03c1_367_, lean_object* v_s_368_, lean_object* v_pos_369_, lean_object* v_pat_370_, lean_object* v_inst_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_String_Pos_skipWhile(v_00_u03c1_367_, v_s_368_, v_pos_369_, v_pat_370_, v_inst_371_);
lean_dec(v_pat_370_);
return v_res_372_;
}
}
uint8_t l_String_startsWith___redArg(lean_object* v_s_373_, lean_object* v_inst_374_){
_start:
{
lean_object* v_startsWith_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_386_; 
v_startsWith_375_ = lean_ctor_get(v_inst_374_, 2);
v_isSharedCheck_386_ = !lean_is_exclusive(v_inst_374_);
if (v_isSharedCheck_386_ == 0)
{
lean_object* v_unused_387_; lean_object* v_unused_388_; 
v_unused_387_ = lean_ctor_get(v_inst_374_, 1);
lean_dec(v_unused_387_);
v_unused_388_ = lean_ctor_get(v_inst_374_, 0);
lean_dec(v_unused_388_);
v___x_377_ = v_inst_374_;
v_isShared_378_ = v_isSharedCheck_386_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_startsWith_375_);
lean_dec(v_inst_374_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_386_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_382_; 
v___x_379_ = lean_string_utf8_byte_size(v_s_373_);
v___x_380_ = lean_unsigned_to_nat(0u);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 2, v___x_379_);
lean_ctor_set(v___x_377_, 1, v___x_380_);
lean_ctor_set(v___x_377_, 0, v_s_373_);
v___x_382_ = v___x_377_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_s_373_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v___x_380_);
lean_ctor_set(v_reuseFailAlloc_385_, 2, v___x_379_);
v___x_382_ = v_reuseFailAlloc_385_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_383_ = lean_apply_1(v_startsWith_375_, v___x_382_);
v___x_384_ = lean_unbox(v___x_383_);
return v___x_384_;
}
}
}
}
LEAN_EXPORT void l_String_startsWith___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_373_ = stack[0].m_obj;
lean_object* v_inst_374_ = stack[1].m_obj;
uint8_t v_res_389_;
v_res_389_ = l_String_startsWith___redArg(v_s_373_, v_inst_374_);
stack->m_num = v_res_389_;
}
LEAN_EXPORT lean_object* l_String_startsWith___redArg___boxed(lean_object* v_s_390_, lean_object* v_inst_391_){
_start:
{
uint8_t v_res_392_; lean_object* v_r_393_; 
v_res_392_ = l_String_startsWith___redArg(v_s_390_, v_inst_391_);
v_r_393_ = lean_box(v_res_392_);
return v_r_393_;
}
}
uint8_t l_String_startsWith(lean_object* v_00_u03c1_394_, lean_object* v_s_395_, lean_object* v_pat_396_, lean_object* v_inst_397_){
_start:
{
lean_object* v_startsWith_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_409_; 
v_startsWith_398_ = lean_ctor_get(v_inst_397_, 2);
v_isSharedCheck_409_ = !lean_is_exclusive(v_inst_397_);
if (v_isSharedCheck_409_ == 0)
{
lean_object* v_unused_410_; lean_object* v_unused_411_; 
v_unused_410_ = lean_ctor_get(v_inst_397_, 1);
lean_dec(v_unused_410_);
v_unused_411_ = lean_ctor_get(v_inst_397_, 0);
lean_dec(v_unused_411_);
v___x_400_ = v_inst_397_;
v_isShared_401_ = v_isSharedCheck_409_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_startsWith_398_);
lean_dec(v_inst_397_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_409_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_402_ = lean_string_utf8_byte_size(v_s_395_);
v___x_403_ = lean_unsigned_to_nat(0u);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 2, v___x_402_);
lean_ctor_set(v___x_400_, 1, v___x_403_);
lean_ctor_set(v___x_400_, 0, v_s_395_);
v___x_405_ = v___x_400_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_s_395_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v___x_403_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v___x_402_);
v___x_405_ = v_reuseFailAlloc_408_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_406_ = lean_apply_1(v_startsWith_398_, v___x_405_);
v___x_407_ = lean_unbox(v___x_406_);
return v___x_407_;
}
}
}
}
LEAN_EXPORT void l_String_startsWith_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_395_ = stack[1].m_obj;
lean_object* v_pat_396_ = stack[2].m_obj;
lean_object* v_inst_397_ = stack[3].m_obj;
uint8_t v_res_412_;
v_res_412_ = l_String_startsWith(lean_box(0), v_s_395_, v_pat_396_, v_inst_397_);
stack->m_num = v_res_412_;
}
LEAN_EXPORT lean_object* l_String_startsWith___boxed(lean_object* v_00_u03c1_413_, lean_object* v_s_414_, lean_object* v_pat_415_, lean_object* v_inst_416_){
_start:
{
uint8_t v_res_417_; lean_object* v_r_418_; 
v_res_417_ = l_String_startsWith(v_00_u03c1_413_, v_s_414_, v_pat_415_, v_inst_416_);
lean_dec(v_pat_415_);
v_r_418_ = lean_box(v_res_417_);
return v_r_418_;
}
}
uint8_t l_String_isPrefixOf(lean_object* v_p_419_, lean_object* v_s_420_){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_421_ = lean_string_utf8_byte_size(v_s_420_);
v___x_422_ = lean_string_utf8_byte_size(v_p_419_);
v___x_423_ = lean_nat_dec_le(v___x_422_, v___x_421_);
if (v___x_423_ == 0)
{
return v___x_423_;
}
else
{
lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_424_ = lean_unsigned_to_nat(0u);
v___x_425_ = lean_string_memcmp(v_s_420_, v_p_419_, v___x_424_, v___x_424_, v___x_422_);
return v___x_425_;
}
}
}
LEAN_EXPORT void l_String_isPrefixOf_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_419_ = stack[0].m_obj;
lean_object* v_s_420_ = stack[1].m_obj;
uint8_t v_res_426_;
v_res_426_ = l_String_isPrefixOf(v_p_419_, v_s_420_);
stack->m_num = v_res_426_;
}
LEAN_EXPORT lean_object* l_String_isPrefixOf___boxed(lean_object* v_p_427_, lean_object* v_s_428_){
_start:
{
uint8_t v_res_429_; lean_object* v_r_430_; 
v_res_429_ = l_String_isPrefixOf(v_p_427_, v_s_428_);
lean_dec_ref(v_s_428_);
lean_dec_ref(v_p_427_);
v_r_430_ = lean_box(v_res_429_);
return v_r_430_;
}
}
uint8_t lean_string_isprefixof(lean_object* v_p_431_, lean_object* v_s_432_){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_433_ = lean_string_utf8_byte_size(v_s_432_);
v___x_434_ = lean_string_utf8_byte_size(v_p_431_);
v___x_435_ = lean_nat_dec_le(v___x_434_, v___x_433_);
if (v___x_435_ == 0)
{
lean_dec_ref(v_s_432_);
lean_dec_ref(v_p_431_);
return v___x_435_;
}
else
{
lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_436_ = lean_unsigned_to_nat(0u);
v___x_437_ = lean_string_memcmp(v_s_432_, v_p_431_, v___x_436_, v___x_436_, v___x_434_);
lean_dec_ref(v_p_431_);
lean_dec_ref(v_s_432_);
return v___x_437_;
}
}
}
LEAN_EXPORT void lean_string_isprefixof_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_431_ = stack[0].m_obj;
lean_object* v_s_432_ = stack[1].m_obj;
uint8_t v_res_438_;
v_res_438_ = lean_string_isprefixof(v_p_431_, v_s_432_);
stack->m_num = v_res_438_;
}
LEAN_EXPORT lean_object* l_String_Internal_isPrefixOfImpl___boxed(lean_object* v_p_439_, lean_object* v_s_440_){
_start:
{
uint8_t v_res_441_; lean_object* v_r_442_; 
v_res_441_ = lean_string_isprefixof(v_p_439_, v_s_440_);
v_r_442_ = lean_box(v_res_441_);
return v_r_442_;
}
}
uint8_t l_String_endsWith___redArg(lean_object* v_s_443_, lean_object* v_inst_444_){
_start:
{
lean_object* v_endsWith_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_456_; 
v_endsWith_445_ = lean_ctor_get(v_inst_444_, 2);
v_isSharedCheck_456_ = !lean_is_exclusive(v_inst_444_);
if (v_isSharedCheck_456_ == 0)
{
lean_object* v_unused_457_; lean_object* v_unused_458_; 
v_unused_457_ = lean_ctor_get(v_inst_444_, 1);
lean_dec(v_unused_457_);
v_unused_458_ = lean_ctor_get(v_inst_444_, 0);
lean_dec(v_unused_458_);
v___x_447_ = v_inst_444_;
v_isShared_448_ = v_isSharedCheck_456_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_endsWith_445_);
lean_dec(v_inst_444_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_456_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_449_ = lean_string_utf8_byte_size(v_s_443_);
v___x_450_ = lean_unsigned_to_nat(0u);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 2, v___x_449_);
lean_ctor_set(v___x_447_, 1, v___x_450_);
lean_ctor_set(v___x_447_, 0, v_s_443_);
v___x_452_ = v___x_447_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_s_443_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v___x_450_);
lean_ctor_set(v_reuseFailAlloc_455_, 2, v___x_449_);
v___x_452_ = v_reuseFailAlloc_455_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_453_ = lean_apply_1(v_endsWith_445_, v___x_452_);
v___x_454_ = lean_unbox(v___x_453_);
return v___x_454_;
}
}
}
}
LEAN_EXPORT void l_String_endsWith___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_443_ = stack[0].m_obj;
lean_object* v_inst_444_ = stack[1].m_obj;
uint8_t v_res_459_;
v_res_459_ = l_String_endsWith___redArg(v_s_443_, v_inst_444_);
stack->m_num = v_res_459_;
}
LEAN_EXPORT lean_object* l_String_endsWith___redArg___boxed(lean_object* v_s_460_, lean_object* v_inst_461_){
_start:
{
uint8_t v_res_462_; lean_object* v_r_463_; 
v_res_462_ = l_String_endsWith___redArg(v_s_460_, v_inst_461_);
v_r_463_ = lean_box(v_res_462_);
return v_r_463_;
}
}
uint8_t l_String_endsWith(lean_object* v_00_u03c1_464_, lean_object* v_s_465_, lean_object* v_pat_466_, lean_object* v_inst_467_){
_start:
{
lean_object* v_endsWith_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_479_; 
v_endsWith_468_ = lean_ctor_get(v_inst_467_, 2);
v_isSharedCheck_479_ = !lean_is_exclusive(v_inst_467_);
if (v_isSharedCheck_479_ == 0)
{
lean_object* v_unused_480_; lean_object* v_unused_481_; 
v_unused_480_ = lean_ctor_get(v_inst_467_, 1);
lean_dec(v_unused_480_);
v_unused_481_ = lean_ctor_get(v_inst_467_, 0);
lean_dec(v_unused_481_);
v___x_470_ = v_inst_467_;
v_isShared_471_ = v_isSharedCheck_479_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_endsWith_468_);
lean_dec(v_inst_467_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_479_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_475_; 
v___x_472_ = lean_string_utf8_byte_size(v_s_465_);
v___x_473_ = lean_unsigned_to_nat(0u);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 2, v___x_472_);
lean_ctor_set(v___x_470_, 1, v___x_473_);
lean_ctor_set(v___x_470_, 0, v_s_465_);
v___x_475_ = v___x_470_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_s_465_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_478_, 2, v___x_472_);
v___x_475_ = v_reuseFailAlloc_478_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_476_ = lean_apply_1(v_endsWith_468_, v___x_475_);
v___x_477_ = lean_unbox(v___x_476_);
return v___x_477_;
}
}
}
}
LEAN_EXPORT void l_String_endsWith_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_465_ = stack[1].m_obj;
lean_object* v_pat_466_ = stack[2].m_obj;
lean_object* v_inst_467_ = stack[3].m_obj;
uint8_t v_res_482_;
v_res_482_ = l_String_endsWith(lean_box(0), v_s_465_, v_pat_466_, v_inst_467_);
stack->m_num = v_res_482_;
}
LEAN_EXPORT lean_object* l_String_endsWith___boxed(lean_object* v_00_u03c1_483_, lean_object* v_s_484_, lean_object* v_pat_485_, lean_object* v_inst_486_){
_start:
{
uint8_t v_res_487_; lean_object* v_r_488_; 
v_res_487_ = l_String_endsWith(v_00_u03c1_483_, v_s_484_, v_pat_485_, v_inst_486_);
lean_dec(v_pat_485_);
v_r_488_ = lean_box(v_res_487_);
return v_r_488_;
}
}
LEAN_EXPORT lean_object* l_String_skipSuffix_x3f___redArg(lean_object* v_s_489_, lean_object* v_inst_490_){
_start:
{
lean_object* v_skipSuffix_x3f_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_510_; 
v_skipSuffix_x3f_491_ = lean_ctor_get(v_inst_490_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v_inst_490_);
if (v_isSharedCheck_510_ == 0)
{
lean_object* v_unused_511_; lean_object* v_unused_512_; 
v_unused_511_ = lean_ctor_get(v_inst_490_, 2);
lean_dec(v_unused_511_);
v_unused_512_ = lean_ctor_get(v_inst_490_, 1);
lean_dec(v_unused_512_);
v___x_493_ = v_inst_490_;
v_isShared_494_ = v_isSharedCheck_510_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_skipSuffix_x3f_491_);
lean_dec(v_inst_490_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_510_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_498_; 
v___x_495_ = lean_string_utf8_byte_size(v_s_489_);
v___x_496_ = lean_unsigned_to_nat(0u);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 2, v___x_495_);
lean_ctor_set(v___x_493_, 1, v___x_496_);
lean_ctor_set(v___x_493_, 0, v_s_489_);
v___x_498_ = v___x_493_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_s_489_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v___x_496_);
lean_ctor_set(v_reuseFailAlloc_509_, 2, v___x_495_);
v___x_498_ = v_reuseFailAlloc_509_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
lean_object* v___x_499_; 
v___x_499_ = lean_apply_1(v_skipSuffix_x3f_491_, v___x_498_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v___x_500_; 
v___x_500_ = lean_box(0);
return v___x_500_;
}
else
{
lean_object* v_val_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
v_val_501_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_508_ == 0)
{
v___x_503_ = v___x_499_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_val_501_);
lean_dec(v___x_499_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_val_501_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_skipSuffix_x3f(lean_object* v_00_u03c1_513_, lean_object* v_s_514_, lean_object* v_pat_515_, lean_object* v_inst_516_){
_start:
{
lean_object* v_skipSuffix_x3f_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_536_; 
v_skipSuffix_x3f_517_ = lean_ctor_get(v_inst_516_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v_inst_516_);
if (v_isSharedCheck_536_ == 0)
{
lean_object* v_unused_537_; lean_object* v_unused_538_; 
v_unused_537_ = lean_ctor_get(v_inst_516_, 2);
lean_dec(v_unused_537_);
v_unused_538_ = lean_ctor_get(v_inst_516_, 1);
lean_dec(v_unused_538_);
v___x_519_ = v_inst_516_;
v_isShared_520_ = v_isSharedCheck_536_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_skipSuffix_x3f_517_);
lean_dec(v_inst_516_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_536_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_524_; 
v___x_521_ = lean_string_utf8_byte_size(v_s_514_);
v___x_522_ = lean_unsigned_to_nat(0u);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 2, v___x_521_);
lean_ctor_set(v___x_519_, 1, v___x_522_);
lean_ctor_set(v___x_519_, 0, v_s_514_);
v___x_524_ = v___x_519_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_s_514_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v___x_522_);
lean_ctor_set(v_reuseFailAlloc_535_, 2, v___x_521_);
v___x_524_ = v_reuseFailAlloc_535_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
lean_object* v___x_525_; 
v___x_525_ = lean_apply_1(v_skipSuffix_x3f_517_, v___x_524_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v___x_526_; 
v___x_526_ = lean_box(0);
return v___x_526_;
}
else
{
lean_object* v_val_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
v_val_527_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_525_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_val_527_);
lean_dec(v___x_525_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_val_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_skipSuffix_x3f___boxed(lean_object* v_00_u03c1_539_, lean_object* v_s_540_, lean_object* v_pat_541_, lean_object* v_inst_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_String_skipSuffix_x3f(v_00_u03c1_539_, v_s_540_, v_pat_541_, v_inst_542_);
lean_dec(v_pat_541_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_String_skipSuffixWhile___redArg(lean_object* v_s_544_, lean_object* v_inst_545_){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = lean_string_utf8_byte_size(v_s_544_);
v___x_548_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_548_, 0, v_s_544_);
lean_ctor_set(v___x_548_, 1, v___x_546_);
lean_ctor_set(v___x_548_, 2, v___x_547_);
v___x_549_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_548_, v___x_547_, v_inst_545_);
lean_dec_ref_known(v___x_548_, 3);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_String_skipSuffixWhile(lean_object* v_00_u03c1_550_, lean_object* v_s_551_, lean_object* v_pat_552_, lean_object* v_inst_553_){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_554_ = lean_unsigned_to_nat(0u);
v___x_555_ = lean_string_utf8_byte_size(v_s_551_);
v___x_556_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_556_, 0, v_s_551_);
lean_ctor_set(v___x_556_, 1, v___x_554_);
lean_ctor_set(v___x_556_, 2, v___x_555_);
v___x_557_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_556_, v___x_555_, v_inst_553_);
lean_dec_ref_known(v___x_556_, 3);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_String_skipSuffixWhile___boxed(lean_object* v_00_u03c1_558_, lean_object* v_s_559_, lean_object* v_pat_560_, lean_object* v_inst_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_String_skipSuffixWhile(v_00_u03c1_558_, v_s_559_, v_pat_560_, v_inst_561_);
lean_dec(v_pat_560_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_revSkip_x3f___redArg(lean_object* v_s_563_, lean_object* v_pos_564_, lean_object* v_inst_565_){
_start:
{
lean_object* v_skipSuffix_x3f_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_584_; 
v_skipSuffix_x3f_566_ = lean_ctor_get(v_inst_565_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v_inst_565_);
if (v_isSharedCheck_584_ == 0)
{
lean_object* v_unused_585_; lean_object* v_unused_586_; 
v_unused_585_ = lean_ctor_get(v_inst_565_, 2);
lean_dec(v_unused_585_);
v_unused_586_ = lean_ctor_get(v_inst_565_, 1);
lean_dec(v_unused_586_);
v___x_568_ = v_inst_565_;
v_isShared_569_ = v_isSharedCheck_584_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_skipSuffix_x3f_566_);
lean_dec(v_inst_565_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_584_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_570_; lean_object* v___x_572_; 
v___x_570_ = lean_unsigned_to_nat(0u);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 2, v_pos_564_);
lean_ctor_set(v___x_568_, 1, v___x_570_);
lean_ctor_set(v___x_568_, 0, v_s_563_);
v___x_572_ = v___x_568_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_s_563_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v___x_570_);
lean_ctor_set(v_reuseFailAlloc_583_, 2, v_pos_564_);
v___x_572_ = v_reuseFailAlloc_583_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
lean_object* v___x_573_; 
v___x_573_ = lean_apply_1(v_skipSuffix_x3f_566_, v___x_572_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v___x_574_; 
v___x_574_ = lean_box(0);
return v___x_574_;
}
else
{
lean_object* v_val_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_582_; 
v_val_575_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_582_ == 0)
{
v___x_577_ = v___x_573_;
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_val_575_);
lean_dec(v___x_573_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_580_; 
if (v_isShared_578_ == 0)
{
v___x_580_ = v___x_577_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_val_575_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_revSkip_x3f(lean_object* v_00_u03c1_587_, lean_object* v_s_588_, lean_object* v_pos_589_, lean_object* v_pat_590_, lean_object* v_inst_591_){
_start:
{
lean_object* v_skipSuffix_x3f_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_610_; 
v_skipSuffix_x3f_592_ = lean_ctor_get(v_inst_591_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v_inst_591_);
if (v_isSharedCheck_610_ == 0)
{
lean_object* v_unused_611_; lean_object* v_unused_612_; 
v_unused_611_ = lean_ctor_get(v_inst_591_, 2);
lean_dec(v_unused_611_);
v_unused_612_ = lean_ctor_get(v_inst_591_, 1);
lean_dec(v_unused_612_);
v___x_594_ = v_inst_591_;
v_isShared_595_ = v_isSharedCheck_610_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_skipSuffix_x3f_592_);
lean_dec(v_inst_591_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_610_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_596_ = lean_unsigned_to_nat(0u);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 2, v_pos_589_);
lean_ctor_set(v___x_594_, 1, v___x_596_);
lean_ctor_set(v___x_594_, 0, v_s_588_);
v___x_598_ = v___x_594_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_s_588_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_609_, 2, v_pos_589_);
v___x_598_ = v_reuseFailAlloc_609_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v___x_599_; 
v___x_599_ = lean_apply_1(v_skipSuffix_x3f_592_, v___x_598_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v___x_600_; 
v___x_600_ = lean_box(0);
return v___x_600_;
}
else
{
lean_object* v_val_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
v_val_601_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v___x_599_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_val_601_);
lean_dec(v___x_599_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_val_601_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_revSkip_x3f___boxed(lean_object* v_00_u03c1_613_, lean_object* v_s_614_, lean_object* v_pos_615_, lean_object* v_pat_616_, lean_object* v_inst_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_String_Pos_revSkip_x3f(v_00_u03c1_613_, v_s_614_, v_pos_615_, v_pat_616_, v_inst_617_);
lean_dec(v_pat_616_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_revSkipWhile___redArg(lean_object* v_s_619_, lean_object* v_pos_620_, lean_object* v_inst_621_){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_622_ = lean_unsigned_to_nat(0u);
v___x_623_ = lean_string_utf8_byte_size(v_s_619_);
v___x_624_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_624_, 0, v_s_619_);
lean_ctor_set(v___x_624_, 1, v___x_622_);
lean_ctor_set(v___x_624_, 2, v___x_623_);
v___x_625_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_624_, v_pos_620_, v_inst_621_);
lean_dec_ref_known(v___x_624_, 3);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_revSkipWhile(lean_object* v_00_u03c1_626_, lean_object* v_s_627_, lean_object* v_pos_628_, lean_object* v_pat_629_, lean_object* v_inst_630_){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_631_ = lean_unsigned_to_nat(0u);
v___x_632_ = lean_string_utf8_byte_size(v_s_627_);
v___x_633_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_633_, 0, v_s_627_);
lean_ctor_set(v___x_633_, 1, v___x_631_);
lean_ctor_set(v___x_633_, 2, v___x_632_);
v___x_634_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_633_, v_pos_628_, v_inst_630_);
lean_dec_ref_known(v___x_633_, 3);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_revSkipWhile___boxed(lean_object* v_00_u03c1_635_, lean_object* v_s_636_, lean_object* v_pos_637_, lean_object* v_pat_638_, lean_object* v_inst_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_String_Pos_revSkipWhile(v_00_u03c1_635_, v_s_636_, v_pos_637_, v_pat_638_, v_inst_639_);
lean_dec(v_pat_638_);
return v_res_640_;
}
}
static lean_object* _init_l_String_trimAsciiEnd___closed__1(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = ((lean_object*)(l_String_trimAsciiEnd___closed__0));
v___x_643_ = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool(v___x_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_String_trimAsciiEnd(lean_object* v_s_644_){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_646_ = lean_string_utf8_byte_size(v_s_644_);
lean_inc_ref(v_s_644_);
v___x_647_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_647_, 0, v_s_644_);
lean_ctor_set(v___x_647_, 1, v___x_645_);
lean_ctor_set(v___x_647_, 2, v___x_646_);
v___x_648_ = lean_obj_once(&l_String_trimAsciiEnd___closed__1, &l_String_trimAsciiEnd___closed__1_once, _init_l_String_trimAsciiEnd___closed__1);
v___x_649_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_647_, v___x_646_, v___x_648_);
lean_dec_ref_known(v___x_647_, 3);
v___x_650_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_650_, 0, v_s_644_);
lean_ctor_set(v___x_650_, 1, v___x_645_);
lean_ctor_set(v___x_650_, 2, v___x_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimRight_spec__0(lean_object* v_s_651_, lean_object* v_pos_652_){
_start:
{
lean_object* v_str_653_; lean_object* v_startInclusive_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v_decide_658_; 
v_str_653_ = lean_ctor_get(v_s_651_, 0);
v_startInclusive_654_ = lean_ctor_get(v_s_651_, 1);
v___x_655_ = lean_nat_add(v_startInclusive_654_, v_pos_652_);
v___x_656_ = lean_nat_sub(v___x_655_, v_startInclusive_654_);
v___x_657_ = lean_unsigned_to_nat(0u);
v_decide_658_ = lean_nat_dec_eq(v___x_656_, v___x_657_);
if (v_decide_658_ == 0)
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_667_; uint32_t v___x_668_; uint32_t v___x_669_; uint8_t v___x_670_; 
lean_inc(v_startInclusive_654_);
lean_inc_ref(v_str_653_);
v___x_659_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_659_, 0, v_str_653_);
lean_ctor_set(v___x_659_, 1, v_startInclusive_654_);
lean_ctor_set(v___x_659_, 2, v___x_655_);
v___x_660_ = lean_unsigned_to_nat(1u);
v___x_661_ = lean_nat_sub(v___x_656_, v___x_660_);
lean_dec(v___x_656_);
v___x_662_ = l_String_Slice_posLE(v___x_659_, v___x_661_);
lean_dec_ref_known(v___x_659_, 3);
v___x_667_ = lean_nat_add(v_startInclusive_654_, v___x_662_);
v___x_668_ = lean_string_utf8_get_fast(v_str_653_, v___x_667_);
lean_dec(v___x_667_);
v___x_669_ = 32;
v___x_670_ = lean_uint32_dec_eq(v___x_668_, v___x_669_);
if (v___x_670_ == 0)
{
uint32_t v___x_671_; uint8_t v___x_672_; 
v___x_671_ = 9;
v___x_672_ = lean_uint32_dec_eq(v___x_668_, v___x_671_);
if (v___x_672_ == 0)
{
uint32_t v___x_673_; uint8_t v___x_674_; 
v___x_673_ = 13;
v___x_674_ = lean_uint32_dec_eq(v___x_668_, v___x_673_);
if (v___x_674_ == 0)
{
uint32_t v___x_675_; uint8_t v___x_676_; 
v___x_675_ = 10;
v___x_676_ = lean_uint32_dec_eq(v___x_668_, v___x_675_);
if (v___x_676_ == 0)
{
lean_dec(v___x_662_);
return v_pos_652_;
}
else
{
goto v___jp_663_;
}
}
else
{
goto v___jp_663_;
}
}
else
{
goto v___jp_663_;
}
}
else
{
goto v___jp_663_;
}
v___jp_663_:
{
lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_664_ = lean_nat_add(v___x_662_, v___x_660_);
v___x_665_ = lean_nat_dec_le(v___x_664_, v_pos_652_);
lean_dec(v___x_664_);
if (v___x_665_ == 0)
{
lean_dec(v___x_662_);
return v_pos_652_;
}
else
{
lean_dec(v_pos_652_);
v_pos_652_ = v___x_662_;
goto _start;
}
}
}
else
{
lean_dec(v___x_656_);
lean_dec(v___x_655_);
return v_pos_652_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimRight_spec__0___boxed(lean_object* v_s_677_, lean_object* v_pos_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimRight_spec__0(v_s_677_, v_pos_678_);
lean_dec_ref(v_s_677_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimRight(lean_object* v_s_680_){
_start:
{
lean_object* v_str_681_; lean_object* v_startInclusive_682_; lean_object* v_endExclusive_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_693_; 
v_str_681_ = lean_ctor_get(v_s_680_, 0);
lean_inc_ref(v_str_681_);
v_startInclusive_682_ = lean_ctor_get(v_s_680_, 1);
lean_inc(v_startInclusive_682_);
v_endExclusive_683_ = lean_ctor_get(v_s_680_, 2);
v___x_684_ = lean_nat_sub(v_endExclusive_683_, v_startInclusive_682_);
v___x_685_ = l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimRight_spec__0(v_s_680_, v___x_684_);
v_isSharedCheck_693_ = !lean_is_exclusive(v_s_680_);
if (v_isSharedCheck_693_ == 0)
{
lean_object* v_unused_694_; lean_object* v_unused_695_; lean_object* v_unused_696_; 
v_unused_694_ = lean_ctor_get(v_s_680_, 2);
lean_dec(v_unused_694_);
v_unused_695_ = lean_ctor_get(v_s_680_, 1);
lean_dec(v_unused_695_);
v_unused_696_ = lean_ctor_get(v_s_680_, 0);
lean_dec(v_unused_696_);
v___x_687_ = v_s_680_;
v_isShared_688_ = v_isSharedCheck_693_;
goto v_resetjp_686_;
}
else
{
lean_dec(v_s_680_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_693_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_689_ = lean_nat_add(v_startInclusive_682_, v___x_685_);
lean_dec(v___x_685_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 2, v___x_689_);
v___x_691_ = v___x_687_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_str_681_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_startInclusive_682_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v___x_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
static lean_object* _init_l_String_trimAsciiStart___closed__0(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = ((lean_object*)(l_String_trimAsciiEnd___closed__0));
v___x_698_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_String_trimAsciiStart(lean_object* v_s_699_){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_700_ = lean_unsigned_to_nat(0u);
v___x_701_ = lean_string_utf8_byte_size(v_s_699_);
lean_inc_ref(v_s_699_);
v___x_702_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_702_, 0, v_s_699_);
lean_ctor_set(v___x_702_, 1, v___x_700_);
lean_ctor_set(v___x_702_, 2, v___x_701_);
v___x_703_ = lean_obj_once(&l_String_trimAsciiStart___closed__0, &l_String_trimAsciiStart___closed__0_once, _init_l_String_trimAsciiStart___closed__0);
v___x_704_ = l_String_Slice_Pos_skipWhile___redArg(v___x_702_, v___x_700_, v___x_703_);
lean_dec_ref_known(v___x_702_, 3);
v___x_705_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_705_, 0, v_s_699_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
lean_ctor_set(v___x_705_, 2, v___x_701_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00String_Slice_trimLeft_spec__0(lean_object* v_s_706_, lean_object* v_pos_707_){
_start:
{
lean_object* v_str_708_; lean_object* v_startInclusive_709_; lean_object* v_endExclusive_710_; lean_object* v___x_711_; lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v_decide_722_; 
v_str_708_ = lean_ctor_get(v_s_706_, 0);
v_startInclusive_709_ = lean_ctor_get(v_s_706_, 1);
v_endExclusive_710_ = lean_ctor_get(v_s_706_, 2);
v___x_711_ = lean_nat_add(v_startInclusive_709_, v_pos_707_);
v___x_720_ = lean_unsigned_to_nat(0u);
v___x_721_ = lean_nat_sub(v_endExclusive_710_, v___x_711_);
v_decide_722_ = lean_nat_dec_eq(v___x_720_, v___x_721_);
lean_dec(v___x_721_);
if (v_decide_722_ == 0)
{
uint32_t v___x_723_; uint32_t v___x_724_; uint8_t v___x_725_; 
v___x_723_ = lean_string_utf8_get_fast(v_str_708_, v___x_711_);
v___x_724_ = 32;
v___x_725_ = lean_uint32_dec_eq(v___x_723_, v___x_724_);
if (v___x_725_ == 0)
{
uint32_t v___x_726_; uint8_t v___x_727_; 
v___x_726_ = 9;
v___x_727_ = lean_uint32_dec_eq(v___x_723_, v___x_726_);
if (v___x_727_ == 0)
{
uint32_t v___x_728_; uint8_t v___x_729_; 
v___x_728_ = 13;
v___x_729_ = lean_uint32_dec_eq(v___x_723_, v___x_728_);
if (v___x_729_ == 0)
{
uint32_t v___x_730_; uint8_t v___x_731_; 
v___x_730_ = 10;
v___x_731_ = lean_uint32_dec_eq(v___x_723_, v___x_730_);
if (v___x_731_ == 0)
{
lean_dec(v___x_711_);
return v_pos_707_;
}
else
{
goto v___jp_712_;
}
}
else
{
goto v___jp_712_;
}
}
else
{
goto v___jp_712_;
}
}
else
{
goto v___jp_712_;
}
}
else
{
lean_dec(v___x_711_);
return v_pos_707_;
}
v___jp_712_:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_713_ = lean_string_utf8_next_fast(v_str_708_, v___x_711_);
v___x_714_ = lean_nat_sub(v___x_713_, v___x_711_);
lean_dec(v___x_711_);
v___x_715_ = lean_nat_add(v_pos_707_, v___x_714_);
lean_dec(v___x_714_);
v___x_716_ = lean_unsigned_to_nat(1u);
v___x_717_ = lean_nat_add(v_pos_707_, v___x_716_);
v___x_718_ = lean_nat_dec_le(v___x_717_, v___x_715_);
lean_dec(v___x_717_);
if (v___x_718_ == 0)
{
lean_dec(v___x_715_);
return v_pos_707_;
}
else
{
lean_dec(v_pos_707_);
v_pos_707_ = v___x_715_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00String_Slice_trimLeft_spec__0___boxed(lean_object* v_s_732_, lean_object* v_pos_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_String_Slice_Pos_skipWhile___at___00String_Slice_trimLeft_spec__0(v_s_732_, v_pos_733_);
lean_dec_ref(v_s_732_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimLeft(lean_object* v_s_735_){
_start:
{
lean_object* v_str_736_; lean_object* v_startInclusive_737_; lean_object* v_endExclusive_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_748_; 
v_str_736_ = lean_ctor_get(v_s_735_, 0);
lean_inc_ref(v_str_736_);
v_startInclusive_737_ = lean_ctor_get(v_s_735_, 1);
lean_inc(v_startInclusive_737_);
v_endExclusive_738_ = lean_ctor_get(v_s_735_, 2);
lean_inc(v_endExclusive_738_);
v___x_739_ = lean_unsigned_to_nat(0u);
v___x_740_ = l_String_Slice_Pos_skipWhile___at___00String_Slice_trimLeft_spec__0(v_s_735_, v___x_739_);
v_isSharedCheck_748_ = !lean_is_exclusive(v_s_735_);
if (v_isSharedCheck_748_ == 0)
{
lean_object* v_unused_749_; lean_object* v_unused_750_; lean_object* v_unused_751_; 
v_unused_749_ = lean_ctor_get(v_s_735_, 2);
lean_dec(v_unused_749_);
v_unused_750_ = lean_ctor_get(v_s_735_, 1);
lean_dec(v_unused_750_);
v_unused_751_ = lean_ctor_get(v_s_735_, 0);
lean_dec(v_unused_751_);
v___x_742_ = v_s_735_;
v_isShared_743_ = v_isSharedCheck_748_;
goto v_resetjp_741_;
}
else
{
lean_dec(v_s_735_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_748_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_744_; lean_object* v___x_746_; 
v___x_744_ = lean_nat_add(v_startInclusive_737_, v___x_740_);
lean_dec(v___x_740_);
lean_dec(v_startInclusive_737_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 1, v___x_744_);
v___x_746_ = v___x_742_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_str_736_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v___x_744_);
lean_ctor_set(v_reuseFailAlloc_747_, 2, v_endExclusive_738_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_trimAscii(lean_object* v_s_752_){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_753_ = lean_unsigned_to_nat(0u);
v___x_754_ = lean_string_utf8_byte_size(v_s_752_);
v___x_755_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_755_, 0, v_s_752_);
lean_ctor_set(v___x_755_, 1, v___x_753_);
lean_ctor_set(v___x_755_, 2, v___x_754_);
v___x_756_ = l_String_Slice_trimAscii(v___x_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trim(lean_object* v_s_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_String_Slice_trimAscii(v_s_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* lean_string_trim(lean_object* v_s_759_){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v_str_764_; lean_object* v_startInclusive_765_; lean_object* v_endExclusive_766_; lean_object* v___x_767_; 
v___x_760_ = lean_unsigned_to_nat(0u);
v___x_761_ = lean_string_utf8_byte_size(v_s_759_);
v___x_762_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_762_, 0, v_s_759_);
lean_ctor_set(v___x_762_, 1, v___x_760_);
lean_ctor_set(v___x_762_, 2, v___x_761_);
v___x_763_ = l_String_Slice_trimAscii(v___x_762_);
v_str_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc_ref(v_str_764_);
v_startInclusive_765_ = lean_ctor_get(v___x_763_, 1);
lean_inc(v_startInclusive_765_);
v_endExclusive_766_ = lean_ctor_get(v___x_763_, 2);
lean_inc(v_endExclusive_766_);
lean_dec_ref(v___x_763_);
v___x_767_ = lean_string_utf8_extract_fast(v_str_764_, v_startInclusive_765_, v_endExclusive_766_);
lean_dec(v_endExclusive_766_);
lean_dec(v_startInclusive_765_);
lean_dec_ref(v_str_764_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextWhile(lean_object* v_s_768_, lean_object* v_p_769_, lean_object* v_i_770_){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = lean_string_utf8_byte_size(v_s_768_);
v___x_772_ = l_Substring_Raw_takeWhileAux(v_s_768_, v___x_771_, v_p_769_, v_i_770_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextWhile___boxed(lean_object* v_s_773_, lean_object* v_p_774_, lean_object* v_i_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_String_Pos_Raw_nextWhile(v_s_773_, v_p_774_, v_i_775_);
lean_dec_ref(v_s_773_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_String_nextWhile(lean_object* v_s_777_, lean_object* v_p_778_, lean_object* v_i_779_){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_string_utf8_byte_size(v_s_777_);
v___x_781_ = l_Substring_Raw_takeWhileAux(v_s_777_, v___x_780_, v_p_778_, v_i_779_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_String_nextWhile___boxed(lean_object* v_s_782_, lean_object* v_p_783_, lean_object* v_i_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_String_nextWhile(v_s_782_, v_p_783_, v_i_784_);
lean_dec_ref(v_s_782_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0(lean_object* v_p_786_, lean_object* v_s_787_, lean_object* v_stopPos_788_, lean_object* v_i_789_){
_start:
{
uint8_t v___y_791_; lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
v___x_794_ = lean_unsigned_to_nat(1u);
v___x_795_ = lean_nat_add(v_i_789_, v___x_794_);
v___x_796_ = lean_nat_dec_le(v___x_795_, v_stopPos_788_);
lean_dec(v___x_795_);
if (v___x_796_ == 0)
{
lean_dec_ref(v_p_786_);
return v_i_789_;
}
else
{
if (v___x_796_ == 0)
{
v___y_791_ = v___x_796_;
goto v___jp_790_;
}
else
{
uint32_t v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v___x_800_; 
v___x_797_ = lean_string_utf8_get(v_s_787_, v_i_789_);
v___x_798_ = lean_box_uint32(v___x_797_);
lean_inc_ref(v_p_786_);
v___x_799_ = lean_apply_1(v_p_786_, v___x_798_);
v___x_800_ = lean_unbox(v___x_799_);
v___y_791_ = v___x_800_;
goto v___jp_790_;
}
}
v___jp_790_:
{
if (v___y_791_ == 0)
{
lean_dec_ref(v_p_786_);
return v_i_789_;
}
else
{
lean_object* v___x_792_; 
v___x_792_ = lean_string_utf8_next(v_s_787_, v_i_789_);
lean_dec(v_i_789_);
v_i_789_ = v___x_792_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0___boxed(lean_object* v_p_801_, lean_object* v_s_802_, lean_object* v_stopPos_803_, lean_object* v_i_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0(v_p_801_, v_s_802_, v_stopPos_803_, v_i_804_);
lean_dec(v_stopPos_803_);
lean_dec_ref(v_s_802_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* lean_string_nextwhile(lean_object* v_s_806_, lean_object* v_p_807_, lean_object* v_i_808_){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = lean_string_utf8_byte_size(v_s_806_);
v___x_810_ = l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0(v_p_807_, v_s_806_, v___x_809_, v_i_808_);
lean_dec_ref(v_s_806_);
return v___x_810_;
}
}
uint8_t l_String_Pos_Raw_nextUntil___lam__0(lean_object* v_p_811_, uint32_t v_c_812_){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; uint8_t v___x_815_; 
v___x_813_ = lean_box_uint32(v_c_812_);
v___x_814_ = lean_apply_1(v_p_811_, v___x_813_);
v___x_815_ = lean_unbox(v___x_814_);
if (v___x_815_ == 0)
{
uint8_t v___x_816_; 
v___x_816_ = 1;
return v___x_816_;
}
else
{
uint8_t v___x_817_; 
v___x_817_ = 0;
return v___x_817_;
}
}
}
LEAN_EXPORT void l_String_Pos_Raw_nextUntil___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_811_ = stack[0].m_obj;
uint32_t v_c_812_ = stack[1].m_num;
uint8_t v_res_818_;
v_res_818_ = l_String_Pos_Raw_nextUntil___lam__0(v_p_811_, v_c_812_);
stack->m_num = v_res_818_;
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextUntil___lam__0___boxed(lean_object* v_p_819_, lean_object* v_c_820_){
_start:
{
uint32_t v_c_boxed_821_; uint8_t v_res_822_; lean_object* v_r_823_; 
v_c_boxed_821_ = lean_unbox_uint32(v_c_820_);
lean_dec(v_c_820_);
v_res_822_ = l_String_Pos_Raw_nextUntil___lam__0(v_p_819_, v_c_boxed_821_);
v_r_823_ = lean_box(v_res_822_);
return v_r_823_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextUntil(lean_object* v_s_824_, lean_object* v_p_825_, lean_object* v_i_826_){
_start:
{
lean_object* v___f_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___f_827_ = lean_alloc_closure((void*)(l_String_Pos_Raw_nextUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_827_, 0, v_p_825_);
v___x_828_ = lean_string_utf8_byte_size(v_s_824_);
v___x_829_ = l_Substring_Raw_takeWhileAux(v_s_824_, v___x_828_, v___f_827_, v_i_826_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextUntil___boxed(lean_object* v_s_830_, lean_object* v_p_831_, lean_object* v_i_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_String_Pos_Raw_nextUntil(v_s_830_, v_p_831_, v_i_832_);
lean_dec_ref(v_s_830_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0(lean_object* v_p_834_, lean_object* v_s_835_, lean_object* v_stopPos_836_, lean_object* v_i_837_){
_start:
{
uint8_t v___y_839_; lean_object* v___x_842_; lean_object* v___x_843_; uint8_t v___x_844_; 
v___x_842_ = lean_unsigned_to_nat(1u);
v___x_843_ = lean_nat_add(v_i_837_, v___x_842_);
v___x_844_ = lean_nat_dec_le(v___x_843_, v_stopPos_836_);
lean_dec(v___x_843_);
if (v___x_844_ == 0)
{
lean_dec_ref(v_p_834_);
return v_i_837_;
}
else
{
if (v___x_844_ == 0)
{
v___y_839_ = v___x_844_;
goto v___jp_838_;
}
else
{
uint32_t v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; uint8_t v___x_848_; 
v___x_845_ = lean_string_utf8_get(v_s_835_, v_i_837_);
v___x_846_ = lean_box_uint32(v___x_845_);
lean_inc_ref(v_p_834_);
v___x_847_ = lean_apply_1(v_p_834_, v___x_846_);
v___x_848_ = lean_unbox(v___x_847_);
if (v___x_848_ == 0)
{
v___y_839_ = v___x_844_;
goto v___jp_838_;
}
else
{
lean_dec_ref(v_p_834_);
return v_i_837_;
}
}
}
v___jp_838_:
{
if (v___y_839_ == 0)
{
lean_dec_ref(v_p_834_);
return v_i_837_;
}
else
{
lean_object* v___x_840_; 
v___x_840_ = lean_string_utf8_next(v_s_835_, v_i_837_);
lean_dec(v_i_837_);
v_i_837_ = v___x_840_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0___boxed(lean_object* v_p_849_, lean_object* v_s_850_, lean_object* v_stopPos_851_, lean_object* v_i_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0(v_p_849_, v_s_850_, v_stopPos_851_, v_i_852_);
lean_dec(v_stopPos_851_);
lean_dec_ref(v_s_850_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_String_nextUntil(lean_object* v_s_854_, lean_object* v_p_855_, lean_object* v_i_856_){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = lean_string_utf8_byte_size(v_s_854_);
v___x_858_ = l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0(v_p_855_, v_s_854_, v___x_857_, v_i_856_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_String_nextUntil___boxed(lean_object* v_s_859_, lean_object* v_p_860_, lean_object* v_i_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_String_nextUntil(v_s_859_, v_p_860_, v_i_861_);
lean_dec_ref(v_s_859_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___redArg(lean_object* v_s_863_, lean_object* v_inst_864_){
_start:
{
lean_object* v_skipPrefix_x3f_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_885_; 
v_skipPrefix_x3f_865_ = lean_ctor_get(v_inst_864_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v_inst_864_);
if (v_isSharedCheck_885_ == 0)
{
lean_object* v_unused_886_; lean_object* v_unused_887_; 
v_unused_886_ = lean_ctor_get(v_inst_864_, 2);
lean_dec(v_unused_886_);
v_unused_887_ = lean_ctor_get(v_inst_864_, 1);
lean_dec(v_unused_887_);
v___x_867_ = v_inst_864_;
v_isShared_868_ = v_isSharedCheck_885_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_skipPrefix_x3f_865_);
lean_dec(v_inst_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_885_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_869_ = lean_string_utf8_byte_size(v_s_863_);
v___x_870_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_s_863_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 2, v___x_869_);
lean_ctor_set(v___x_867_, 1, v___x_870_);
lean_ctor_set(v___x_867_, 0, v_s_863_);
v___x_872_ = v___x_867_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_s_863_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v___x_870_);
lean_ctor_set(v_reuseFailAlloc_884_, 2, v___x_869_);
v___x_872_ = v_reuseFailAlloc_884_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_873_; 
v___x_873_ = lean_apply_1(v_skipPrefix_x3f_865_, v___x_872_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v___x_874_; 
lean_dec_ref(v_s_863_);
v___x_874_ = lean_box(0);
return v___x_874_;
}
else
{
lean_object* v_val_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_883_; 
v_val_875_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_883_ == 0)
{
v___x_877_ = v___x_873_;
v_isShared_878_ = v_isSharedCheck_883_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_val_875_);
lean_dec(v___x_873_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_883_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_879_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_879_, 0, v_s_863_);
lean_ctor_set(v___x_879_, 1, v_val_875_);
lean_ctor_set(v___x_879_, 2, v___x_869_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_879_);
v___x_881_ = v___x_877_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_879_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f(lean_object* v_00_u03c1_888_, lean_object* v_s_889_, lean_object* v_pat_890_, lean_object* v_inst_891_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l_String_dropPrefix_x3f___redArg(v_s_889_, v_inst_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___boxed(lean_object* v_00_u03c1_893_, lean_object* v_s_894_, lean_object* v_pat_895_, lean_object* v_inst_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_String_dropPrefix_x3f(v_00_u03c1_893_, v_s_894_, v_pat_895_, v_inst_896_);
lean_dec(v_pat_895_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___redArg(lean_object* v_s_898_, lean_object* v_inst_899_){
_start:
{
lean_object* v_skipSuffix_x3f_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_920_; 
v_skipSuffix_x3f_900_ = lean_ctor_get(v_inst_899_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v_inst_899_);
if (v_isSharedCheck_920_ == 0)
{
lean_object* v_unused_921_; lean_object* v_unused_922_; 
v_unused_921_ = lean_ctor_get(v_inst_899_, 2);
lean_dec(v_unused_921_);
v_unused_922_ = lean_ctor_get(v_inst_899_, 1);
lean_dec(v_unused_922_);
v___x_902_ = v_inst_899_;
v_isShared_903_ = v_isSharedCheck_920_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_skipSuffix_x3f_900_);
lean_dec(v_inst_899_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_920_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_907_; 
v___x_904_ = lean_string_utf8_byte_size(v_s_898_);
v___x_905_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_s_898_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 2, v___x_904_);
lean_ctor_set(v___x_902_, 1, v___x_905_);
lean_ctor_set(v___x_902_, 0, v_s_898_);
v___x_907_ = v___x_902_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_s_898_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v___x_905_);
lean_ctor_set(v_reuseFailAlloc_919_, 2, v___x_904_);
v___x_907_ = v_reuseFailAlloc_919_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
lean_object* v___x_908_; 
v___x_908_ = lean_apply_1(v_skipSuffix_x3f_900_, v___x_907_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v___x_909_; 
lean_dec_ref(v_s_898_);
v___x_909_ = lean_box(0);
return v___x_909_;
}
else
{
lean_object* v_val_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_918_; 
v_val_910_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_918_ == 0)
{
v___x_912_ = v___x_908_;
v_isShared_913_ = v_isSharedCheck_918_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_val_910_);
lean_dec(v___x_908_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_918_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_914_; lean_object* v___x_916_; 
v___x_914_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_914_, 0, v_s_898_);
lean_ctor_set(v___x_914_, 1, v___x_905_);
lean_ctor_set(v___x_914_, 2, v_val_910_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v___x_914_);
v___x_916_ = v___x_912_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_914_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f(lean_object* v_00_u03c1_923_, lean_object* v_s_924_, lean_object* v_pat_925_, lean_object* v_inst_926_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_String_dropSuffix_x3f___redArg(v_s_924_, v_inst_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___boxed(lean_object* v_00_u03c1_928_, lean_object* v_s_929_, lean_object* v_pat_930_, lean_object* v_inst_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_String_dropSuffix_x3f(v_00_u03c1_928_, v_s_929_, v_pat_930_, v_inst_931_);
lean_dec(v_pat_930_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix___redArg(lean_object* v_s_933_, lean_object* v_inst_934_){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_935_ = lean_unsigned_to_nat(0u);
v___x_936_ = lean_string_utf8_byte_size(v_s_933_);
v___x_937_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_937_, 0, v_s_933_);
lean_ctor_set(v___x_937_, 1, v___x_935_);
lean_ctor_set(v___x_937_, 2, v___x_936_);
v___x_938_ = l_String_Slice_dropPrefix___redArg(v___x_937_, v_inst_934_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix(lean_object* v_00_u03c1_939_, lean_object* v_s_940_, lean_object* v_pat_941_, lean_object* v_inst_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_String_dropPrefix___redArg(v_s_940_, v_inst_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix___boxed(lean_object* v_00_u03c1_944_, lean_object* v_s_945_, lean_object* v_pat_946_, lean_object* v_inst_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_String_dropPrefix(v_00_u03c1_944_, v_s_945_, v_pat_946_, v_inst_947_);
lean_dec(v_pat_946_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg(lean_object* v_pre_949_, lean_object* v_s_950_){
_start:
{
lean_object* v_str_951_; lean_object* v_startInclusive_952_; lean_object* v_endExclusive_953_; lean_object* v___x_954_; lean_object* v___x_955_; uint8_t v___x_956_; 
v_str_951_ = lean_ctor_get(v_s_950_, 0);
v_startInclusive_952_ = lean_ctor_get(v_s_950_, 1);
v_endExclusive_953_ = lean_ctor_get(v_s_950_, 2);
v___x_954_ = lean_string_utf8_byte_size(v_pre_949_);
v___x_955_ = lean_nat_sub(v_endExclusive_953_, v_startInclusive_952_);
v___x_956_ = lean_nat_dec_le(v___x_954_, v___x_955_);
lean_dec(v___x_955_);
if (v___x_956_ == 0)
{
return v_s_950_;
}
else
{
lean_object* v___x_957_; uint8_t v___x_958_; 
v___x_957_ = lean_unsigned_to_nat(0u);
v___x_958_ = lean_string_memcmp(v_str_951_, v_pre_949_, v_startInclusive_952_, v___x_957_, v___x_954_);
if (v___x_958_ == 0)
{
return v_s_950_;
}
else
{
lean_object* v___x_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_967_; 
lean_inc(v_endExclusive_953_);
lean_inc(v_startInclusive_952_);
lean_inc_ref(v_str_951_);
v___x_959_ = l_String_Slice_pos_x21(v_s_950_, v___x_954_);
v_isSharedCheck_967_ = !lean_is_exclusive(v_s_950_);
if (v_isSharedCheck_967_ == 0)
{
lean_object* v_unused_968_; lean_object* v_unused_969_; lean_object* v_unused_970_; 
v_unused_968_ = lean_ctor_get(v_s_950_, 2);
lean_dec(v_unused_968_);
v_unused_969_ = lean_ctor_get(v_s_950_, 1);
lean_dec(v_unused_969_);
v_unused_970_ = lean_ctor_get(v_s_950_, 0);
lean_dec(v_unused_970_);
v___x_961_ = v_s_950_;
v_isShared_962_ = v_isSharedCheck_967_;
goto v_resetjp_960_;
}
else
{
lean_dec(v_s_950_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_967_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_963_; lean_object* v___x_965_; 
v___x_963_ = lean_nat_add(v_startInclusive_952_, v___x_959_);
lean_dec(v___x_959_);
lean_dec(v_startInclusive_952_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 1, v___x_963_);
v___x_965_ = v___x_961_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_str_951_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v___x_963_);
lean_ctor_set(v_reuseFailAlloc_966_, 2, v_endExclusive_953_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg___boxed(lean_object* v_pre_971_, lean_object* v_s_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg(v_pre_971_, v_s_972_);
lean_dec_ref(v_pre_971_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix___at___00String_stripPrefix_spec__0(lean_object* v_pre_974_, lean_object* v_s_975_, lean_object* v_pat_976_){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_977_ = lean_unsigned_to_nat(0u);
v___x_978_ = lean_string_utf8_byte_size(v_s_975_);
v___x_979_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_979_, 0, v_s_975_);
lean_ctor_set(v___x_979_, 1, v___x_977_);
lean_ctor_set(v___x_979_, 2, v___x_978_);
v___x_980_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg(v_pre_974_, v___x_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix___at___00String_stripPrefix_spec__0___boxed(lean_object* v_pre_981_, lean_object* v_s_982_, lean_object* v_pat_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_String_dropPrefix___at___00String_stripPrefix_spec__0(v_pre_981_, v_s_982_, v_pat_983_);
lean_dec_ref(v_pat_983_);
lean_dec_ref(v_pre_981_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_String_stripPrefix(lean_object* v_s_985_, lean_object* v_pre_986_){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = l_String_dropPrefix___at___00String_stripPrefix_spec__0(v_pre_986_, v_s_985_, v_pre_986_);
v___x_988_ = l_String_Slice_toString(v___x_987_);
lean_dec_ref(v___x_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_String_stripPrefix___boxed(lean_object* v_s_989_, lean_object* v_pre_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_String_stripPrefix(v_s_989_, v_pre_990_);
lean_dec_ref(v_pre_990_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0(lean_object* v_pat_992_, lean_object* v_pre_993_, lean_object* v_s_994_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg(v_pre_993_, v_s_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___boxed(lean_object* v_pat_996_, lean_object* v_pre_997_, lean_object* v_s_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0(v_pat_996_, v_pre_997_, v_s_998_);
lean_dec_ref(v_pre_997_);
lean_dec_ref(v_pat_996_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix___redArg(lean_object* v_s_1000_, lean_object* v_inst_1001_){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1002_ = lean_unsigned_to_nat(0u);
v___x_1003_ = lean_string_utf8_byte_size(v_s_1000_);
v___x_1004_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1004_, 0, v_s_1000_);
lean_ctor_set(v___x_1004_, 1, v___x_1002_);
lean_ctor_set(v___x_1004_, 2, v___x_1003_);
v___x_1005_ = l_String_Slice_dropSuffix___redArg(v___x_1004_, v_inst_1001_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix(lean_object* v_00_u03c1_1006_, lean_object* v_s_1007_, lean_object* v_pat_1008_, lean_object* v_inst_1009_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l_String_dropSuffix___redArg(v_s_1007_, v_inst_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix___boxed(lean_object* v_00_u03c1_1011_, lean_object* v_s_1012_, lean_object* v_pat_1013_, lean_object* v_inst_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_String_dropSuffix(v_00_u03c1_1011_, v_s_1012_, v_pat_1013_, v_inst_1014_);
lean_dec(v_pat_1013_);
return v_res_1015_;
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

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
LEAN_EXPORT uint8_t l_String_all___redArg(lean_object* v_s_237_, lean_object* v_inst_238_){
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
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; uint8_t v_decide_256_; 
v___x_252_ = lean_unsigned_to_nat(0u);
v___x_253_ = lean_string_utf8_byte_size(v_s_249_);
v___x_254_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_254_, 0, v_s_249_);
lean_ctor_set(v___x_254_, 1, v___x_252_);
lean_ctor_set(v___x_254_, 2, v___x_253_);
v___x_255_ = l_String_Slice_Pos_skipWhile___redArg(v___x_254_, v___x_252_, v_inst_251_);
lean_dec_ref_known(v___x_254_, 3);
v_decide_256_ = lean_nat_dec_eq(v___x_255_, v___x_253_);
lean_dec(v___x_255_);
return v_decide_256_;
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
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; uint8_t v_decide_269_; 
v___x_265_ = lean_unsigned_to_nat(0u);
v___x_266_ = lean_string_utf8_byte_size(v_s_263_);
v___x_267_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_267_, 0, v_s_263_);
lean_ctor_set(v___x_267_, 1, v___x_265_);
lean_ctor_set(v___x_267_, 2, v___x_266_);
v___x_268_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_267_, v___x_266_, v_inst_264_);
lean_dec_ref_known(v___x_267_, 3);
v_decide_269_ = lean_nat_dec_eq(v___x_268_, v___x_265_);
lean_dec(v___x_268_);
return v_decide_269_;
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
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v_decide_282_; 
v___x_278_ = lean_unsigned_to_nat(0u);
v___x_279_ = lean_string_utf8_byte_size(v_s_275_);
v___x_280_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_280_, 0, v_s_275_);
lean_ctor_set(v___x_280_, 1, v___x_278_);
lean_ctor_set(v___x_280_, 2, v___x_279_);
v___x_281_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_280_, v___x_279_, v_inst_277_);
lean_dec_ref_known(v___x_280_, 3);
v_decide_282_ = lean_nat_dec_eq(v___x_281_, v___x_278_);
lean_dec(v___x_281_);
return v_decide_282_;
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
lean_object* v_str_643_; lean_object* v_startInclusive_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v_decide_648_; 
v_str_643_ = lean_ctor_get(v_s_641_, 0);
v_startInclusive_644_ = lean_ctor_get(v_s_641_, 1);
v___x_645_ = lean_nat_add(v_startInclusive_644_, v_pos_642_);
v___x_646_ = lean_nat_sub(v___x_645_, v_startInclusive_644_);
v___x_647_ = lean_unsigned_to_nat(0u);
v_decide_648_ = lean_nat_dec_eq(v___x_646_, v___x_647_);
if (v_decide_648_ == 0)
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_657_; uint32_t v___x_658_; uint32_t v___x_659_; uint8_t v___x_660_; 
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
v___x_657_ = lean_nat_add(v_startInclusive_644_, v___x_652_);
v___x_658_ = lean_string_utf8_get_fast(v_str_643_, v___x_657_);
lean_dec(v___x_657_);
v___x_659_ = 32;
v___x_660_ = lean_uint32_dec_eq(v___x_658_, v___x_659_);
if (v___x_660_ == 0)
{
uint32_t v___x_661_; uint8_t v___x_662_; 
v___x_661_ = 9;
v___x_662_ = lean_uint32_dec_eq(v___x_658_, v___x_661_);
if (v___x_662_ == 0)
{
uint32_t v___x_663_; uint8_t v___x_664_; 
v___x_663_ = 13;
v___x_664_ = lean_uint32_dec_eq(v___x_658_, v___x_663_);
if (v___x_664_ == 0)
{
uint32_t v___x_665_; uint8_t v___x_666_; 
v___x_665_ = 10;
v___x_666_ = lean_uint32_dec_eq(v___x_658_, v___x_665_);
if (v___x_666_ == 0)
{
lean_dec(v___x_652_);
return v_pos_642_;
}
else
{
goto v___jp_653_;
}
}
else
{
goto v___jp_653_;
}
}
else
{
goto v___jp_653_;
}
}
else
{
goto v___jp_653_;
}
v___jp_653_:
{
lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_654_ = lean_nat_add(v___x_652_, v___x_650_);
v___x_655_ = lean_nat_dec_le(v___x_654_, v_pos_642_);
lean_dec(v___x_654_);
if (v___x_655_ == 0)
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
}
else
{
lean_dec(v___x_646_);
lean_dec(v___x_645_);
return v_pos_642_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimRight_spec__0___boxed(lean_object* v_s_667_, lean_object* v_pos_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimRight_spec__0(v_s_667_, v_pos_668_);
lean_dec_ref(v_s_667_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimRight(lean_object* v_s_670_){
_start:
{
lean_object* v_str_671_; lean_object* v_startInclusive_672_; lean_object* v_endExclusive_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_683_; 
v_str_671_ = lean_ctor_get(v_s_670_, 0);
lean_inc_ref(v_str_671_);
v_startInclusive_672_ = lean_ctor_get(v_s_670_, 1);
lean_inc(v_startInclusive_672_);
v_endExclusive_673_ = lean_ctor_get(v_s_670_, 2);
v___x_674_ = lean_nat_sub(v_endExclusive_673_, v_startInclusive_672_);
v___x_675_ = l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimRight_spec__0(v_s_670_, v___x_674_);
v_isSharedCheck_683_ = !lean_is_exclusive(v_s_670_);
if (v_isSharedCheck_683_ == 0)
{
lean_object* v_unused_684_; lean_object* v_unused_685_; lean_object* v_unused_686_; 
v_unused_684_ = lean_ctor_get(v_s_670_, 2);
lean_dec(v_unused_684_);
v_unused_685_ = lean_ctor_get(v_s_670_, 1);
lean_dec(v_unused_685_);
v_unused_686_ = lean_ctor_get(v_s_670_, 0);
lean_dec(v_unused_686_);
v___x_677_ = v_s_670_;
v_isShared_678_ = v_isSharedCheck_683_;
goto v_resetjp_676_;
}
else
{
lean_dec(v_s_670_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_683_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_679_; lean_object* v___x_681_; 
v___x_679_ = lean_nat_add(v_startInclusive_672_, v___x_675_);
lean_dec(v___x_675_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 2, v___x_679_);
v___x_681_ = v___x_677_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_str_671_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_startInclusive_672_);
lean_ctor_set(v_reuseFailAlloc_682_, 2, v___x_679_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
static lean_object* _init_l_String_trimAsciiStart___closed__0(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = ((lean_object*)(l_String_trimAsciiEnd___closed__0));
v___x_688_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_String_trimAsciiStart(lean_object* v_s_689_){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_690_ = lean_unsigned_to_nat(0u);
v___x_691_ = lean_string_utf8_byte_size(v_s_689_);
lean_inc_ref(v_s_689_);
v___x_692_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_692_, 0, v_s_689_);
lean_ctor_set(v___x_692_, 1, v___x_690_);
lean_ctor_set(v___x_692_, 2, v___x_691_);
v___x_693_ = lean_obj_once(&l_String_trimAsciiStart___closed__0, &l_String_trimAsciiStart___closed__0_once, _init_l_String_trimAsciiStart___closed__0);
v___x_694_ = l_String_Slice_Pos_skipWhile___redArg(v___x_692_, v___x_690_, v___x_693_);
lean_dec_ref_known(v___x_692_, 3);
v___x_695_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_695_, 0, v_s_689_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
lean_ctor_set(v___x_695_, 2, v___x_691_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00String_Slice_trimLeft_spec__0(lean_object* v_s_696_, lean_object* v_pos_697_){
_start:
{
lean_object* v_str_698_; lean_object* v_startInclusive_699_; lean_object* v_endExclusive_700_; lean_object* v___x_701_; lean_object* v___x_710_; lean_object* v___x_711_; uint8_t v_decide_712_; 
v_str_698_ = lean_ctor_get(v_s_696_, 0);
v_startInclusive_699_ = lean_ctor_get(v_s_696_, 1);
v_endExclusive_700_ = lean_ctor_get(v_s_696_, 2);
v___x_701_ = lean_nat_add(v_startInclusive_699_, v_pos_697_);
v___x_710_ = lean_unsigned_to_nat(0u);
v___x_711_ = lean_nat_sub(v_endExclusive_700_, v___x_701_);
v_decide_712_ = lean_nat_dec_eq(v___x_710_, v___x_711_);
lean_dec(v___x_711_);
if (v_decide_712_ == 0)
{
uint32_t v___x_713_; uint32_t v___x_714_; uint8_t v___x_715_; 
v___x_713_ = lean_string_utf8_get_fast(v_str_698_, v___x_701_);
v___x_714_ = 32;
v___x_715_ = lean_uint32_dec_eq(v___x_713_, v___x_714_);
if (v___x_715_ == 0)
{
uint32_t v___x_716_; uint8_t v___x_717_; 
v___x_716_ = 9;
v___x_717_ = lean_uint32_dec_eq(v___x_713_, v___x_716_);
if (v___x_717_ == 0)
{
uint32_t v___x_718_; uint8_t v___x_719_; 
v___x_718_ = 13;
v___x_719_ = lean_uint32_dec_eq(v___x_713_, v___x_718_);
if (v___x_719_ == 0)
{
uint32_t v___x_720_; uint8_t v___x_721_; 
v___x_720_ = 10;
v___x_721_ = lean_uint32_dec_eq(v___x_713_, v___x_720_);
if (v___x_721_ == 0)
{
lean_dec(v___x_701_);
return v_pos_697_;
}
else
{
goto v___jp_702_;
}
}
else
{
goto v___jp_702_;
}
}
else
{
goto v___jp_702_;
}
}
else
{
goto v___jp_702_;
}
}
else
{
lean_dec(v___x_701_);
return v_pos_697_;
}
v___jp_702_:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_703_ = lean_string_utf8_next_fast(v_str_698_, v___x_701_);
v___x_704_ = lean_nat_sub(v___x_703_, v___x_701_);
lean_dec(v___x_701_);
v___x_705_ = lean_nat_add(v_pos_697_, v___x_704_);
lean_dec(v___x_704_);
v___x_706_ = lean_unsigned_to_nat(1u);
v___x_707_ = lean_nat_add(v_pos_697_, v___x_706_);
v___x_708_ = lean_nat_dec_le(v___x_707_, v___x_705_);
lean_dec(v___x_707_);
if (v___x_708_ == 0)
{
lean_dec(v___x_705_);
return v_pos_697_;
}
else
{
lean_dec(v_pos_697_);
v_pos_697_ = v___x_705_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00String_Slice_trimLeft_spec__0___boxed(lean_object* v_s_722_, lean_object* v_pos_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_String_Slice_Pos_skipWhile___at___00String_Slice_trimLeft_spec__0(v_s_722_, v_pos_723_);
lean_dec_ref(v_s_722_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimLeft(lean_object* v_s_725_){
_start:
{
lean_object* v_str_726_; lean_object* v_startInclusive_727_; lean_object* v_endExclusive_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_738_; 
v_str_726_ = lean_ctor_get(v_s_725_, 0);
lean_inc_ref(v_str_726_);
v_startInclusive_727_ = lean_ctor_get(v_s_725_, 1);
lean_inc(v_startInclusive_727_);
v_endExclusive_728_ = lean_ctor_get(v_s_725_, 2);
lean_inc(v_endExclusive_728_);
v___x_729_ = lean_unsigned_to_nat(0u);
v___x_730_ = l_String_Slice_Pos_skipWhile___at___00String_Slice_trimLeft_spec__0(v_s_725_, v___x_729_);
v_isSharedCheck_738_ = !lean_is_exclusive(v_s_725_);
if (v_isSharedCheck_738_ == 0)
{
lean_object* v_unused_739_; lean_object* v_unused_740_; lean_object* v_unused_741_; 
v_unused_739_ = lean_ctor_get(v_s_725_, 2);
lean_dec(v_unused_739_);
v_unused_740_ = lean_ctor_get(v_s_725_, 1);
lean_dec(v_unused_740_);
v_unused_741_ = lean_ctor_get(v_s_725_, 0);
lean_dec(v_unused_741_);
v___x_732_ = v_s_725_;
v_isShared_733_ = v_isSharedCheck_738_;
goto v_resetjp_731_;
}
else
{
lean_dec(v_s_725_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_738_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_734_; lean_object* v___x_736_; 
v___x_734_ = lean_nat_add(v_startInclusive_727_, v___x_730_);
lean_dec(v___x_730_);
lean_dec(v_startInclusive_727_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 1, v___x_734_);
v___x_736_ = v___x_732_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_str_726_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v___x_734_);
lean_ctor_set(v_reuseFailAlloc_737_, 2, v_endExclusive_728_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_trimAscii(lean_object* v_s_742_){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_743_ = lean_unsigned_to_nat(0u);
v___x_744_ = lean_string_utf8_byte_size(v_s_742_);
v___x_745_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_745_, 0, v_s_742_);
lean_ctor_set(v___x_745_, 1, v___x_743_);
lean_ctor_set(v___x_745_, 2, v___x_744_);
v___x_746_ = l_String_Slice_trimAscii(v___x_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trim(lean_object* v_s_747_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l_String_Slice_trimAscii(v_s_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* lean_string_trim(lean_object* v_s_749_){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v_str_754_; lean_object* v_startInclusive_755_; lean_object* v_endExclusive_756_; lean_object* v___x_757_; 
v___x_750_ = lean_unsigned_to_nat(0u);
v___x_751_ = lean_string_utf8_byte_size(v_s_749_);
v___x_752_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_752_, 0, v_s_749_);
lean_ctor_set(v___x_752_, 1, v___x_750_);
lean_ctor_set(v___x_752_, 2, v___x_751_);
v___x_753_ = l_String_Slice_trimAscii(v___x_752_);
v_str_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc_ref(v_str_754_);
v_startInclusive_755_ = lean_ctor_get(v___x_753_, 1);
lean_inc(v_startInclusive_755_);
v_endExclusive_756_ = lean_ctor_get(v___x_753_, 2);
lean_inc(v_endExclusive_756_);
lean_dec_ref(v___x_753_);
v___x_757_ = lean_string_utf8_extract_fast(v_str_754_, v_startInclusive_755_, v_endExclusive_756_);
lean_dec(v_endExclusive_756_);
lean_dec(v_startInclusive_755_);
lean_dec_ref(v_str_754_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextWhile(lean_object* v_s_758_, lean_object* v_p_759_, lean_object* v_i_760_){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = lean_string_utf8_byte_size(v_s_758_);
v___x_762_ = l_Substring_Raw_takeWhileAux(v_s_758_, v___x_761_, v_p_759_, v_i_760_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextWhile___boxed(lean_object* v_s_763_, lean_object* v_p_764_, lean_object* v_i_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_String_Pos_Raw_nextWhile(v_s_763_, v_p_764_, v_i_765_);
lean_dec_ref(v_s_763_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_String_nextWhile(lean_object* v_s_767_, lean_object* v_p_768_, lean_object* v_i_769_){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = lean_string_utf8_byte_size(v_s_767_);
v___x_771_ = l_Substring_Raw_takeWhileAux(v_s_767_, v___x_770_, v_p_768_, v_i_769_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_String_nextWhile___boxed(lean_object* v_s_772_, lean_object* v_p_773_, lean_object* v_i_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_String_nextWhile(v_s_772_, v_p_773_, v_i_774_);
lean_dec_ref(v_s_772_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0(lean_object* v_p_776_, lean_object* v_s_777_, lean_object* v_stopPos_778_, lean_object* v_i_779_){
_start:
{
uint8_t v___y_781_; lean_object* v___x_784_; lean_object* v___x_785_; uint8_t v___x_786_; 
v___x_784_ = lean_unsigned_to_nat(1u);
v___x_785_ = lean_nat_add(v_i_779_, v___x_784_);
v___x_786_ = lean_nat_dec_le(v___x_785_, v_stopPos_778_);
lean_dec(v___x_785_);
if (v___x_786_ == 0)
{
lean_dec_ref(v_p_776_);
return v_i_779_;
}
else
{
if (v___x_786_ == 0)
{
v___y_781_ = v___x_786_;
goto v___jp_780_;
}
else
{
uint32_t v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_787_ = lean_string_utf8_get(v_s_777_, v_i_779_);
v___x_788_ = lean_box_uint32(v___x_787_);
lean_inc_ref(v_p_776_);
v___x_789_ = lean_apply_1(v_p_776_, v___x_788_);
v___x_790_ = lean_unbox(v___x_789_);
v___y_781_ = v___x_790_;
goto v___jp_780_;
}
}
v___jp_780_:
{
if (v___y_781_ == 0)
{
lean_dec_ref(v_p_776_);
return v_i_779_;
}
else
{
lean_object* v___x_782_; 
v___x_782_ = lean_string_utf8_next(v_s_777_, v_i_779_);
lean_dec(v_i_779_);
v_i_779_ = v___x_782_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0___boxed(lean_object* v_p_791_, lean_object* v_s_792_, lean_object* v_stopPos_793_, lean_object* v_i_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0(v_p_791_, v_s_792_, v_stopPos_793_, v_i_794_);
lean_dec(v_stopPos_793_);
lean_dec_ref(v_s_792_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* lean_string_nextwhile(lean_object* v_s_796_, lean_object* v_p_797_, lean_object* v_i_798_){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = lean_string_utf8_byte_size(v_s_796_);
v___x_800_ = l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0(v_p_797_, v_s_796_, v___x_799_, v_i_798_);
lean_dec_ref(v_s_796_);
return v___x_800_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_Raw_nextUntil___lam__0(lean_object* v_p_801_, uint32_t v_c_802_){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v___x_803_ = lean_box_uint32(v_c_802_);
v___x_804_ = lean_apply_1(v_p_801_, v___x_803_);
v___x_805_ = lean_unbox(v___x_804_);
if (v___x_805_ == 0)
{
uint8_t v___x_806_; 
v___x_806_ = 1;
return v___x_806_;
}
else
{
uint8_t v___x_807_; 
v___x_807_ = 0;
return v___x_807_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextUntil___lam__0___boxed(lean_object* v_p_808_, lean_object* v_c_809_){
_start:
{
uint32_t v_c_boxed_810_; uint8_t v_res_811_; lean_object* v_r_812_; 
v_c_boxed_810_ = lean_unbox_uint32(v_c_809_);
lean_dec(v_c_809_);
v_res_811_ = l_String_Pos_Raw_nextUntil___lam__0(v_p_808_, v_c_boxed_810_);
v_r_812_ = lean_box(v_res_811_);
return v_r_812_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextUntil(lean_object* v_s_813_, lean_object* v_p_814_, lean_object* v_i_815_){
_start:
{
lean_object* v___f_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___f_816_ = lean_alloc_closure((void*)(l_String_Pos_Raw_nextUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_816_, 0, v_p_814_);
v___x_817_ = lean_string_utf8_byte_size(v_s_813_);
v___x_818_ = l_Substring_Raw_takeWhileAux(v_s_813_, v___x_817_, v___f_816_, v_i_815_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextUntil___boxed(lean_object* v_s_819_, lean_object* v_p_820_, lean_object* v_i_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_String_Pos_Raw_nextUntil(v_s_819_, v_p_820_, v_i_821_);
lean_dec_ref(v_s_819_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0(lean_object* v_p_823_, lean_object* v_s_824_, lean_object* v_stopPos_825_, lean_object* v_i_826_){
_start:
{
uint8_t v___y_828_; lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_831_ = lean_unsigned_to_nat(1u);
v___x_832_ = lean_nat_add(v_i_826_, v___x_831_);
v___x_833_ = lean_nat_dec_le(v___x_832_, v_stopPos_825_);
lean_dec(v___x_832_);
if (v___x_833_ == 0)
{
lean_dec_ref(v_p_823_);
return v_i_826_;
}
else
{
if (v___x_833_ == 0)
{
v___y_828_ = v___x_833_;
goto v___jp_827_;
}
else
{
uint32_t v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_834_ = lean_string_utf8_get(v_s_824_, v_i_826_);
v___x_835_ = lean_box_uint32(v___x_834_);
lean_inc_ref(v_p_823_);
v___x_836_ = lean_apply_1(v_p_823_, v___x_835_);
v___x_837_ = lean_unbox(v___x_836_);
if (v___x_837_ == 0)
{
v___y_828_ = v___x_833_;
goto v___jp_827_;
}
else
{
lean_dec_ref(v_p_823_);
return v_i_826_;
}
}
}
v___jp_827_:
{
if (v___y_828_ == 0)
{
lean_dec_ref(v_p_823_);
return v_i_826_;
}
else
{
lean_object* v___x_829_; 
v___x_829_ = lean_string_utf8_next(v_s_824_, v_i_826_);
lean_dec(v_i_826_);
v_i_826_ = v___x_829_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0___boxed(lean_object* v_p_838_, lean_object* v_s_839_, lean_object* v_stopPos_840_, lean_object* v_i_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0(v_p_838_, v_s_839_, v_stopPos_840_, v_i_841_);
lean_dec(v_stopPos_840_);
lean_dec_ref(v_s_839_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_String_nextUntil(lean_object* v_s_843_, lean_object* v_p_844_, lean_object* v_i_845_){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = lean_string_utf8_byte_size(v_s_843_);
v___x_847_ = l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0(v_p_844_, v_s_843_, v___x_846_, v_i_845_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_String_nextUntil___boxed(lean_object* v_s_848_, lean_object* v_p_849_, lean_object* v_i_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_String_nextUntil(v_s_848_, v_p_849_, v_i_850_);
lean_dec_ref(v_s_848_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___redArg(lean_object* v_s_852_, lean_object* v_inst_853_){
_start:
{
lean_object* v_skipPrefix_x3f_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_874_; 
v_skipPrefix_x3f_854_ = lean_ctor_get(v_inst_853_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v_inst_853_);
if (v_isSharedCheck_874_ == 0)
{
lean_object* v_unused_875_; lean_object* v_unused_876_; 
v_unused_875_ = lean_ctor_get(v_inst_853_, 2);
lean_dec(v_unused_875_);
v_unused_876_ = lean_ctor_get(v_inst_853_, 1);
lean_dec(v_unused_876_);
v___x_856_ = v_inst_853_;
v_isShared_857_ = v_isSharedCheck_874_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_skipPrefix_x3f_854_);
lean_dec(v_inst_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_874_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_858_ = lean_string_utf8_byte_size(v_s_852_);
v___x_859_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_s_852_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 2, v___x_858_);
lean_ctor_set(v___x_856_, 1, v___x_859_);
lean_ctor_set(v___x_856_, 0, v_s_852_);
v___x_861_ = v___x_856_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_s_852_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v___x_859_);
lean_ctor_set(v_reuseFailAlloc_873_, 2, v___x_858_);
v___x_861_ = v_reuseFailAlloc_873_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_862_; 
v___x_862_ = lean_apply_1(v_skipPrefix_x3f_854_, v___x_861_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v___x_863_; 
lean_dec_ref(v_s_852_);
v___x_863_ = lean_box(0);
return v___x_863_;
}
else
{
lean_object* v_val_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_872_; 
v_val_864_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_872_ == 0)
{
v___x_866_ = v___x_862_;
v_isShared_867_ = v_isSharedCheck_872_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_val_864_);
lean_dec(v___x_862_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_872_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_868_; lean_object* v___x_870_; 
v___x_868_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_868_, 0, v_s_852_);
lean_ctor_set(v___x_868_, 1, v_val_864_);
lean_ctor_set(v___x_868_, 2, v___x_858_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_868_);
v___x_870_ = v___x_866_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_868_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f(lean_object* v_00_u03c1_877_, lean_object* v_s_878_, lean_object* v_pat_879_, lean_object* v_inst_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_String_dropPrefix_x3f___redArg(v_s_878_, v_inst_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___boxed(lean_object* v_00_u03c1_882_, lean_object* v_s_883_, lean_object* v_pat_884_, lean_object* v_inst_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_String_dropPrefix_x3f(v_00_u03c1_882_, v_s_883_, v_pat_884_, v_inst_885_);
lean_dec(v_pat_884_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___redArg(lean_object* v_s_887_, lean_object* v_inst_888_){
_start:
{
lean_object* v_skipSuffix_x3f_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_909_; 
v_skipSuffix_x3f_889_ = lean_ctor_get(v_inst_888_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v_inst_888_);
if (v_isSharedCheck_909_ == 0)
{
lean_object* v_unused_910_; lean_object* v_unused_911_; 
v_unused_910_ = lean_ctor_get(v_inst_888_, 2);
lean_dec(v_unused_910_);
v_unused_911_ = lean_ctor_get(v_inst_888_, 1);
lean_dec(v_unused_911_);
v___x_891_ = v_inst_888_;
v_isShared_892_ = v_isSharedCheck_909_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_skipSuffix_x3f_889_);
lean_dec(v_inst_888_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_909_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_896_; 
v___x_893_ = lean_string_utf8_byte_size(v_s_887_);
v___x_894_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_s_887_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 2, v___x_893_);
lean_ctor_set(v___x_891_, 1, v___x_894_);
lean_ctor_set(v___x_891_, 0, v_s_887_);
v___x_896_ = v___x_891_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_s_887_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v___x_894_);
lean_ctor_set(v_reuseFailAlloc_908_, 2, v___x_893_);
v___x_896_ = v_reuseFailAlloc_908_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
lean_object* v___x_897_; 
v___x_897_ = lean_apply_1(v_skipSuffix_x3f_889_, v___x_896_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v___x_898_; 
lean_dec_ref(v_s_887_);
v___x_898_ = lean_box(0);
return v___x_898_;
}
else
{
lean_object* v_val_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_907_; 
v_val_899_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_907_ == 0)
{
v___x_901_ = v___x_897_;
v_isShared_902_ = v_isSharedCheck_907_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_val_899_);
lean_dec(v___x_897_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_907_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_903_; lean_object* v___x_905_; 
v___x_903_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_903_, 0, v_s_887_);
lean_ctor_set(v___x_903_, 1, v___x_894_);
lean_ctor_set(v___x_903_, 2, v_val_899_);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 0, v___x_903_);
v___x_905_ = v___x_901_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_903_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f(lean_object* v_00_u03c1_912_, lean_object* v_s_913_, lean_object* v_pat_914_, lean_object* v_inst_915_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = l_String_dropSuffix_x3f___redArg(v_s_913_, v_inst_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___boxed(lean_object* v_00_u03c1_917_, lean_object* v_s_918_, lean_object* v_pat_919_, lean_object* v_inst_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_String_dropSuffix_x3f(v_00_u03c1_917_, v_s_918_, v_pat_919_, v_inst_920_);
lean_dec(v_pat_919_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix___redArg(lean_object* v_s_922_, lean_object* v_inst_923_){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_924_ = lean_unsigned_to_nat(0u);
v___x_925_ = lean_string_utf8_byte_size(v_s_922_);
v___x_926_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_926_, 0, v_s_922_);
lean_ctor_set(v___x_926_, 1, v___x_924_);
lean_ctor_set(v___x_926_, 2, v___x_925_);
v___x_927_ = l_String_Slice_dropPrefix___redArg(v___x_926_, v_inst_923_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix(lean_object* v_00_u03c1_928_, lean_object* v_s_929_, lean_object* v_pat_930_, lean_object* v_inst_931_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_String_dropPrefix___redArg(v_s_929_, v_inst_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix___boxed(lean_object* v_00_u03c1_933_, lean_object* v_s_934_, lean_object* v_pat_935_, lean_object* v_inst_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_String_dropPrefix(v_00_u03c1_933_, v_s_934_, v_pat_935_, v_inst_936_);
lean_dec(v_pat_935_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg(lean_object* v_pre_938_, lean_object* v_s_939_){
_start:
{
lean_object* v_str_940_; lean_object* v_startInclusive_941_; lean_object* v_endExclusive_942_; lean_object* v___x_943_; lean_object* v___x_944_; uint8_t v___x_945_; 
v_str_940_ = lean_ctor_get(v_s_939_, 0);
v_startInclusive_941_ = lean_ctor_get(v_s_939_, 1);
v_endExclusive_942_ = lean_ctor_get(v_s_939_, 2);
v___x_943_ = lean_string_utf8_byte_size(v_pre_938_);
v___x_944_ = lean_nat_sub(v_endExclusive_942_, v_startInclusive_941_);
v___x_945_ = lean_nat_dec_le(v___x_943_, v___x_944_);
lean_dec(v___x_944_);
if (v___x_945_ == 0)
{
return v_s_939_;
}
else
{
lean_object* v___x_946_; uint8_t v___x_947_; 
v___x_946_ = lean_unsigned_to_nat(0u);
v___x_947_ = lean_string_memcmp(v_str_940_, v_pre_938_, v_startInclusive_941_, v___x_946_, v___x_943_);
if (v___x_947_ == 0)
{
return v_s_939_;
}
else
{
lean_object* v___x_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_956_; 
lean_inc(v_endExclusive_942_);
lean_inc(v_startInclusive_941_);
lean_inc_ref(v_str_940_);
v___x_948_ = l_String_Slice_pos_x21(v_s_939_, v___x_943_);
v_isSharedCheck_956_ = !lean_is_exclusive(v_s_939_);
if (v_isSharedCheck_956_ == 0)
{
lean_object* v_unused_957_; lean_object* v_unused_958_; lean_object* v_unused_959_; 
v_unused_957_ = lean_ctor_get(v_s_939_, 2);
lean_dec(v_unused_957_);
v_unused_958_ = lean_ctor_get(v_s_939_, 1);
lean_dec(v_unused_958_);
v_unused_959_ = lean_ctor_get(v_s_939_, 0);
lean_dec(v_unused_959_);
v___x_950_ = v_s_939_;
v_isShared_951_ = v_isSharedCheck_956_;
goto v_resetjp_949_;
}
else
{
lean_dec(v_s_939_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_956_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_952_; lean_object* v___x_954_; 
v___x_952_ = lean_nat_add(v_startInclusive_941_, v___x_948_);
lean_dec(v___x_948_);
lean_dec(v_startInclusive_941_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 1, v___x_952_);
v___x_954_ = v___x_950_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_str_940_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v___x_952_);
lean_ctor_set(v_reuseFailAlloc_955_, 2, v_endExclusive_942_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg___boxed(lean_object* v_pre_960_, lean_object* v_s_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg(v_pre_960_, v_s_961_);
lean_dec_ref(v_pre_960_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix___at___00String_stripPrefix_spec__0(lean_object* v_pre_963_, lean_object* v_s_964_, lean_object* v_pat_965_){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_966_ = lean_unsigned_to_nat(0u);
v___x_967_ = lean_string_utf8_byte_size(v_s_964_);
v___x_968_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_968_, 0, v_s_964_);
lean_ctor_set(v___x_968_, 1, v___x_966_);
lean_ctor_set(v___x_968_, 2, v___x_967_);
v___x_969_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg(v_pre_963_, v___x_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix___at___00String_stripPrefix_spec__0___boxed(lean_object* v_pre_970_, lean_object* v_s_971_, lean_object* v_pat_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_String_dropPrefix___at___00String_stripPrefix_spec__0(v_pre_970_, v_s_971_, v_pat_972_);
lean_dec_ref(v_pat_972_);
lean_dec_ref(v_pre_970_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_String_stripPrefix(lean_object* v_s_974_, lean_object* v_pre_975_){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = l_String_dropPrefix___at___00String_stripPrefix_spec__0(v_pre_975_, v_s_974_, v_pre_975_);
v___x_977_ = l_String_Slice_toString(v___x_976_);
lean_dec_ref(v___x_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_String_stripPrefix___boxed(lean_object* v_s_978_, lean_object* v_pre_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_String_stripPrefix(v_s_978_, v_pre_979_);
lean_dec_ref(v_pre_979_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0(lean_object* v_pat_981_, lean_object* v_pre_982_, lean_object* v_s_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg(v_pre_982_, v_s_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___boxed(lean_object* v_pat_985_, lean_object* v_pre_986_, lean_object* v_s_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0(v_pat_985_, v_pre_986_, v_s_987_);
lean_dec_ref(v_pre_986_);
lean_dec_ref(v_pat_985_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix___redArg(lean_object* v_s_989_, lean_object* v_inst_990_){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_991_ = lean_unsigned_to_nat(0u);
v___x_992_ = lean_string_utf8_byte_size(v_s_989_);
v___x_993_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_993_, 0, v_s_989_);
lean_ctor_set(v___x_993_, 1, v___x_991_);
lean_ctor_set(v___x_993_, 2, v___x_992_);
v___x_994_ = l_String_Slice_dropSuffix___redArg(v___x_993_, v_inst_990_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix(lean_object* v_00_u03c1_995_, lean_object* v_s_996_, lean_object* v_pat_997_, lean_object* v_inst_998_){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = l_String_dropSuffix___redArg(v_s_996_, v_inst_998_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix___boxed(lean_object* v_00_u03c1_1000_, lean_object* v_s_1001_, lean_object* v_pat_1002_, lean_object* v_inst_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_String_dropSuffix(v_00_u03c1_1000_, v_s_1001_, v_pat_1002_, v_inst_1003_);
lean_dec(v_pat_1002_);
return v_res_1004_;
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

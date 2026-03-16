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
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_Raw_takeWhileAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_dropSuffix___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l_Char_isWhitespace___boxed(lean_object*);
lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool(lean_object*);
lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(lean_object*);
lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_dropPrefix___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_String_Slice_0__String_Slice_takeEndWhile_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_String_Slice_0__String_Slice_takeWhile_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_takeWhile___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_takeWhile___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_takeWhile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_takeWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropWhile___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropWhile___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropWhile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_takeEndWhile___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_takeEndWhile___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_takeEndWhile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_takeEndWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_takeEndWhile_go___at___00String_takeRightWhile_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_takeRightWhile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_takeRightWhile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropEndWhile___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropEndWhile___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropEndWhile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropEndWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_dropRightWhile_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_dropRightWhile_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropRightWhile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropRightWhile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropRightWhile___boxed(lean_object*, lean_object*);
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
static const lean_closure_object l_String_trimAsciiEnd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Char_isWhitespace___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_trimAsciiEnd___closed__0 = (const lean_object*)&l_String_trimAsciiEnd___closed__0_value;
static lean_once_cell_t l_String_trimAsciiEnd___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_trimAsciiEnd___closed__1;
LEAN_EXPORT lean_object* l_String_trimAsciiEnd(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_trimRight_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_trimRight_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_trimRight(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_trimRight(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_trimRight___boxed(lean_object*);
static lean_once_cell_t l_String_trimAsciiStart___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_trimAsciiStart___closed__0;
LEAN_EXPORT lean_object* l_String_trimAsciiStart(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_trimLeft_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_trimLeft_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_trimLeft(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_trimLeft(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_trimLeft___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_trimAscii(lean_object*);
LEAN_EXPORT lean_object* l_String_trim(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_trim(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_trim___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_String_takeWhile___redArg(lean_object* v_s_94_, lean_object* v_pat_95_, lean_object* v_inst_96_){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_97_ = lean_unsigned_to_nat(0u);
v___x_98_ = lean_string_utf8_byte_size(v_s_94_);
v___x_99_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_99_, 0, v_s_94_);
lean_ctor_set(v___x_99_, 1, v___x_97_);
lean_ctor_set(v___x_99_, 2, v___x_98_);
v___x_100_ = l___private_Init_Data_String_Slice_0__String_Slice_takeWhile_go(lean_box(0), v___x_99_, v_pat_95_, v_inst_96_, v___x_97_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_String_takeWhile___redArg___boxed(lean_object* v_s_101_, lean_object* v_pat_102_, lean_object* v_inst_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_String_takeWhile___redArg(v_s_101_, v_pat_102_, v_inst_103_);
lean_dec(v_pat_102_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_String_takeWhile(lean_object* v_00_u03c1_105_, lean_object* v_s_106_, lean_object* v_pat_107_, lean_object* v_inst_108_){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_109_ = lean_unsigned_to_nat(0u);
v___x_110_ = lean_string_utf8_byte_size(v_s_106_);
v___x_111_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_111_, 0, v_s_106_);
lean_ctor_set(v___x_111_, 1, v___x_109_);
lean_ctor_set(v___x_111_, 2, v___x_110_);
v___x_112_ = l___private_Init_Data_String_Slice_0__String_Slice_takeWhile_go(lean_box(0), v___x_111_, v_pat_107_, v_inst_108_, v___x_109_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_String_takeWhile___boxed(lean_object* v_00_u03c1_113_, lean_object* v_s_114_, lean_object* v_pat_115_, lean_object* v_inst_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_String_takeWhile(v_00_u03c1_113_, v_s_114_, v_pat_115_, v_inst_116_);
lean_dec(v_pat_115_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_String_dropWhile___redArg(lean_object* v_s_118_, lean_object* v_pat_119_, lean_object* v_inst_120_){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = lean_string_utf8_byte_size(v_s_118_);
v___x_123_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_123_, 0, v_s_118_);
lean_ctor_set(v___x_123_, 1, v___x_121_);
lean_ctor_set(v___x_123_, 2, v___x_122_);
v___x_124_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go(lean_box(0), v___x_123_, v_pat_119_, v_inst_120_, v___x_121_);
lean_dec_ref(v___x_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_String_dropWhile___redArg___boxed(lean_object* v_s_125_, lean_object* v_pat_126_, lean_object* v_inst_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_String_dropWhile___redArg(v_s_125_, v_pat_126_, v_inst_127_);
lean_dec(v_pat_126_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_String_dropWhile(lean_object* v_00_u03c1_129_, lean_object* v_s_130_, lean_object* v_pat_131_, lean_object* v_inst_132_){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_133_ = lean_unsigned_to_nat(0u);
v___x_134_ = lean_string_utf8_byte_size(v_s_130_);
v___x_135_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_135_, 0, v_s_130_);
lean_ctor_set(v___x_135_, 1, v___x_133_);
lean_ctor_set(v___x_135_, 2, v___x_134_);
v___x_136_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go(lean_box(0), v___x_135_, v_pat_131_, v_inst_132_, v___x_133_);
lean_dec_ref(v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_String_dropWhile___boxed(lean_object* v_00_u03c1_137_, lean_object* v_s_138_, lean_object* v_pat_139_, lean_object* v_inst_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_String_dropWhile(v_00_u03c1_137_, v_s_138_, v_pat_139_, v_inst_140_);
lean_dec(v_pat_139_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_String_takeEndWhile___redArg(lean_object* v_s_142_, lean_object* v_pat_143_, lean_object* v_inst_144_){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_145_ = lean_unsigned_to_nat(0u);
v___x_146_ = lean_string_utf8_byte_size(v_s_142_);
v___x_147_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_147_, 0, v_s_142_);
lean_ctor_set(v___x_147_, 1, v___x_145_);
lean_ctor_set(v___x_147_, 2, v___x_146_);
v___x_148_ = l___private_Init_Data_String_Slice_0__String_Slice_takeEndWhile_go(lean_box(0), v___x_147_, v_pat_143_, v_inst_144_, v___x_146_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_String_takeEndWhile___redArg___boxed(lean_object* v_s_149_, lean_object* v_pat_150_, lean_object* v_inst_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_String_takeEndWhile___redArg(v_s_149_, v_pat_150_, v_inst_151_);
lean_dec(v_pat_150_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_String_takeEndWhile(lean_object* v_00_u03c1_153_, lean_object* v_s_154_, lean_object* v_pat_155_, lean_object* v_inst_156_){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_157_ = lean_unsigned_to_nat(0u);
v___x_158_ = lean_string_utf8_byte_size(v_s_154_);
v___x_159_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_159_, 0, v_s_154_);
lean_ctor_set(v___x_159_, 1, v___x_157_);
lean_ctor_set(v___x_159_, 2, v___x_158_);
v___x_160_ = l___private_Init_Data_String_Slice_0__String_Slice_takeEndWhile_go(lean_box(0), v___x_159_, v_pat_155_, v_inst_156_, v___x_158_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_String_takeEndWhile___boxed(lean_object* v_00_u03c1_161_, lean_object* v_s_162_, lean_object* v_pat_163_, lean_object* v_inst_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_String_takeEndWhile(v_00_u03c1_161_, v_s_162_, v_pat_163_, v_inst_164_);
lean_dec(v_pat_163_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_takeEndWhile_go___at___00String_takeRightWhile_spec__0(lean_object* v_p_166_, lean_object* v_s_167_, lean_object* v_curr_168_){
_start:
{
lean_object* v_str_169_; lean_object* v_startInclusive_170_; lean_object* v_endExclusive_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; 
v_str_169_ = lean_ctor_get(v_s_167_, 0);
v_startInclusive_170_ = lean_ctor_get(v_s_167_, 1);
v_endExclusive_171_ = lean_ctor_get(v_s_167_, 2);
v___x_172_ = lean_nat_add(v_startInclusive_170_, v_curr_168_);
v___x_173_ = lean_nat_sub(v___x_172_, v_startInclusive_170_);
v___x_174_ = lean_unsigned_to_nat(0u);
v___x_175_ = lean_nat_dec_eq(v___x_173_, v___x_174_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; uint32_t v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
lean_inc(v___x_172_);
lean_inc(v_startInclusive_170_);
lean_inc_ref(v_str_169_);
v___x_176_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_176_, 0, v_str_169_);
lean_ctor_set(v___x_176_, 1, v_startInclusive_170_);
lean_ctor_set(v___x_176_, 2, v___x_172_);
v___x_177_ = lean_unsigned_to_nat(1u);
v___x_178_ = lean_nat_sub(v___x_173_, v___x_177_);
lean_dec(v___x_173_);
v___x_179_ = l_String_Slice_posLE(v___x_176_, v___x_178_);
lean_dec_ref(v___x_176_);
v___x_180_ = lean_nat_add(v_startInclusive_170_, v___x_179_);
v___x_181_ = lean_string_utf8_get_fast(v_str_169_, v___x_180_);
lean_dec(v___x_180_);
v___x_182_ = lean_box_uint32(v___x_181_);
lean_inc_ref(v_p_166_);
v___x_183_ = lean_apply_1(v_p_166_, v___x_182_);
v___x_184_ = lean_unbox(v___x_183_);
if (v___x_184_ == 0)
{
lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_191_; 
lean_inc(v_endExclusive_171_);
lean_inc_ref(v_str_169_);
lean_dec(v___x_179_);
lean_dec(v_curr_168_);
lean_dec_ref(v_p_166_);
v_isSharedCheck_191_ = !lean_is_exclusive(v_s_167_);
if (v_isSharedCheck_191_ == 0)
{
lean_object* v_unused_192_; lean_object* v_unused_193_; lean_object* v_unused_194_; 
v_unused_192_ = lean_ctor_get(v_s_167_, 2);
lean_dec(v_unused_192_);
v_unused_193_ = lean_ctor_get(v_s_167_, 1);
lean_dec(v_unused_193_);
v_unused_194_ = lean_ctor_get(v_s_167_, 0);
lean_dec(v_unused_194_);
v___x_186_ = v_s_167_;
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
else
{
lean_dec(v_s_167_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_189_; 
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 1, v___x_172_);
v___x_189_ = v___x_186_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_str_169_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v___x_172_);
lean_ctor_set(v_reuseFailAlloc_190_, 2, v_endExclusive_171_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
else
{
uint8_t v___x_195_; 
v___x_195_ = lean_nat_dec_lt(v___x_179_, v_curr_168_);
lean_dec(v_curr_168_);
if (v___x_195_ == 0)
{
lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_202_; 
lean_inc(v_endExclusive_171_);
lean_inc_ref(v_str_169_);
lean_dec(v___x_179_);
lean_dec_ref(v_p_166_);
v_isSharedCheck_202_ = !lean_is_exclusive(v_s_167_);
if (v_isSharedCheck_202_ == 0)
{
lean_object* v_unused_203_; lean_object* v_unused_204_; lean_object* v_unused_205_; 
v_unused_203_ = lean_ctor_get(v_s_167_, 2);
lean_dec(v_unused_203_);
v_unused_204_ = lean_ctor_get(v_s_167_, 1);
lean_dec(v_unused_204_);
v_unused_205_ = lean_ctor_get(v_s_167_, 0);
lean_dec(v_unused_205_);
v___x_197_ = v_s_167_;
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
else
{
lean_dec(v_s_167_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_200_; 
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 1, v___x_172_);
v___x_200_ = v___x_197_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_str_169_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v___x_172_);
lean_ctor_set(v_reuseFailAlloc_201_, 2, v_endExclusive_171_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
else
{
lean_dec(v___x_172_);
v_curr_168_ = v___x_179_;
goto _start;
}
}
}
else
{
lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_213_; 
lean_inc(v_endExclusive_171_);
lean_inc_ref(v_str_169_);
lean_dec(v___x_173_);
lean_dec(v_curr_168_);
lean_dec_ref(v_p_166_);
v_isSharedCheck_213_ = !lean_is_exclusive(v_s_167_);
if (v_isSharedCheck_213_ == 0)
{
lean_object* v_unused_214_; lean_object* v_unused_215_; lean_object* v_unused_216_; 
v_unused_214_ = lean_ctor_get(v_s_167_, 2);
lean_dec(v_unused_214_);
v_unused_215_ = lean_ctor_get(v_s_167_, 1);
lean_dec(v_unused_215_);
v_unused_216_ = lean_ctor_get(v_s_167_, 0);
lean_dec(v_unused_216_);
v___x_208_ = v_s_167_;
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
else
{
lean_dec(v_s_167_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_211_; 
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 1, v___x_172_);
v___x_211_ = v___x_208_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_str_169_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v___x_172_);
lean_ctor_set(v_reuseFailAlloc_212_, 2, v_endExclusive_171_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_takeRightWhile(lean_object* v_s_217_, lean_object* v_p_218_){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_219_ = lean_unsigned_to_nat(0u);
v___x_220_ = lean_string_utf8_byte_size(v_s_217_);
v___x_221_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_221_, 0, v_s_217_);
lean_ctor_set(v___x_221_, 1, v___x_219_);
lean_ctor_set(v___x_221_, 2, v___x_220_);
v___x_222_ = l___private_Init_Data_String_Slice_0__String_Slice_takeEndWhile_go___at___00String_takeRightWhile_spec__0(v_p_218_, v___x_221_, v___x_220_);
v___x_223_ = l_String_Slice_toString(v___x_222_);
lean_dec_ref(v___x_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeRightWhile(lean_object* v_s_224_, lean_object* v_p_225_){
_start:
{
lean_object* v_startInclusive_226_; lean_object* v_endExclusive_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v_startInclusive_226_ = lean_ctor_get(v_s_224_, 1);
v_endExclusive_227_ = lean_ctor_get(v_s_224_, 2);
v___x_228_ = lean_nat_sub(v_endExclusive_227_, v_startInclusive_226_);
v___x_229_ = l___private_Init_Data_String_Slice_0__String_Slice_takeEndWhile_go___at___00String_takeRightWhile_spec__0(v_p_225_, v_s_224_, v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_String_dropEndWhile___redArg(lean_object* v_s_230_, lean_object* v_pat_231_, lean_object* v_inst_232_){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_233_ = lean_unsigned_to_nat(0u);
v___x_234_ = lean_string_utf8_byte_size(v_s_230_);
v___x_235_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_235_, 0, v_s_230_);
lean_ctor_set(v___x_235_, 1, v___x_233_);
lean_ctor_set(v___x_235_, 2, v___x_234_);
v___x_236_ = l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go(lean_box(0), v___x_235_, v_pat_231_, v_inst_232_, v___x_234_);
lean_dec_ref(v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_String_dropEndWhile___redArg___boxed(lean_object* v_s_237_, lean_object* v_pat_238_, lean_object* v_inst_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_String_dropEndWhile___redArg(v_s_237_, v_pat_238_, v_inst_239_);
lean_dec(v_pat_238_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_String_dropEndWhile(lean_object* v_00_u03c1_241_, lean_object* v_s_242_, lean_object* v_pat_243_, lean_object* v_inst_244_){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_245_ = lean_unsigned_to_nat(0u);
v___x_246_ = lean_string_utf8_byte_size(v_s_242_);
v___x_247_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_247_, 0, v_s_242_);
lean_ctor_set(v___x_247_, 1, v___x_245_);
lean_ctor_set(v___x_247_, 2, v___x_246_);
v___x_248_ = l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go(lean_box(0), v___x_247_, v_pat_243_, v_inst_244_, v___x_246_);
lean_dec_ref(v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_String_dropEndWhile___boxed(lean_object* v_00_u03c1_249_, lean_object* v_s_250_, lean_object* v_pat_251_, lean_object* v_inst_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_String_dropEndWhile(v_00_u03c1_249_, v_s_250_, v_pat_251_, v_inst_252_);
lean_dec(v_pat_251_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_dropRightWhile_spec__0(lean_object* v_p_254_, lean_object* v_s_255_, lean_object* v_curr_256_){
_start:
{
lean_object* v_str_257_; lean_object* v_startInclusive_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v_str_257_ = lean_ctor_get(v_s_255_, 0);
v_startInclusive_258_ = lean_ctor_get(v_s_255_, 1);
v___x_259_ = lean_nat_add(v_startInclusive_258_, v_curr_256_);
lean_inc(v___x_259_);
lean_inc(v_startInclusive_258_);
lean_inc_ref(v_str_257_);
v___x_260_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_260_, 0, v_str_257_);
lean_ctor_set(v___x_260_, 1, v_startInclusive_258_);
lean_ctor_set(v___x_260_, 2, v___x_259_);
v___x_261_ = lean_nat_sub(v___x_259_, v_startInclusive_258_);
lean_dec(v___x_259_);
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = lean_nat_dec_eq(v___x_261_, v___x_262_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; uint32_t v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; 
v___x_264_ = lean_unsigned_to_nat(1u);
v___x_265_ = lean_nat_sub(v___x_261_, v___x_264_);
lean_dec(v___x_261_);
v___x_266_ = l_String_Slice_posLE(v___x_260_, v___x_265_);
v___x_267_ = lean_nat_add(v_startInclusive_258_, v___x_266_);
v___x_268_ = lean_string_utf8_get_fast(v_str_257_, v___x_267_);
lean_dec(v___x_267_);
v___x_269_ = lean_box_uint32(v___x_268_);
lean_inc_ref(v_p_254_);
v___x_270_ = lean_apply_1(v_p_254_, v___x_269_);
v___x_271_ = lean_unbox(v___x_270_);
if (v___x_271_ == 0)
{
lean_dec(v___x_266_);
lean_dec(v_curr_256_);
lean_dec_ref(v_p_254_);
return v___x_260_;
}
else
{
uint8_t v___x_272_; 
v___x_272_ = lean_nat_dec_lt(v___x_266_, v_curr_256_);
lean_dec(v_curr_256_);
if (v___x_272_ == 0)
{
lean_dec(v___x_266_);
lean_dec_ref(v_p_254_);
return v___x_260_;
}
else
{
lean_dec_ref(v___x_260_);
v_curr_256_ = v___x_266_;
goto _start;
}
}
}
else
{
lean_dec(v___x_261_);
lean_dec(v_curr_256_);
lean_dec_ref(v_p_254_);
return v___x_260_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_dropRightWhile_spec__0___boxed(lean_object* v_p_274_, lean_object* v_s_275_, lean_object* v_curr_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_dropRightWhile_spec__0(v_p_274_, v_s_275_, v_curr_276_);
lean_dec_ref(v_s_275_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_String_dropRightWhile(lean_object* v_s_278_, lean_object* v_p_279_){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_280_ = lean_unsigned_to_nat(0u);
v___x_281_ = lean_string_utf8_byte_size(v_s_278_);
v___x_282_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_282_, 0, v_s_278_);
lean_ctor_set(v___x_282_, 1, v___x_280_);
lean_ctor_set(v___x_282_, 2, v___x_281_);
v___x_283_ = l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_dropRightWhile_spec__0(v_p_279_, v___x_282_, v___x_281_);
lean_dec_ref(v___x_282_);
v___x_284_ = l_String_Slice_toString(v___x_283_);
lean_dec_ref(v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropRightWhile(lean_object* v_s_285_, lean_object* v_p_286_){
_start:
{
lean_object* v_startInclusive_287_; lean_object* v_endExclusive_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v_startInclusive_287_ = lean_ctor_get(v_s_285_, 1);
v_endExclusive_288_ = lean_ctor_get(v_s_285_, 2);
v___x_289_ = lean_nat_sub(v_endExclusive_288_, v_startInclusive_287_);
v___x_290_ = l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_dropRightWhile_spec__0(v_p_286_, v_s_285_, v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropRightWhile___boxed(lean_object* v_s_291_, lean_object* v_p_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_String_Slice_dropRightWhile(v_s_291_, v_p_292_);
lean_dec_ref(v_s_291_);
return v_res_293_;
}
}
LEAN_EXPORT uint8_t l_String_startsWith___redArg(lean_object* v_s_294_, lean_object* v_inst_295_){
_start:
{
lean_object* v_startsWith_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_307_; 
v_startsWith_296_ = lean_ctor_get(v_inst_295_, 2);
v_isSharedCheck_307_ = !lean_is_exclusive(v_inst_295_);
if (v_isSharedCheck_307_ == 0)
{
lean_object* v_unused_308_; lean_object* v_unused_309_; 
v_unused_308_ = lean_ctor_get(v_inst_295_, 1);
lean_dec(v_unused_308_);
v_unused_309_ = lean_ctor_get(v_inst_295_, 0);
lean_dec(v_unused_309_);
v___x_298_ = v_inst_295_;
v_isShared_299_ = v_isSharedCheck_307_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_startsWith_296_);
lean_dec(v_inst_295_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_307_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_303_; 
v___x_300_ = lean_string_utf8_byte_size(v_s_294_);
v___x_301_ = lean_unsigned_to_nat(0u);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 2, v___x_300_);
lean_ctor_set(v___x_298_, 1, v___x_301_);
lean_ctor_set(v___x_298_, 0, v_s_294_);
v___x_303_ = v___x_298_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_s_294_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v___x_301_);
lean_ctor_set(v_reuseFailAlloc_306_, 2, v___x_300_);
v___x_303_ = v_reuseFailAlloc_306_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_304_ = lean_apply_1(v_startsWith_296_, v___x_303_);
v___x_305_ = lean_unbox(v___x_304_);
return v___x_305_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_startsWith___redArg___boxed(lean_object* v_s_310_, lean_object* v_inst_311_){
_start:
{
uint8_t v_res_312_; lean_object* v_r_313_; 
v_res_312_ = l_String_startsWith___redArg(v_s_310_, v_inst_311_);
v_r_313_ = lean_box(v_res_312_);
return v_r_313_;
}
}
LEAN_EXPORT uint8_t l_String_startsWith(lean_object* v_00_u03c1_314_, lean_object* v_s_315_, lean_object* v_pat_316_, lean_object* v_inst_317_){
_start:
{
lean_object* v_startsWith_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_329_; 
v_startsWith_318_ = lean_ctor_get(v_inst_317_, 2);
v_isSharedCheck_329_ = !lean_is_exclusive(v_inst_317_);
if (v_isSharedCheck_329_ == 0)
{
lean_object* v_unused_330_; lean_object* v_unused_331_; 
v_unused_330_ = lean_ctor_get(v_inst_317_, 1);
lean_dec(v_unused_330_);
v_unused_331_ = lean_ctor_get(v_inst_317_, 0);
lean_dec(v_unused_331_);
v___x_320_ = v_inst_317_;
v_isShared_321_ = v_isSharedCheck_329_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_startsWith_318_);
lean_dec(v_inst_317_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_329_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_322_ = lean_string_utf8_byte_size(v_s_315_);
v___x_323_ = lean_unsigned_to_nat(0u);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 2, v___x_322_);
lean_ctor_set(v___x_320_, 1, v___x_323_);
lean_ctor_set(v___x_320_, 0, v_s_315_);
v___x_325_ = v___x_320_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_s_315_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v___x_323_);
lean_ctor_set(v_reuseFailAlloc_328_, 2, v___x_322_);
v___x_325_ = v_reuseFailAlloc_328_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_326_; uint8_t v___x_327_; 
v___x_326_ = lean_apply_1(v_startsWith_318_, v___x_325_);
v___x_327_ = lean_unbox(v___x_326_);
return v___x_327_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_startsWith___boxed(lean_object* v_00_u03c1_332_, lean_object* v_s_333_, lean_object* v_pat_334_, lean_object* v_inst_335_){
_start:
{
uint8_t v_res_336_; lean_object* v_r_337_; 
v_res_336_ = l_String_startsWith(v_00_u03c1_332_, v_s_333_, v_pat_334_, v_inst_335_);
lean_dec(v_pat_334_);
v_r_337_ = lean_box(v_res_336_);
return v_r_337_;
}
}
LEAN_EXPORT uint8_t l_String_isPrefixOf(lean_object* v_p_338_, lean_object* v_s_339_){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_340_ = lean_string_utf8_byte_size(v_s_339_);
v___x_341_ = lean_string_utf8_byte_size(v_p_338_);
v___x_342_ = lean_nat_dec_le(v___x_341_, v___x_340_);
if (v___x_342_ == 0)
{
return v___x_342_;
}
else
{
lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_343_ = lean_unsigned_to_nat(0u);
v___x_344_ = lean_string_memcmp(v_s_339_, v_p_338_, v___x_343_, v___x_343_, v___x_341_);
return v___x_344_;
}
}
}
LEAN_EXPORT lean_object* l_String_isPrefixOf___boxed(lean_object* v_p_345_, lean_object* v_s_346_){
_start:
{
uint8_t v_res_347_; lean_object* v_r_348_; 
v_res_347_ = l_String_isPrefixOf(v_p_345_, v_s_346_);
lean_dec_ref(v_s_346_);
lean_dec_ref(v_p_345_);
v_r_348_ = lean_box(v_res_347_);
return v_r_348_;
}
}
LEAN_EXPORT uint8_t lean_string_isprefixof(lean_object* v_p_349_, lean_object* v_s_350_){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_351_ = lean_string_utf8_byte_size(v_s_350_);
v___x_352_ = lean_string_utf8_byte_size(v_p_349_);
v___x_353_ = lean_nat_dec_le(v___x_352_, v___x_351_);
if (v___x_353_ == 0)
{
lean_dec_ref(v_s_350_);
lean_dec_ref(v_p_349_);
return v___x_353_;
}
else
{
lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_354_ = lean_unsigned_to_nat(0u);
v___x_355_ = lean_string_memcmp(v_s_350_, v_p_349_, v___x_354_, v___x_354_, v___x_352_);
lean_dec_ref(v_p_349_);
lean_dec_ref(v_s_350_);
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l_String_Internal_isPrefixOfImpl___boxed(lean_object* v_p_356_, lean_object* v_s_357_){
_start:
{
uint8_t v_res_358_; lean_object* v_r_359_; 
v_res_358_ = lean_string_isprefixof(v_p_356_, v_s_357_);
v_r_359_ = lean_box(v_res_358_);
return v_r_359_;
}
}
LEAN_EXPORT uint8_t l_String_endsWith___redArg(lean_object* v_s_360_, lean_object* v_inst_361_){
_start:
{
lean_object* v_endsWith_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_373_; 
v_endsWith_362_ = lean_ctor_get(v_inst_361_, 2);
v_isSharedCheck_373_ = !lean_is_exclusive(v_inst_361_);
if (v_isSharedCheck_373_ == 0)
{
lean_object* v_unused_374_; lean_object* v_unused_375_; 
v_unused_374_ = lean_ctor_get(v_inst_361_, 1);
lean_dec(v_unused_374_);
v_unused_375_ = lean_ctor_get(v_inst_361_, 0);
lean_dec(v_unused_375_);
v___x_364_ = v_inst_361_;
v_isShared_365_ = v_isSharedCheck_373_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_endsWith_362_);
lean_dec(v_inst_361_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_373_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_366_ = lean_string_utf8_byte_size(v_s_360_);
v___x_367_ = lean_unsigned_to_nat(0u);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 2, v___x_366_);
lean_ctor_set(v___x_364_, 1, v___x_367_);
lean_ctor_set(v___x_364_, 0, v_s_360_);
v___x_369_ = v___x_364_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_s_360_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_372_, 2, v___x_366_);
v___x_369_ = v_reuseFailAlloc_372_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_370_ = lean_apply_1(v_endsWith_362_, v___x_369_);
v___x_371_ = lean_unbox(v___x_370_);
return v___x_371_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_endsWith___redArg___boxed(lean_object* v_s_376_, lean_object* v_inst_377_){
_start:
{
uint8_t v_res_378_; lean_object* v_r_379_; 
v_res_378_ = l_String_endsWith___redArg(v_s_376_, v_inst_377_);
v_r_379_ = lean_box(v_res_378_);
return v_r_379_;
}
}
LEAN_EXPORT uint8_t l_String_endsWith(lean_object* v_00_u03c1_380_, lean_object* v_s_381_, lean_object* v_pat_382_, lean_object* v_inst_383_){
_start:
{
lean_object* v_endsWith_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_395_; 
v_endsWith_384_ = lean_ctor_get(v_inst_383_, 2);
v_isSharedCheck_395_ = !lean_is_exclusive(v_inst_383_);
if (v_isSharedCheck_395_ == 0)
{
lean_object* v_unused_396_; lean_object* v_unused_397_; 
v_unused_396_ = lean_ctor_get(v_inst_383_, 1);
lean_dec(v_unused_396_);
v_unused_397_ = lean_ctor_get(v_inst_383_, 0);
lean_dec(v_unused_397_);
v___x_386_ = v_inst_383_;
v_isShared_387_ = v_isSharedCheck_395_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_endsWith_384_);
lean_dec(v_inst_383_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_395_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_391_; 
v___x_388_ = lean_string_utf8_byte_size(v_s_381_);
v___x_389_ = lean_unsigned_to_nat(0u);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 2, v___x_388_);
lean_ctor_set(v___x_386_, 1, v___x_389_);
lean_ctor_set(v___x_386_, 0, v_s_381_);
v___x_391_ = v___x_386_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_s_381_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v___x_389_);
lean_ctor_set(v_reuseFailAlloc_394_, 2, v___x_388_);
v___x_391_ = v_reuseFailAlloc_394_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_392_ = lean_apply_1(v_endsWith_384_, v___x_391_);
v___x_393_ = lean_unbox(v___x_392_);
return v___x_393_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_endsWith___boxed(lean_object* v_00_u03c1_398_, lean_object* v_s_399_, lean_object* v_pat_400_, lean_object* v_inst_401_){
_start:
{
uint8_t v_res_402_; lean_object* v_r_403_; 
v_res_402_ = l_String_endsWith(v_00_u03c1_398_, v_s_399_, v_pat_400_, v_inst_401_);
lean_dec(v_pat_400_);
v_r_403_ = lean_box(v_res_402_);
return v_r_403_;
}
}
static lean_object* _init_l_String_trimAsciiEnd___closed__1(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = ((lean_object*)(l_String_trimAsciiEnd___closed__0));
v___x_406_ = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool(v___x_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_String_trimAsciiEnd(lean_object* v_s_407_){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_408_ = lean_unsigned_to_nat(0u);
v___x_409_ = lean_string_utf8_byte_size(v_s_407_);
v___x_410_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_410_, 0, v_s_407_);
lean_ctor_set(v___x_410_, 1, v___x_408_);
lean_ctor_set(v___x_410_, 2, v___x_409_);
v___x_411_ = ((lean_object*)(l_String_trimAsciiEnd___closed__0));
v___x_412_ = lean_obj_once(&l_String_trimAsciiEnd___closed__1, &l_String_trimAsciiEnd___closed__1_once, _init_l_String_trimAsciiEnd___closed__1);
v___x_413_ = l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go(lean_box(0), v___x_410_, v___x_411_, v___x_412_, v___x_409_);
lean_dec_ref(v___x_410_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_trimRight_spec__0(lean_object* v_s_414_, lean_object* v_curr_415_){
_start:
{
lean_object* v_str_416_; lean_object* v_startInclusive_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; uint8_t v___x_422_; 
v_str_416_ = lean_ctor_get(v_s_414_, 0);
v_startInclusive_417_ = lean_ctor_get(v_s_414_, 1);
v___x_418_ = lean_nat_add(v_startInclusive_417_, v_curr_415_);
lean_inc(v___x_418_);
lean_inc(v_startInclusive_417_);
lean_inc_ref(v_str_416_);
v___x_419_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_419_, 0, v_str_416_);
lean_ctor_set(v___x_419_, 1, v_startInclusive_417_);
lean_ctor_set(v___x_419_, 2, v___x_418_);
v___x_420_ = lean_nat_sub(v___x_418_, v_startInclusive_417_);
lean_dec(v___x_418_);
v___x_421_ = lean_unsigned_to_nat(0u);
v___x_422_ = lean_nat_dec_eq(v___x_420_, v___x_421_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; uint8_t v___y_430_; lean_object* v___x_431_; uint32_t v___x_432_; uint8_t v___y_434_; uint32_t v___x_439_; uint8_t v___x_440_; 
v___x_423_ = lean_unsigned_to_nat(1u);
v___x_424_ = lean_nat_sub(v___x_420_, v___x_423_);
lean_dec(v___x_420_);
v___x_425_ = l_String_Slice_posLE(v___x_419_, v___x_424_);
v___x_431_ = lean_nat_add(v_startInclusive_417_, v___x_425_);
v___x_432_ = lean_string_utf8_get_fast(v_str_416_, v___x_431_);
lean_dec(v___x_431_);
v___x_439_ = 32;
v___x_440_ = lean_uint32_dec_eq(v___x_432_, v___x_439_);
if (v___x_440_ == 0)
{
uint32_t v___x_441_; uint8_t v___x_442_; 
v___x_441_ = 9;
v___x_442_ = lean_uint32_dec_eq(v___x_432_, v___x_441_);
v___y_434_ = v___x_442_;
goto v___jp_433_;
}
else
{
v___y_434_ = v___x_440_;
goto v___jp_433_;
}
v___jp_426_:
{
uint8_t v___x_427_; 
v___x_427_ = lean_nat_dec_lt(v___x_425_, v_curr_415_);
lean_dec(v_curr_415_);
if (v___x_427_ == 0)
{
lean_dec(v___x_425_);
return v___x_419_;
}
else
{
lean_dec_ref(v___x_419_);
v_curr_415_ = v___x_425_;
goto _start;
}
}
v___jp_429_:
{
if (v___y_430_ == 0)
{
lean_dec(v___x_425_);
lean_dec(v_curr_415_);
return v___x_419_;
}
else
{
goto v___jp_426_;
}
}
v___jp_433_:
{
if (v___y_434_ == 0)
{
uint32_t v___x_435_; uint8_t v___x_436_; 
v___x_435_ = 13;
v___x_436_ = lean_uint32_dec_eq(v___x_432_, v___x_435_);
if (v___x_436_ == 0)
{
uint32_t v___x_437_; uint8_t v___x_438_; 
v___x_437_ = 10;
v___x_438_ = lean_uint32_dec_eq(v___x_432_, v___x_437_);
v___y_430_ = v___x_438_;
goto v___jp_429_;
}
else
{
v___y_430_ = v___x_436_;
goto v___jp_429_;
}
}
else
{
goto v___jp_426_;
}
}
}
else
{
lean_dec(v___x_420_);
lean_dec(v_curr_415_);
return v___x_419_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_trimRight_spec__0___boxed(lean_object* v_s_443_, lean_object* v_curr_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_trimRight_spec__0(v_s_443_, v_curr_444_);
lean_dec_ref(v_s_443_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_String_trimRight(lean_object* v_s_446_){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v_str_451_; lean_object* v_startInclusive_452_; lean_object* v_endExclusive_453_; lean_object* v___x_454_; 
v___x_447_ = lean_unsigned_to_nat(0u);
v___x_448_ = lean_string_utf8_byte_size(v_s_446_);
v___x_449_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_449_, 0, v_s_446_);
lean_ctor_set(v___x_449_, 1, v___x_447_);
lean_ctor_set(v___x_449_, 2, v___x_448_);
v___x_450_ = l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_trimRight_spec__0(v___x_449_, v___x_448_);
lean_dec_ref(v___x_449_);
v_str_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc_ref(v_str_451_);
v_startInclusive_452_ = lean_ctor_get(v___x_450_, 1);
lean_inc(v_startInclusive_452_);
v_endExclusive_453_ = lean_ctor_get(v___x_450_, 2);
lean_inc(v_endExclusive_453_);
lean_dec_ref(v___x_450_);
v___x_454_ = lean_string_utf8_extract(v_str_451_, v_startInclusive_452_, v_endExclusive_453_);
lean_dec(v_endExclusive_453_);
lean_dec(v_startInclusive_452_);
lean_dec_ref(v_str_451_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimRight(lean_object* v_s_455_){
_start:
{
lean_object* v_startInclusive_456_; lean_object* v_endExclusive_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v_startInclusive_456_ = lean_ctor_get(v_s_455_, 1);
v_endExclusive_457_ = lean_ctor_get(v_s_455_, 2);
v___x_458_ = lean_nat_sub(v_endExclusive_457_, v_startInclusive_456_);
v___x_459_ = l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_trimRight_spec__0(v_s_455_, v___x_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimRight___boxed(lean_object* v_s_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_String_Slice_trimRight(v_s_460_);
lean_dec_ref(v_s_460_);
return v_res_461_;
}
}
static lean_object* _init_l_String_trimAsciiStart___closed__0(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = ((lean_object*)(l_String_trimAsciiEnd___closed__0));
v___x_463_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_String_trimAsciiStart(lean_object* v_s_464_){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_465_ = lean_unsigned_to_nat(0u);
v___x_466_ = lean_string_utf8_byte_size(v_s_464_);
v___x_467_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_467_, 0, v_s_464_);
lean_ctor_set(v___x_467_, 1, v___x_465_);
lean_ctor_set(v___x_467_, 2, v___x_466_);
v___x_468_ = ((lean_object*)(l_String_trimAsciiEnd___closed__0));
v___x_469_ = lean_obj_once(&l_String_trimAsciiStart___closed__0, &l_String_trimAsciiStart___closed__0_once, _init_l_String_trimAsciiStart___closed__0);
v___x_470_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go(lean_box(0), v___x_467_, v___x_468_, v___x_469_, v___x_465_);
lean_dec_ref(v___x_467_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_trimLeft_spec__0(lean_object* v_s_471_, lean_object* v_curr_472_){
_start:
{
lean_object* v_str_473_; lean_object* v_startInclusive_474_; lean_object* v_endExclusive_475_; lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___y_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v_str_473_ = lean_ctor_get(v_s_471_, 0);
v_startInclusive_474_ = lean_ctor_get(v_s_471_, 1);
v_endExclusive_475_ = lean_ctor_get(v_s_471_, 2);
v___x_476_ = lean_nat_add(v_startInclusive_474_, v_curr_472_);
lean_inc(v_endExclusive_475_);
lean_inc(v___x_476_);
lean_inc_ref(v_str_473_);
v___x_477_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_477_, 0, v_str_473_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
lean_ctor_set(v___x_477_, 2, v_endExclusive_475_);
v___x_486_ = lean_unsigned_to_nat(0u);
v___x_487_ = lean_nat_sub(v_endExclusive_475_, v___x_476_);
v___x_488_ = lean_nat_dec_eq(v___x_486_, v___x_487_);
lean_dec(v___x_487_);
if (v___x_488_ == 0)
{
uint32_t v___x_489_; uint8_t v___y_491_; uint32_t v___x_496_; uint8_t v___x_497_; 
v___x_489_ = lean_string_utf8_get_fast(v_str_473_, v___x_476_);
v___x_496_ = 32;
v___x_497_ = lean_uint32_dec_eq(v___x_489_, v___x_496_);
if (v___x_497_ == 0)
{
uint32_t v___x_498_; uint8_t v___x_499_; 
v___x_498_ = 9;
v___x_499_ = lean_uint32_dec_eq(v___x_489_, v___x_498_);
v___y_491_ = v___x_499_;
goto v___jp_490_;
}
else
{
v___y_491_ = v___x_497_;
goto v___jp_490_;
}
v___jp_490_:
{
if (v___y_491_ == 0)
{
uint32_t v___x_492_; uint8_t v___x_493_; 
v___x_492_ = 13;
v___x_493_ = lean_uint32_dec_eq(v___x_489_, v___x_492_);
if (v___x_493_ == 0)
{
uint32_t v___x_494_; uint8_t v___x_495_; 
v___x_494_ = 10;
v___x_495_ = lean_uint32_dec_eq(v___x_489_, v___x_494_);
v___y_485_ = v___x_495_;
goto v___jp_484_;
}
else
{
v___y_485_ = v___x_493_;
goto v___jp_484_;
}
}
else
{
goto v___jp_478_;
}
}
}
else
{
lean_dec(v___x_476_);
lean_dec(v_curr_472_);
return v___x_477_;
}
v___jp_478_:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_479_ = lean_string_utf8_next_fast(v_str_473_, v___x_476_);
v___x_480_ = lean_nat_sub(v___x_479_, v___x_476_);
lean_dec(v___x_476_);
v___x_481_ = lean_nat_add(v_curr_472_, v___x_480_);
lean_dec(v___x_480_);
v___x_482_ = lean_nat_dec_lt(v_curr_472_, v___x_481_);
lean_dec(v_curr_472_);
if (v___x_482_ == 0)
{
lean_dec(v___x_481_);
return v___x_477_;
}
else
{
lean_dec_ref(v___x_477_);
v_curr_472_ = v___x_481_;
goto _start;
}
}
v___jp_484_:
{
if (v___y_485_ == 0)
{
lean_dec(v___x_476_);
lean_dec(v_curr_472_);
return v___x_477_;
}
else
{
goto v___jp_478_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_trimLeft_spec__0___boxed(lean_object* v_s_500_, lean_object* v_curr_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_trimLeft_spec__0(v_s_500_, v_curr_501_);
lean_dec_ref(v_s_500_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_String_trimLeft(lean_object* v_s_503_){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v_str_508_; lean_object* v_startInclusive_509_; lean_object* v_endExclusive_510_; lean_object* v___x_511_; 
v___x_504_ = lean_unsigned_to_nat(0u);
v___x_505_ = lean_string_utf8_byte_size(v_s_503_);
v___x_506_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_506_, 0, v_s_503_);
lean_ctor_set(v___x_506_, 1, v___x_504_);
lean_ctor_set(v___x_506_, 2, v___x_505_);
v___x_507_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_trimLeft_spec__0(v___x_506_, v___x_504_);
lean_dec_ref(v___x_506_);
v_str_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc_ref(v_str_508_);
v_startInclusive_509_ = lean_ctor_get(v___x_507_, 1);
lean_inc(v_startInclusive_509_);
v_endExclusive_510_ = lean_ctor_get(v___x_507_, 2);
lean_inc(v_endExclusive_510_);
lean_dec_ref(v___x_507_);
v___x_511_ = lean_string_utf8_extract(v_str_508_, v_startInclusive_509_, v_endExclusive_510_);
lean_dec(v_endExclusive_510_);
lean_dec(v_startInclusive_509_);
lean_dec_ref(v_str_508_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimLeft(lean_object* v_s_512_){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = lean_unsigned_to_nat(0u);
v___x_514_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_trimLeft_spec__0(v_s_512_, v___x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimLeft___boxed(lean_object* v_s_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_String_Slice_trimLeft(v_s_515_);
lean_dec_ref(v_s_515_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_String_trimAscii(lean_object* v_s_517_){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_518_ = lean_unsigned_to_nat(0u);
v___x_519_ = lean_string_utf8_byte_size(v_s_517_);
v___x_520_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_520_, 0, v_s_517_);
lean_ctor_set(v___x_520_, 1, v___x_518_);
lean_ctor_set(v___x_520_, 2, v___x_519_);
v___x_521_ = l_String_Slice_trimAscii(v___x_520_);
lean_dec_ref(v___x_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_String_trim(lean_object* v_s_522_){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v_str_527_; lean_object* v_startInclusive_528_; lean_object* v_endExclusive_529_; lean_object* v___x_530_; 
v___x_523_ = lean_unsigned_to_nat(0u);
v___x_524_ = lean_string_utf8_byte_size(v_s_522_);
v___x_525_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_525_, 0, v_s_522_);
lean_ctor_set(v___x_525_, 1, v___x_523_);
lean_ctor_set(v___x_525_, 2, v___x_524_);
v___x_526_ = l_String_Slice_trimAscii(v___x_525_);
lean_dec_ref(v___x_525_);
v_str_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc_ref(v_str_527_);
v_startInclusive_528_ = lean_ctor_get(v___x_526_, 1);
lean_inc(v_startInclusive_528_);
v_endExclusive_529_ = lean_ctor_get(v___x_526_, 2);
lean_inc(v_endExclusive_529_);
lean_dec_ref(v___x_526_);
v___x_530_ = lean_string_utf8_extract(v_str_527_, v_startInclusive_528_, v_endExclusive_529_);
lean_dec(v_endExclusive_529_);
lean_dec(v_startInclusive_528_);
lean_dec_ref(v_str_527_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trim(lean_object* v_s_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_String_Slice_trimAscii(v_s_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trim___boxed(lean_object* v_s_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_String_Slice_trim(v_s_533_);
lean_dec_ref(v_s_533_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* lean_string_trim(lean_object* v_s_535_){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v_str_540_; lean_object* v_startInclusive_541_; lean_object* v_endExclusive_542_; lean_object* v___x_543_; 
v___x_536_ = lean_unsigned_to_nat(0u);
v___x_537_ = lean_string_utf8_byte_size(v_s_535_);
v___x_538_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_538_, 0, v_s_535_);
lean_ctor_set(v___x_538_, 1, v___x_536_);
lean_ctor_set(v___x_538_, 2, v___x_537_);
v___x_539_ = l_String_Slice_trimAscii(v___x_538_);
lean_dec_ref(v___x_538_);
v_str_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc_ref(v_str_540_);
v_startInclusive_541_ = lean_ctor_get(v___x_539_, 1);
lean_inc(v_startInclusive_541_);
v_endExclusive_542_ = lean_ctor_get(v___x_539_, 2);
lean_inc(v_endExclusive_542_);
lean_dec_ref(v___x_539_);
v___x_543_ = lean_string_utf8_extract(v_str_540_, v_startInclusive_541_, v_endExclusive_542_);
lean_dec(v_endExclusive_542_);
lean_dec(v_startInclusive_541_);
lean_dec_ref(v_str_540_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextWhile(lean_object* v_s_544_, lean_object* v_p_545_, lean_object* v_i_546_){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_string_utf8_byte_size(v_s_544_);
v___x_548_ = l_Substring_Raw_takeWhileAux(v_s_544_, v___x_547_, v_p_545_, v_i_546_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextWhile___boxed(lean_object* v_s_549_, lean_object* v_p_550_, lean_object* v_i_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_String_Pos_Raw_nextWhile(v_s_549_, v_p_550_, v_i_551_);
lean_dec_ref(v_s_549_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_String_nextWhile(lean_object* v_s_553_, lean_object* v_p_554_, lean_object* v_i_555_){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = lean_string_utf8_byte_size(v_s_553_);
v___x_557_ = l_Substring_Raw_takeWhileAux(v_s_553_, v___x_556_, v_p_554_, v_i_555_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_String_nextWhile___boxed(lean_object* v_s_558_, lean_object* v_p_559_, lean_object* v_i_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_String_nextWhile(v_s_558_, v_p_559_, v_i_560_);
lean_dec_ref(v_s_558_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0(lean_object* v_p_562_, lean_object* v_s_563_, lean_object* v_stopPos_564_, lean_object* v_i_565_){
_start:
{
uint8_t v___x_566_; 
v___x_566_ = lean_nat_dec_lt(v_i_565_, v_stopPos_564_);
if (v___x_566_ == 0)
{
lean_dec_ref(v_p_562_);
return v_i_565_;
}
else
{
uint32_t v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_567_ = lean_string_utf8_get(v_s_563_, v_i_565_);
v___x_568_ = lean_box_uint32(v___x_567_);
lean_inc_ref(v_p_562_);
v___x_569_ = lean_apply_1(v_p_562_, v___x_568_);
v___x_570_ = lean_unbox(v___x_569_);
if (v___x_570_ == 0)
{
lean_dec_ref(v_p_562_);
return v_i_565_;
}
else
{
lean_object* v___x_571_; 
v___x_571_ = lean_string_utf8_next(v_s_563_, v_i_565_);
lean_dec(v_i_565_);
v_i_565_ = v___x_571_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0___boxed(lean_object* v_p_573_, lean_object* v_s_574_, lean_object* v_stopPos_575_, lean_object* v_i_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0(v_p_573_, v_s_574_, v_stopPos_575_, v_i_576_);
lean_dec(v_stopPos_575_);
lean_dec_ref(v_s_574_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* lean_string_nextwhile(lean_object* v_s_578_, lean_object* v_p_579_, lean_object* v_i_580_){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = lean_string_utf8_byte_size(v_s_578_);
v___x_582_ = l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0(v_p_579_, v_s_578_, v___x_581_, v_i_580_);
lean_dec_ref(v_s_578_);
return v___x_582_;
}
}
LEAN_EXPORT uint8_t l_String_Pos_Raw_nextUntil___lam__0(lean_object* v_p_583_, uint32_t v_c_584_){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_585_ = lean_box_uint32(v_c_584_);
v___x_586_ = lean_apply_1(v_p_583_, v___x_585_);
v___x_587_ = lean_unbox(v___x_586_);
if (v___x_587_ == 0)
{
uint8_t v___x_588_; 
v___x_588_ = 1;
return v___x_588_;
}
else
{
uint8_t v___x_589_; 
v___x_589_ = 0;
return v___x_589_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextUntil___lam__0___boxed(lean_object* v_p_590_, lean_object* v_c_591_){
_start:
{
uint32_t v_c_boxed_592_; uint8_t v_res_593_; lean_object* v_r_594_; 
v_c_boxed_592_ = lean_unbox_uint32(v_c_591_);
lean_dec(v_c_591_);
v_res_593_ = l_String_Pos_Raw_nextUntil___lam__0(v_p_590_, v_c_boxed_592_);
v_r_594_ = lean_box(v_res_593_);
return v_r_594_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextUntil(lean_object* v_s_595_, lean_object* v_p_596_, lean_object* v_i_597_){
_start:
{
lean_object* v___f_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___f_598_ = lean_alloc_closure((void*)(l_String_Pos_Raw_nextUntil___lam__0___boxed), 2, 1);
lean_closure_set(v___f_598_, 0, v_p_596_);
v___x_599_ = lean_string_utf8_byte_size(v_s_595_);
v___x_600_ = l_Substring_Raw_takeWhileAux(v_s_595_, v___x_599_, v___f_598_, v_i_597_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_nextUntil___boxed(lean_object* v_s_601_, lean_object* v_p_602_, lean_object* v_i_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_String_Pos_Raw_nextUntil(v_s_601_, v_p_602_, v_i_603_);
lean_dec_ref(v_s_601_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0(lean_object* v_p_605_, lean_object* v_s_606_, lean_object* v_stopPos_607_, lean_object* v_i_608_){
_start:
{
uint8_t v___x_609_; 
v___x_609_ = lean_nat_dec_lt(v_i_608_, v_stopPos_607_);
if (v___x_609_ == 0)
{
lean_dec_ref(v_p_605_);
return v_i_608_;
}
else
{
uint32_t v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_610_ = lean_string_utf8_get(v_s_606_, v_i_608_);
v___x_611_ = lean_box_uint32(v___x_610_);
lean_inc_ref(v_p_605_);
v___x_612_ = lean_apply_1(v_p_605_, v___x_611_);
v___x_613_ = lean_unbox(v___x_612_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; 
v___x_614_ = lean_string_utf8_next(v_s_606_, v_i_608_);
lean_dec(v_i_608_);
v_i_608_ = v___x_614_;
goto _start;
}
else
{
lean_dec_ref(v_p_605_);
return v_i_608_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0___boxed(lean_object* v_p_616_, lean_object* v_s_617_, lean_object* v_stopPos_618_, lean_object* v_i_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0(v_p_616_, v_s_617_, v_stopPos_618_, v_i_619_);
lean_dec(v_stopPos_618_);
lean_dec_ref(v_s_617_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_String_nextUntil(lean_object* v_s_621_, lean_object* v_p_622_, lean_object* v_i_623_){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = lean_string_utf8_byte_size(v_s_621_);
v___x_625_ = l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0(v_p_622_, v_s_621_, v___x_624_, v_i_623_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_String_nextUntil___boxed(lean_object* v_s_626_, lean_object* v_p_627_, lean_object* v_i_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_String_nextUntil(v_s_626_, v_p_627_, v_i_628_);
lean_dec_ref(v_s_626_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___redArg(lean_object* v_s_630_, lean_object* v_inst_631_){
_start:
{
lean_object* v_dropPrefix_x3f_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_652_; 
v_dropPrefix_x3f_632_ = lean_ctor_get(v_inst_631_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v_inst_631_);
if (v_isSharedCheck_652_ == 0)
{
lean_object* v_unused_653_; lean_object* v_unused_654_; 
v_unused_653_ = lean_ctor_get(v_inst_631_, 2);
lean_dec(v_unused_653_);
v_unused_654_ = lean_ctor_get(v_inst_631_, 1);
lean_dec(v_unused_654_);
v___x_634_ = v_inst_631_;
v_isShared_635_ = v_isSharedCheck_652_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_dropPrefix_x3f_632_);
lean_dec(v_inst_631_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_652_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_636_ = lean_string_utf8_byte_size(v_s_630_);
v___x_637_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_s_630_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 2, v___x_636_);
lean_ctor_set(v___x_634_, 1, v___x_637_);
lean_ctor_set(v___x_634_, 0, v_s_630_);
v___x_639_ = v___x_634_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_s_630_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v___x_637_);
lean_ctor_set(v_reuseFailAlloc_651_, 2, v___x_636_);
v___x_639_ = v_reuseFailAlloc_651_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
lean_object* v___x_640_; 
v___x_640_ = lean_apply_1(v_dropPrefix_x3f_632_, v___x_639_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v___x_641_; 
lean_dec_ref(v_s_630_);
v___x_641_ = lean_box(0);
return v___x_641_;
}
else
{
lean_object* v_val_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_650_; 
v_val_642_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_650_ == 0)
{
v___x_644_ = v___x_640_;
v_isShared_645_ = v_isSharedCheck_650_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_val_642_);
lean_dec(v___x_640_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_650_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_646_; lean_object* v___x_648_; 
v___x_646_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_646_, 0, v_s_630_);
lean_ctor_set(v___x_646_, 1, v_val_642_);
lean_ctor_set(v___x_646_, 2, v___x_636_);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 0, v___x_646_);
v___x_648_ = v___x_644_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_646_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f(lean_object* v_00_u03c1_655_, lean_object* v_s_656_, lean_object* v_pat_657_, lean_object* v_inst_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_String_dropPrefix_x3f___redArg(v_s_656_, v_inst_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___boxed(lean_object* v_00_u03c1_660_, lean_object* v_s_661_, lean_object* v_pat_662_, lean_object* v_inst_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_String_dropPrefix_x3f(v_00_u03c1_660_, v_s_661_, v_pat_662_, v_inst_663_);
lean_dec(v_pat_662_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___redArg(lean_object* v_s_665_, lean_object* v_inst_666_){
_start:
{
lean_object* v_dropSuffix_x3f_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_687_; 
v_dropSuffix_x3f_667_ = lean_ctor_get(v_inst_666_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v_inst_666_);
if (v_isSharedCheck_687_ == 0)
{
lean_object* v_unused_688_; lean_object* v_unused_689_; 
v_unused_688_ = lean_ctor_get(v_inst_666_, 2);
lean_dec(v_unused_688_);
v_unused_689_ = lean_ctor_get(v_inst_666_, 1);
lean_dec(v_unused_689_);
v___x_669_ = v_inst_666_;
v_isShared_670_ = v_isSharedCheck_687_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_dropSuffix_x3f_667_);
lean_dec(v_inst_666_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_687_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_671_ = lean_string_utf8_byte_size(v_s_665_);
v___x_672_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_s_665_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 2, v___x_671_);
lean_ctor_set(v___x_669_, 1, v___x_672_);
lean_ctor_set(v___x_669_, 0, v_s_665_);
v___x_674_ = v___x_669_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_s_665_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_686_, 2, v___x_671_);
v___x_674_ = v_reuseFailAlloc_686_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_675_; 
v___x_675_ = lean_apply_1(v_dropSuffix_x3f_667_, v___x_674_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v___x_676_; 
lean_dec_ref(v_s_665_);
v___x_676_ = lean_box(0);
return v___x_676_;
}
else
{
lean_object* v_val_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_685_; 
v_val_677_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_685_ == 0)
{
v___x_679_ = v___x_675_;
v_isShared_680_ = v_isSharedCheck_685_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_val_677_);
lean_dec(v___x_675_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_685_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_681_; lean_object* v___x_683_; 
v___x_681_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_681_, 0, v_s_665_);
lean_ctor_set(v___x_681_, 1, v___x_672_);
lean_ctor_set(v___x_681_, 2, v_val_677_);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 0, v___x_681_);
v___x_683_ = v___x_679_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_681_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f(lean_object* v_00_u03c1_690_, lean_object* v_s_691_, lean_object* v_pat_692_, lean_object* v_inst_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_String_dropSuffix_x3f___redArg(v_s_691_, v_inst_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix_x3f___boxed(lean_object* v_00_u03c1_695_, lean_object* v_s_696_, lean_object* v_pat_697_, lean_object* v_inst_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_String_dropSuffix_x3f(v_00_u03c1_695_, v_s_696_, v_pat_697_, v_inst_698_);
lean_dec(v_pat_697_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix___redArg(lean_object* v_s_700_, lean_object* v_inst_701_){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_702_ = lean_unsigned_to_nat(0u);
v___x_703_ = lean_string_utf8_byte_size(v_s_700_);
v___x_704_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_704_, 0, v_s_700_);
lean_ctor_set(v___x_704_, 1, v___x_702_);
lean_ctor_set(v___x_704_, 2, v___x_703_);
v___x_705_ = l_String_Slice_dropPrefix___redArg(v___x_704_, v_inst_701_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix(lean_object* v_00_u03c1_706_, lean_object* v_s_707_, lean_object* v_pat_708_, lean_object* v_inst_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_String_dropPrefix___redArg(v_s_707_, v_inst_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix___boxed(lean_object* v_00_u03c1_711_, lean_object* v_s_712_, lean_object* v_pat_713_, lean_object* v_inst_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_String_dropPrefix(v_00_u03c1_711_, v_s_712_, v_pat_713_, v_inst_714_);
lean_dec(v_pat_713_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg(lean_object* v_pre_716_, lean_object* v_s_717_){
_start:
{
lean_object* v_str_718_; lean_object* v_startInclusive_719_; lean_object* v_endExclusive_720_; lean_object* v___x_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v_str_718_ = lean_ctor_get(v_s_717_, 0);
v_startInclusive_719_ = lean_ctor_get(v_s_717_, 1);
v_endExclusive_720_ = lean_ctor_get(v_s_717_, 2);
v___x_721_ = lean_string_utf8_byte_size(v_pre_716_);
v___x_722_ = lean_nat_sub(v_endExclusive_720_, v_startInclusive_719_);
v___x_723_ = lean_nat_dec_le(v___x_721_, v___x_722_);
lean_dec(v___x_722_);
if (v___x_723_ == 0)
{
return v_s_717_;
}
else
{
lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_724_ = lean_unsigned_to_nat(0u);
v___x_725_ = lean_string_memcmp(v_str_718_, v_pre_716_, v_startInclusive_719_, v___x_724_, v___x_721_);
if (v___x_725_ == 0)
{
return v_s_717_;
}
else
{
lean_object* v___x_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_734_; 
lean_inc(v_endExclusive_720_);
lean_inc(v_startInclusive_719_);
lean_inc_ref(v_str_718_);
v___x_726_ = l_String_Slice_pos_x21(v_s_717_, v___x_721_);
v_isSharedCheck_734_ = !lean_is_exclusive(v_s_717_);
if (v_isSharedCheck_734_ == 0)
{
lean_object* v_unused_735_; lean_object* v_unused_736_; lean_object* v_unused_737_; 
v_unused_735_ = lean_ctor_get(v_s_717_, 2);
lean_dec(v_unused_735_);
v_unused_736_ = lean_ctor_get(v_s_717_, 1);
lean_dec(v_unused_736_);
v_unused_737_ = lean_ctor_get(v_s_717_, 0);
lean_dec(v_unused_737_);
v___x_728_ = v_s_717_;
v_isShared_729_ = v_isSharedCheck_734_;
goto v_resetjp_727_;
}
else
{
lean_dec(v_s_717_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_734_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_730_ = lean_nat_add(v_startInclusive_719_, v___x_726_);
lean_dec(v___x_726_);
lean_dec(v_startInclusive_719_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 1, v___x_730_);
v___x_732_ = v___x_728_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_str_718_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v___x_730_);
lean_ctor_set(v_reuseFailAlloc_733_, 2, v_endExclusive_720_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg___boxed(lean_object* v_pre_738_, lean_object* v_s_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg(v_pre_738_, v_s_739_);
lean_dec_ref(v_pre_738_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix___at___00String_stripPrefix_spec__0(lean_object* v_pre_741_, lean_object* v_s_742_, lean_object* v_pat_743_){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_744_ = lean_unsigned_to_nat(0u);
v___x_745_ = lean_string_utf8_byte_size(v_s_742_);
v___x_746_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_746_, 0, v_s_742_);
lean_ctor_set(v___x_746_, 1, v___x_744_);
lean_ctor_set(v___x_746_, 2, v___x_745_);
v___x_747_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg(v_pre_741_, v___x_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix___at___00String_stripPrefix_spec__0___boxed(lean_object* v_pre_748_, lean_object* v_s_749_, lean_object* v_pat_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_String_dropPrefix___at___00String_stripPrefix_spec__0(v_pre_748_, v_s_749_, v_pat_750_);
lean_dec_ref(v_pat_750_);
lean_dec_ref(v_pre_748_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_String_stripPrefix(lean_object* v_s_752_, lean_object* v_pre_753_){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = l_String_dropPrefix___at___00String_stripPrefix_spec__0(v_pre_753_, v_s_752_, v_pre_753_);
v___x_755_ = l_String_Slice_toString(v___x_754_);
lean_dec_ref(v___x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_String_stripPrefix___boxed(lean_object* v_s_756_, lean_object* v_pre_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_String_stripPrefix(v_s_756_, v_pre_757_);
lean_dec_ref(v_pre_757_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0(lean_object* v_pat_759_, lean_object* v_pre_760_, lean_object* v_s_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg(v_pre_760_, v_s_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___boxed(lean_object* v_pat_763_, lean_object* v_pre_764_, lean_object* v_s_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0(v_pat_763_, v_pre_764_, v_s_765_);
lean_dec_ref(v_pre_764_);
lean_dec_ref(v_pat_763_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_Slice_stripPrefix_spec__0(lean_object* v_pre_767_, lean_object* v_s_768_){
_start:
{
lean_object* v_str_769_; lean_object* v_startInclusive_770_; lean_object* v_endExclusive_771_; lean_object* v_str_772_; lean_object* v_startInclusive_773_; lean_object* v_endExclusive_774_; lean_object* v___x_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
v_str_769_ = lean_ctor_get(v_pre_767_, 0);
v_startInclusive_770_ = lean_ctor_get(v_pre_767_, 1);
v_endExclusive_771_ = lean_ctor_get(v_pre_767_, 2);
v_str_772_ = lean_ctor_get(v_s_768_, 0);
v_startInclusive_773_ = lean_ctor_get(v_s_768_, 1);
v_endExclusive_774_ = lean_ctor_get(v_s_768_, 2);
v___x_775_ = lean_nat_sub(v_endExclusive_771_, v_startInclusive_770_);
v___x_776_ = lean_nat_sub(v_endExclusive_774_, v_startInclusive_773_);
v___x_777_ = lean_nat_dec_le(v___x_775_, v___x_776_);
lean_dec(v___x_776_);
if (v___x_777_ == 0)
{
lean_dec(v___x_775_);
return v_s_768_;
}
else
{
uint8_t v___x_778_; 
v___x_778_ = lean_string_memcmp(v_str_772_, v_str_769_, v_startInclusive_773_, v_startInclusive_770_, v___x_775_);
if (v___x_778_ == 0)
{
lean_dec(v___x_775_);
return v_s_768_;
}
else
{
lean_object* v___x_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_787_; 
lean_inc(v_endExclusive_774_);
lean_inc(v_startInclusive_773_);
lean_inc_ref(v_str_772_);
v___x_779_ = l_String_Slice_pos_x21(v_s_768_, v___x_775_);
lean_dec(v___x_775_);
v_isSharedCheck_787_ = !lean_is_exclusive(v_s_768_);
if (v_isSharedCheck_787_ == 0)
{
lean_object* v_unused_788_; lean_object* v_unused_789_; lean_object* v_unused_790_; 
v_unused_788_ = lean_ctor_get(v_s_768_, 2);
lean_dec(v_unused_788_);
v_unused_789_ = lean_ctor_get(v_s_768_, 1);
lean_dec(v_unused_789_);
v_unused_790_ = lean_ctor_get(v_s_768_, 0);
lean_dec(v_unused_790_);
v___x_781_ = v_s_768_;
v_isShared_782_ = v_isSharedCheck_787_;
goto v_resetjp_780_;
}
else
{
lean_dec(v_s_768_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_787_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_783_ = lean_nat_add(v_startInclusive_773_, v___x_779_);
lean_dec(v___x_779_);
lean_dec(v_startInclusive_773_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 1, v___x_783_);
v___x_785_ = v___x_781_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_str_772_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v___x_783_);
lean_ctor_set(v_reuseFailAlloc_786_, 2, v_endExclusive_774_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___at___00String_Slice_stripPrefix_spec__0___boxed(lean_object* v_pre_791_, lean_object* v_s_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_String_Slice_dropPrefix___at___00String_Slice_stripPrefix_spec__0(v_pre_791_, v_s_792_);
lean_dec_ref(v_pre_791_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_stripPrefix(lean_object* v_s_794_, lean_object* v_pre_795_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_String_Slice_dropPrefix___at___00String_Slice_stripPrefix_spec__0(v_pre_795_, v_s_794_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_stripPrefix___boxed(lean_object* v_s_797_, lean_object* v_pre_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_String_Slice_stripPrefix(v_s_797_, v_pre_798_);
lean_dec_ref(v_pre_798_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix___redArg(lean_object* v_s_800_, lean_object* v_inst_801_){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_802_ = lean_unsigned_to_nat(0u);
v___x_803_ = lean_string_utf8_byte_size(v_s_800_);
v___x_804_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_804_, 0, v_s_800_);
lean_ctor_set(v___x_804_, 1, v___x_802_);
lean_ctor_set(v___x_804_, 2, v___x_803_);
v___x_805_ = l_String_Slice_dropSuffix___redArg(v___x_804_, v_inst_801_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix(lean_object* v_00_u03c1_806_, lean_object* v_s_807_, lean_object* v_pat_808_, lean_object* v_inst_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_String_dropSuffix___redArg(v_s_807_, v_inst_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix___boxed(lean_object* v_00_u03c1_811_, lean_object* v_s_812_, lean_object* v_pat_813_, lean_object* v_inst_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_String_dropSuffix(v_00_u03c1_811_, v_s_812_, v_pat_813_, v_inst_814_);
lean_dec(v_pat_813_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0___redArg(lean_object* v_suff_816_, lean_object* v_s_817_){
_start:
{
lean_object* v_str_818_; lean_object* v_startInclusive_819_; lean_object* v_endExclusive_820_; lean_object* v___x_821_; lean_object* v___x_822_; uint8_t v___x_823_; 
v_str_818_ = lean_ctor_get(v_s_817_, 0);
v_startInclusive_819_ = lean_ctor_get(v_s_817_, 1);
v_endExclusive_820_ = lean_ctor_get(v_s_817_, 2);
v___x_821_ = lean_string_utf8_byte_size(v_suff_816_);
v___x_822_ = lean_nat_sub(v_endExclusive_820_, v_startInclusive_819_);
v___x_823_ = lean_nat_dec_le(v___x_821_, v___x_822_);
if (v___x_823_ == 0)
{
lean_dec(v___x_822_);
return v_s_817_;
}
else
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; uint8_t v___x_827_; 
v___x_824_ = lean_unsigned_to_nat(0u);
v___x_825_ = lean_nat_sub(v___x_822_, v___x_821_);
lean_dec(v___x_822_);
v___x_826_ = lean_nat_add(v_startInclusive_819_, v___x_825_);
v___x_827_ = lean_string_memcmp(v_str_818_, v_suff_816_, v___x_826_, v___x_824_, v___x_821_);
lean_dec(v___x_826_);
if (v___x_827_ == 0)
{
lean_dec(v___x_825_);
return v_s_817_;
}
else
{
lean_object* v___x_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_836_; 
lean_inc(v_startInclusive_819_);
lean_inc_ref(v_str_818_);
v___x_828_ = l_String_Slice_pos_x21(v_s_817_, v___x_825_);
lean_dec(v___x_825_);
v_isSharedCheck_836_ = !lean_is_exclusive(v_s_817_);
if (v_isSharedCheck_836_ == 0)
{
lean_object* v_unused_837_; lean_object* v_unused_838_; lean_object* v_unused_839_; 
v_unused_837_ = lean_ctor_get(v_s_817_, 2);
lean_dec(v_unused_837_);
v_unused_838_ = lean_ctor_get(v_s_817_, 1);
lean_dec(v_unused_838_);
v_unused_839_ = lean_ctor_get(v_s_817_, 0);
lean_dec(v_unused_839_);
v___x_830_ = v_s_817_;
v_isShared_831_ = v_isSharedCheck_836_;
goto v_resetjp_829_;
}
else
{
lean_dec(v_s_817_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_836_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_832_; lean_object* v___x_834_; 
v___x_832_ = lean_nat_add(v_startInclusive_819_, v___x_828_);
lean_dec(v___x_828_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 2, v___x_832_);
v___x_834_ = v___x_830_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_str_818_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v_startInclusive_819_);
lean_ctor_set(v_reuseFailAlloc_835_, 2, v___x_832_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0___redArg___boxed(lean_object* v_suff_840_, lean_object* v_s_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0___redArg(v_suff_840_, v_s_841_);
lean_dec_ref(v_suff_840_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix___at___00String_stripSuffix_spec__0(lean_object* v_suff_843_, lean_object* v_s_844_, lean_object* v_pat_845_){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_846_ = lean_unsigned_to_nat(0u);
v___x_847_ = lean_string_utf8_byte_size(v_s_844_);
v___x_848_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_848_, 0, v_s_844_);
lean_ctor_set(v___x_848_, 1, v___x_846_);
lean_ctor_set(v___x_848_, 2, v___x_847_);
v___x_849_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0___redArg(v_suff_843_, v___x_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix___at___00String_stripSuffix_spec__0___boxed(lean_object* v_suff_850_, lean_object* v_s_851_, lean_object* v_pat_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_String_dropSuffix___at___00String_stripSuffix_spec__0(v_suff_850_, v_s_851_, v_pat_852_);
lean_dec_ref(v_pat_852_);
lean_dec_ref(v_suff_850_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_String_stripSuffix(lean_object* v_s_854_, lean_object* v_suff_855_){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = l_String_dropSuffix___at___00String_stripSuffix_spec__0(v_suff_855_, v_s_854_, v_suff_855_);
v___x_857_ = l_String_Slice_toString(v___x_856_);
lean_dec_ref(v___x_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_String_stripSuffix___boxed(lean_object* v_s_858_, lean_object* v_suff_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_String_stripSuffix(v_s_858_, v_suff_859_);
lean_dec_ref(v_suff_859_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0(lean_object* v_pat_861_, lean_object* v_suff_862_, lean_object* v_s_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0___redArg(v_suff_862_, v_s_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0___boxed(lean_object* v_pat_865_, lean_object* v_suff_866_, lean_object* v_s_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0(v_pat_865_, v_suff_866_, v_s_867_);
lean_dec_ref(v_suff_866_);
lean_dec_ref(v_pat_865_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_Slice_stripSuffix_spec__0(lean_object* v_suff_869_, lean_object* v_s_870_){
_start:
{
lean_object* v_str_871_; lean_object* v_startInclusive_872_; lean_object* v_endExclusive_873_; lean_object* v_str_874_; lean_object* v_startInclusive_875_; lean_object* v_endExclusive_876_; lean_object* v___x_877_; lean_object* v___x_878_; uint8_t v___x_879_; 
v_str_871_ = lean_ctor_get(v_suff_869_, 0);
v_startInclusive_872_ = lean_ctor_get(v_suff_869_, 1);
v_endExclusive_873_ = lean_ctor_get(v_suff_869_, 2);
v_str_874_ = lean_ctor_get(v_s_870_, 0);
v_startInclusive_875_ = lean_ctor_get(v_s_870_, 1);
v_endExclusive_876_ = lean_ctor_get(v_s_870_, 2);
v___x_877_ = lean_nat_sub(v_endExclusive_873_, v_startInclusive_872_);
v___x_878_ = lean_nat_sub(v_endExclusive_876_, v_startInclusive_875_);
v___x_879_ = lean_nat_dec_le(v___x_877_, v___x_878_);
if (v___x_879_ == 0)
{
lean_dec(v___x_878_);
lean_dec(v___x_877_);
return v_s_870_;
}
else
{
lean_object* v___x_880_; lean_object* v___x_881_; uint8_t v___x_882_; 
v___x_880_ = lean_nat_sub(v___x_878_, v___x_877_);
lean_dec(v___x_878_);
v___x_881_ = lean_nat_add(v_startInclusive_875_, v___x_880_);
v___x_882_ = lean_string_memcmp(v_str_874_, v_str_871_, v___x_881_, v_startInclusive_872_, v___x_877_);
lean_dec(v___x_877_);
lean_dec(v___x_881_);
if (v___x_882_ == 0)
{
lean_dec(v___x_880_);
return v_s_870_;
}
else
{
lean_object* v___x_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_891_; 
lean_inc(v_startInclusive_875_);
lean_inc_ref(v_str_874_);
v___x_883_ = l_String_Slice_pos_x21(v_s_870_, v___x_880_);
lean_dec(v___x_880_);
v_isSharedCheck_891_ = !lean_is_exclusive(v_s_870_);
if (v_isSharedCheck_891_ == 0)
{
lean_object* v_unused_892_; lean_object* v_unused_893_; lean_object* v_unused_894_; 
v_unused_892_ = lean_ctor_get(v_s_870_, 2);
lean_dec(v_unused_892_);
v_unused_893_ = lean_ctor_get(v_s_870_, 1);
lean_dec(v_unused_893_);
v_unused_894_ = lean_ctor_get(v_s_870_, 0);
lean_dec(v_unused_894_);
v___x_885_ = v_s_870_;
v_isShared_886_ = v_isSharedCheck_891_;
goto v_resetjp_884_;
}
else
{
lean_dec(v_s_870_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_891_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; lean_object* v___x_889_; 
v___x_887_ = lean_nat_add(v_startInclusive_875_, v___x_883_);
lean_dec(v___x_883_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 2, v___x_887_);
v___x_889_ = v___x_885_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_str_874_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v_startInclusive_875_);
lean_ctor_set(v_reuseFailAlloc_890_, 2, v___x_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_Slice_stripSuffix_spec__0___boxed(lean_object* v_suff_895_, lean_object* v_s_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_String_Slice_dropSuffix___at___00String_Slice_stripSuffix_spec__0(v_suff_895_, v_s_896_);
lean_dec_ref(v_suff_895_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_stripSuffix(lean_object* v_s_898_, lean_object* v_suff_899_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_String_Slice_dropSuffix___at___00String_Slice_stripSuffix_spec__0(v_suff_899_, v_s_898_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_stripSuffix___boxed(lean_object* v_s_901_, lean_object* v_suff_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_String_Slice_stripSuffix(v_s_901_, v_suff_902_);
lean_dec_ref(v_suff_902_);
return v_res_903_;
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

// Lean compiler output
// Module: Init.Data.String.Substring
// Imports: public import Init.Data.String.Slice import Init.Data.Option.BasicAux
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
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_Char_isWhitespace___boxed(lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_instInhabitedSlice;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t l_String_Pos_Raw_substrEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(lean_object*);
lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
uint8_t l_String_Slice_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
lean_object* l_String_Slice_revPositions(lean_object*);
lean_object* l_String_Slice_Pos_skipWhile___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_ofSlice(lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_toSlice_x3f(lean_object*);
LEAN_EXPORT uint8_t l_Substring_Raw_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_isEmpty___boxed(lean_object*);
LEAN_EXPORT uint8_t lean_substring_isempty(lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_isEmptyImpl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_toString(lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_toString___boxed(lean_object*);
LEAN_EXPORT lean_object* lean_substring_tostring(lean_object*);
LEAN_EXPORT uint32_t l_Substring_Raw_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_get___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t lean_substring_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_getImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_next___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_prev___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_substring_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_nextn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_prevn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_prevn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Substring_Raw_front(lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_front___boxed(lean_object*);
LEAN_EXPORT uint32_t lean_substring_front(lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_frontImpl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_posOf___lam__0(lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_posOf___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_posOf(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Substring_Raw_posOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_drop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_substring_drop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_dropRight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeRight(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Substring_Raw_atEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_atEnd___boxed(lean_object*, lean_object*);
static const lean_string_object l_Substring_Raw_extract___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Substring_Raw_extract___closed__0 = (const lean_object*)&l_Substring_Raw_extract___closed__0_value;
static const lean_ctor_object l_Substring_Raw_extract___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Substring_Raw_extract___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Substring_Raw_extract___closed__1 = (const lean_object*)&l_Substring_Raw_extract___closed__1_value;
LEAN_EXPORT lean_object* l_Substring_Raw_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_extract___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_substring_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_splitOn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_splitOn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_foldl___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_foldl___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Substring_Raw_foldl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Substring_Raw_foldl___redArg___closed__0 = (const lean_object*)&l_Substring_Raw_foldl___redArg___closed__0_value;
static const lean_string_object l_Substring_Raw_foldl___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Substring_Raw_foldl___redArg___closed__1 = (const lean_object*)&l_Substring_Raw_foldl___redArg___closed__1_value;
static const lean_string_object l_Substring_Raw_foldl___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Substring_Raw_foldl___redArg___closed__2 = (const lean_object*)&l_Substring_Raw_foldl___redArg___closed__2_value;
static lean_once_cell_t l_Substring_Raw_foldl___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Substring_Raw_foldl___redArg___closed__3;
LEAN_EXPORT lean_object* l_Substring_Raw_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_foldl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_foldr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_foldr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_foldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_foldr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_any___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Substring_Raw_any(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_any___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Substring_Raw_all(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_all___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_substring_all(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_allImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Substring_Raw_contains___lam__0(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Substring_Raw_contains___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Substring_Raw_contains(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Substring_Raw_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_substring_takewhile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_dropWhile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_dropRightWhile(lean_object*, lean_object*);
static const lean_closure_object l_Substring_Raw_trimLeft___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Char_isWhitespace___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Substring_Raw_trimLeft___closed__0 = (const lean_object*)&l_Substring_Raw_trimLeft___closed__0_value;
LEAN_EXPORT lean_object* l_Substring_Raw_trimLeft(lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_trimRight(lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_trim(lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Substring_Raw_isNat(lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_toNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_repair(lean_object*);
LEAN_EXPORT uint8_t l_Substring_Raw_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_substring_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_beqImpl___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Substring_Raw_hasBeq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Substring_Raw_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Substring_Raw_hasBeq___closed__0 = (const lean_object*)&l_Substring_Raw_hasBeq___closed__0_value;
LEAN_EXPORT const lean_object* l_Substring_Raw_hasBeq = (const lean_object*)&l_Substring_Raw_hasBeq___closed__0_value;
LEAN_EXPORT uint8_t l_Substring_Raw_sameAs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_sameAs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_commonPrefix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_commonSuffix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_dropPrefix_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_dropSuffix_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_bsize(lean_object*);
LEAN_EXPORT lean_object* l_Substring_bsize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Substring_toString(lean_object*);
LEAN_EXPORT lean_object* l_Substring_toString___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Substring_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Substring_isEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Substring_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_next___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_prev___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Substring_atEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_atEnd___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Substring_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_ofSlice(lean_object* v_s_1_){
_start:
{
lean_object* v_str_2_; lean_object* v_startInclusive_3_; lean_object* v_endExclusive_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_11_; 
v_str_2_ = lean_ctor_get(v_s_1_, 0);
v_startInclusive_3_ = lean_ctor_get(v_s_1_, 1);
v_endExclusive_4_ = lean_ctor_get(v_s_1_, 2);
v_isSharedCheck_11_ = !lean_is_exclusive(v_s_1_);
if (v_isSharedCheck_11_ == 0)
{
v___x_6_ = v_s_1_;
v_isShared_7_ = v_isSharedCheck_11_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_endExclusive_4_);
lean_inc(v_startInclusive_3_);
lean_inc(v_str_2_);
lean_dec(v_s_1_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_11_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
lean_object* v___x_9_; 
if (v_isShared_7_ == 0)
{
v___x_9_ = v___x_6_;
goto v_reusejp_8_;
}
else
{
lean_object* v_reuseFailAlloc_10_; 
v_reuseFailAlloc_10_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_10_, 0, v_str_2_);
lean_ctor_set(v_reuseFailAlloc_10_, 1, v_startInclusive_3_);
lean_ctor_set(v_reuseFailAlloc_10_, 2, v_endExclusive_4_);
v___x_9_ = v_reuseFailAlloc_10_;
goto v_reusejp_8_;
}
v_reusejp_8_:
{
return v___x_9_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toSlice_x3f(lean_object* v_s_12_){
_start:
{
lean_object* v_str_13_; lean_object* v_startPos_14_; lean_object* v_stopPos_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_29_; 
v_str_13_ = lean_ctor_get(v_s_12_, 0);
v_startPos_14_ = lean_ctor_get(v_s_12_, 1);
v_stopPos_15_ = lean_ctor_get(v_s_12_, 2);
v_isSharedCheck_29_ = !lean_is_exclusive(v_s_12_);
if (v_isSharedCheck_29_ == 0)
{
v___x_17_ = v_s_12_;
v_isShared_18_ = v_isSharedCheck_29_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_stopPos_15_);
lean_inc(v_startPos_14_);
lean_inc(v_str_13_);
lean_dec(v_s_12_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_29_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
uint8_t v___y_20_; uint8_t v___x_26_; 
v___x_26_ = lean_string_is_valid_pos(v_str_13_, v_startPos_14_);
if (v___x_26_ == 0)
{
v___y_20_ = v___x_26_;
goto v___jp_19_;
}
else
{
uint8_t v___x_27_; 
v___x_27_ = lean_string_is_valid_pos(v_str_13_, v_stopPos_15_);
if (v___x_27_ == 0)
{
v___y_20_ = v___x_27_;
goto v___jp_19_;
}
else
{
uint8_t v___x_28_; 
v___x_28_ = lean_nat_dec_le(v_startPos_14_, v_stopPos_15_);
v___y_20_ = v___x_28_;
goto v___jp_19_;
}
}
v___jp_19_:
{
if (v___y_20_ == 0)
{
lean_object* v___x_21_; 
lean_del_object(v___x_17_);
lean_dec(v_stopPos_15_);
lean_dec(v_startPos_14_);
lean_dec_ref(v_str_13_);
v___x_21_ = lean_box(0);
return v___x_21_;
}
else
{
lean_object* v___x_23_; 
if (v_isShared_18_ == 0)
{
v___x_23_ = v___x_17_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v_str_13_);
lean_ctor_set(v_reuseFailAlloc_25_, 1, v_startPos_14_);
lean_ctor_set(v_reuseFailAlloc_25_, 2, v_stopPos_15_);
v___x_23_ = v_reuseFailAlloc_25_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
lean_object* v___x_24_; 
v___x_24_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_24_, 0, v___x_23_);
return v___x_24_;
}
}
}
}
}
}
uint8_t l_Substring_Raw_isEmpty(lean_object* v_ss_30_){
_start:
{
lean_object* v_startPos_31_; lean_object* v_stopPos_32_; lean_object* v___x_33_; lean_object* v___x_34_; uint8_t v___x_35_; 
v_startPos_31_ = lean_ctor_get(v_ss_30_, 1);
v_stopPos_32_ = lean_ctor_get(v_ss_30_, 2);
v___x_33_ = lean_nat_sub(v_stopPos_32_, v_startPos_31_);
v___x_34_ = lean_unsigned_to_nat(0u);
v___x_35_ = lean_nat_dec_eq(v___x_33_, v___x_34_);
lean_dec(v___x_33_);
return v___x_35_;
}
}
LEAN_EXPORT void l_Substring_Raw_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_ss_30_ = stack[0].m_obj;
uint8_t v_res_36_;
v_res_36_ = l_Substring_Raw_isEmpty(v_ss_30_);
stack->m_num = v_res_36_;
}
LEAN_EXPORT lean_object* l_Substring_Raw_isEmpty___boxed(lean_object* v_ss_37_){
_start:
{
uint8_t v_res_38_; lean_object* v_r_39_; 
v_res_38_ = l_Substring_Raw_isEmpty(v_ss_37_);
lean_dec_ref(v_ss_37_);
v_r_39_ = lean_box(v_res_38_);
return v_r_39_;
}
}
uint8_t lean_substring_isempty(lean_object* v_ss_40_){
_start:
{
lean_object* v_startPos_41_; lean_object* v_stopPos_42_; lean_object* v___x_43_; lean_object* v___x_44_; uint8_t v___x_45_; 
v_startPos_41_ = lean_ctor_get(v_ss_40_, 1);
lean_inc(v_startPos_41_);
v_stopPos_42_ = lean_ctor_get(v_ss_40_, 2);
lean_inc(v_stopPos_42_);
lean_dec_ref(v_ss_40_);
v___x_43_ = lean_nat_sub(v_stopPos_42_, v_startPos_41_);
lean_dec(v_startPos_41_);
lean_dec(v_stopPos_42_);
v___x_44_ = lean_unsigned_to_nat(0u);
v___x_45_ = lean_nat_dec_eq(v___x_43_, v___x_44_);
lean_dec(v___x_43_);
return v___x_45_;
}
}
LEAN_EXPORT void lean_substring_isempty_0interp(lean_interpreter_value* stack)
{
lean_object* v_ss_40_ = stack[0].m_obj;
uint8_t v_res_46_;
v_res_46_ = lean_substring_isempty(v_ss_40_);
stack->m_num = v_res_46_;
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_isEmptyImpl___boxed(lean_object* v_ss_47_){
_start:
{
uint8_t v_res_48_; lean_object* v_r_49_; 
v_res_48_ = lean_substring_isempty(v_ss_47_);
v_r_49_ = lean_box(v_res_48_);
return v_r_49_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toString(lean_object* v_x_50_){
_start:
{
lean_object* v_str_51_; lean_object* v_startPos_52_; lean_object* v_stopPos_53_; lean_object* v___x_54_; 
v_str_51_ = lean_ctor_get(v_x_50_, 0);
v_startPos_52_ = lean_ctor_get(v_x_50_, 1);
v_stopPos_53_ = lean_ctor_get(v_x_50_, 2);
v___x_54_ = lean_string_utf8_extract(v_str_51_, v_startPos_52_, v_stopPos_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toString___boxed(lean_object* v_x_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Substring_Raw_toString(v_x_55_);
lean_dec_ref(v_x_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* lean_substring_tostring(lean_object* v_a_57_){
_start:
{
lean_object* v_str_58_; lean_object* v_startPos_59_; lean_object* v_stopPos_60_; lean_object* v___x_61_; 
v_str_58_ = lean_ctor_get(v_a_57_, 0);
lean_inc_ref(v_str_58_);
v_startPos_59_ = lean_ctor_get(v_a_57_, 1);
lean_inc(v_startPos_59_);
v_stopPos_60_ = lean_ctor_get(v_a_57_, 2);
lean_inc(v_stopPos_60_);
lean_dec_ref(v_a_57_);
v___x_61_ = lean_string_utf8_extract(v_str_58_, v_startPos_59_, v_stopPos_60_);
lean_dec(v_stopPos_60_);
lean_dec(v_startPos_59_);
lean_dec_ref(v_str_58_);
return v___x_61_;
}
}
uint32_t l_Substring_Raw_get(lean_object* v_x_62_, lean_object* v_x_63_){
_start:
{
lean_object* v_str_64_; lean_object* v_startPos_65_; lean_object* v___x_66_; uint32_t v___x_67_; 
v_str_64_ = lean_ctor_get(v_x_62_, 0);
v_startPos_65_ = lean_ctor_get(v_x_62_, 1);
v___x_66_ = lean_nat_add(v_startPos_65_, v_x_63_);
v___x_67_ = lean_string_utf8_get(v_str_64_, v___x_66_);
lean_dec(v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT void l_Substring_Raw_get_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_62_ = stack[0].m_obj;
lean_object* v_x_63_ = stack[1].m_obj;
uint32_t v_res_68_;
v_res_68_ = l_Substring_Raw_get(v_x_62_, v_x_63_);
stack->m_num = v_res_68_;
}
LEAN_EXPORT lean_object* l_Substring_Raw_get___boxed(lean_object* v_x_69_, lean_object* v_x_70_){
_start:
{
uint32_t v_res_71_; lean_object* v_r_72_; 
v_res_71_ = l_Substring_Raw_get(v_x_69_, v_x_70_);
lean_dec(v_x_70_);
lean_dec_ref(v_x_69_);
v_r_72_ = lean_box_uint32(v_res_71_);
return v_r_72_;
}
}
uint32_t lean_substring_get(lean_object* v_a_73_, lean_object* v_a_74_){
_start:
{
lean_object* v_str_75_; lean_object* v_startPos_76_; lean_object* v___x_77_; uint32_t v___x_78_; 
v_str_75_ = lean_ctor_get(v_a_73_, 0);
lean_inc_ref(v_str_75_);
v_startPos_76_ = lean_ctor_get(v_a_73_, 1);
lean_inc(v_startPos_76_);
lean_dec_ref(v_a_73_);
v___x_77_ = lean_nat_add(v_startPos_76_, v_a_74_);
lean_dec(v_a_74_);
lean_dec(v_startPos_76_);
v___x_78_ = lean_string_utf8_get(v_str_75_, v___x_77_);
lean_dec(v___x_77_);
lean_dec_ref(v_str_75_);
return v___x_78_;
}
}
LEAN_EXPORT void lean_substring_get_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_73_ = stack[0].m_obj;
lean_object* v_a_74_ = stack[1].m_obj;
uint32_t v_res_79_;
v_res_79_ = lean_substring_get(v_a_73_, v_a_74_);
stack->m_num = v_res_79_;
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_getImpl___boxed(lean_object* v_a_80_, lean_object* v_a_81_){
_start:
{
uint32_t v_res_82_; lean_object* v_r_83_; 
v_res_82_ = lean_substring_get(v_a_80_, v_a_81_);
v_r_83_ = lean_box_uint32(v_res_82_);
return v_r_83_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_next(lean_object* v_x_84_, lean_object* v_x_85_){
_start:
{
lean_object* v_str_86_; lean_object* v_startPos_87_; lean_object* v_stopPos_88_; lean_object* v_absP_89_; uint8_t v_decide_90_; 
v_str_86_ = lean_ctor_get(v_x_84_, 0);
v_startPos_87_ = lean_ctor_get(v_x_84_, 1);
v_stopPos_88_ = lean_ctor_get(v_x_84_, 2);
v_absP_89_ = lean_nat_add(v_startPos_87_, v_x_85_);
v_decide_90_ = lean_nat_dec_eq(v_absP_89_, v_stopPos_88_);
if (v_decide_90_ == 0)
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_string_utf8_next(v_str_86_, v_absP_89_);
lean_dec(v_absP_89_);
v___x_92_ = lean_nat_sub(v___x_91_, v_startPos_87_);
lean_dec(v___x_91_);
return v___x_92_;
}
else
{
lean_dec(v_absP_89_);
lean_inc(v_x_85_);
return v_x_85_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_next___boxed(lean_object* v_x_93_, lean_object* v_x_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Substring_Raw_next(v_x_93_, v_x_94_);
lean_dec(v_x_94_);
lean_dec_ref(v_x_93_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_prev(lean_object* v_x_96_, lean_object* v_x_97_){
_start:
{
lean_object* v_str_98_; lean_object* v_startPos_99_; lean_object* v_absP_100_; uint8_t v_decide_101_; 
v_str_98_ = lean_ctor_get(v_x_96_, 0);
v_startPos_99_ = lean_ctor_get(v_x_96_, 1);
v_absP_100_ = lean_nat_add(v_startPos_99_, v_x_97_);
v_decide_101_ = lean_nat_dec_eq(v_absP_100_, v_startPos_99_);
if (v_decide_101_ == 0)
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_string_utf8_prev(v_str_98_, v_absP_100_);
lean_dec(v_absP_100_);
v___x_103_ = lean_nat_sub(v___x_102_, v_startPos_99_);
lean_dec(v___x_102_);
return v___x_103_;
}
else
{
lean_dec(v_absP_100_);
lean_inc(v_x_97_);
return v_x_97_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_prev___boxed(lean_object* v_x_104_, lean_object* v_x_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Substring_Raw_prev(v_x_104_, v_x_105_);
lean_dec(v_x_105_);
lean_dec_ref(v_x_104_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* lean_substring_prev(lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v_str_109_; lean_object* v_startPos_110_; lean_object* v_absP_111_; uint8_t v_decide_112_; 
v_str_109_ = lean_ctor_get(v_a_107_, 0);
lean_inc_ref(v_str_109_);
v_startPos_110_ = lean_ctor_get(v_a_107_, 1);
lean_inc(v_startPos_110_);
lean_dec_ref(v_a_107_);
v_absP_111_ = lean_nat_add(v_startPos_110_, v_a_108_);
v_decide_112_ = lean_nat_dec_eq(v_absP_111_, v_startPos_110_);
if (v_decide_112_ == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; 
lean_dec(v_a_108_);
v___x_113_ = lean_string_utf8_prev(v_str_109_, v_absP_111_);
lean_dec(v_absP_111_);
lean_dec_ref(v_str_109_);
v___x_114_ = lean_nat_sub(v___x_113_, v_startPos_110_);
lean_dec(v_startPos_110_);
lean_dec(v___x_113_);
return v___x_114_;
}
else
{
lean_dec(v_absP_111_);
lean_dec(v_startPos_110_);
lean_dec_ref(v_str_109_);
return v_a_108_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_nextn(lean_object* v_x_115_, lean_object* v_x_116_, lean_object* v_x_117_){
_start:
{
lean_object* v_zero_118_; uint8_t v_isZero_119_; 
v_zero_118_ = lean_unsigned_to_nat(0u);
v_isZero_119_ = lean_nat_dec_eq(v_x_116_, v_zero_118_);
if (v_isZero_119_ == 1)
{
lean_dec(v_x_116_);
return v_x_117_;
}
else
{
lean_object* v_str_120_; lean_object* v_startPos_121_; lean_object* v_stopPos_122_; lean_object* v_one_123_; lean_object* v_n_124_; lean_object* v_absP_125_; uint8_t v_decide_126_; 
v_str_120_ = lean_ctor_get(v_x_115_, 0);
v_startPos_121_ = lean_ctor_get(v_x_115_, 1);
v_stopPos_122_ = lean_ctor_get(v_x_115_, 2);
v_one_123_ = lean_unsigned_to_nat(1u);
v_n_124_ = lean_nat_sub(v_x_116_, v_one_123_);
lean_dec(v_x_116_);
v_absP_125_ = lean_nat_add(v_startPos_121_, v_x_117_);
v_decide_126_ = lean_nat_dec_eq(v_absP_125_, v_stopPos_122_);
if (v_decide_126_ == 0)
{
lean_object* v___x_127_; lean_object* v___x_128_; 
lean_dec(v_x_117_);
v___x_127_ = lean_string_utf8_next(v_str_120_, v_absP_125_);
lean_dec(v_absP_125_);
v___x_128_ = lean_nat_sub(v___x_127_, v_startPos_121_);
lean_dec(v___x_127_);
v_x_116_ = v_n_124_;
v_x_117_ = v___x_128_;
goto _start;
}
else
{
lean_dec(v_absP_125_);
v_x_116_ = v_n_124_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_nextn___boxed(lean_object* v_x_131_, lean_object* v_x_132_, lean_object* v_x_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Substring_Raw_nextn(v_x_131_, v_x_132_, v_x_133_);
lean_dec_ref(v_x_131_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_prevn(lean_object* v_x_135_, lean_object* v_x_136_, lean_object* v_x_137_){
_start:
{
lean_object* v_zero_138_; uint8_t v_isZero_139_; 
v_zero_138_ = lean_unsigned_to_nat(0u);
v_isZero_139_ = lean_nat_dec_eq(v_x_136_, v_zero_138_);
if (v_isZero_139_ == 1)
{
lean_dec(v_x_136_);
return v_x_137_;
}
else
{
lean_object* v_str_140_; lean_object* v_startPos_141_; lean_object* v_one_142_; lean_object* v_n_143_; lean_object* v_absP_144_; uint8_t v_decide_145_; 
v_str_140_ = lean_ctor_get(v_x_135_, 0);
v_startPos_141_ = lean_ctor_get(v_x_135_, 1);
v_one_142_ = lean_unsigned_to_nat(1u);
v_n_143_ = lean_nat_sub(v_x_136_, v_one_142_);
lean_dec(v_x_136_);
v_absP_144_ = lean_nat_add(v_startPos_141_, v_x_137_);
v_decide_145_ = lean_nat_dec_eq(v_absP_144_, v_startPos_141_);
if (v_decide_145_ == 0)
{
lean_object* v___x_146_; lean_object* v___x_147_; 
lean_dec(v_x_137_);
v___x_146_ = lean_string_utf8_prev(v_str_140_, v_absP_144_);
lean_dec(v_absP_144_);
v___x_147_ = lean_nat_sub(v___x_146_, v_startPos_141_);
lean_dec(v___x_146_);
v_x_136_ = v_n_143_;
v_x_137_ = v___x_147_;
goto _start;
}
else
{
lean_dec(v_absP_144_);
v_x_136_ = v_n_143_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_prevn___boxed(lean_object* v_x_150_, lean_object* v_x_151_, lean_object* v_x_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Substring_Raw_prevn(v_x_150_, v_x_151_, v_x_152_);
lean_dec_ref(v_x_150_);
return v_res_153_;
}
}
uint32_t l_Substring_Raw_front(lean_object* v_s_154_){
_start:
{
lean_object* v_str_155_; lean_object* v_startPos_156_; uint32_t v___x_157_; 
v_str_155_ = lean_ctor_get(v_s_154_, 0);
v_startPos_156_ = lean_ctor_get(v_s_154_, 1);
v___x_157_ = lean_string_utf8_get(v_str_155_, v_startPos_156_);
return v___x_157_;
}
}
LEAN_EXPORT void l_Substring_Raw_front_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_154_ = stack[0].m_obj;
uint32_t v_res_158_;
v_res_158_ = l_Substring_Raw_front(v_s_154_);
stack->m_num = v_res_158_;
}
LEAN_EXPORT lean_object* l_Substring_Raw_front___boxed(lean_object* v_s_159_){
_start:
{
uint32_t v_res_160_; lean_object* v_r_161_; 
v_res_160_ = l_Substring_Raw_front(v_s_159_);
lean_dec_ref(v_s_159_);
v_r_161_ = lean_box_uint32(v_res_160_);
return v_r_161_;
}
}
uint32_t lean_substring_front(lean_object* v_s_162_){
_start:
{
lean_object* v_str_163_; lean_object* v_startPos_164_; uint32_t v___x_165_; 
v_str_163_ = lean_ctor_get(v_s_162_, 0);
lean_inc_ref(v_str_163_);
v_startPos_164_ = lean_ctor_get(v_s_162_, 1);
lean_inc(v_startPos_164_);
lean_dec_ref(v_s_162_);
v___x_165_ = lean_string_utf8_get(v_str_163_, v_startPos_164_);
lean_dec(v_startPos_164_);
lean_dec_ref(v_str_163_);
return v___x_165_;
}
}
LEAN_EXPORT void lean_substring_front_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_162_ = stack[0].m_obj;
uint32_t v_res_166_;
v_res_166_ = lean_substring_front(v_s_162_);
stack->m_num = v_res_166_;
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_frontImpl___boxed(lean_object* v_s_167_){
_start:
{
uint32_t v_res_168_; lean_object* v_r_169_; 
v_res_168_ = lean_substring_front(v_s_167_);
v_r_169_ = lean_box_uint32(v_res_168_);
return v_r_169_;
}
}
lean_object* l_Substring_Raw_posOf___lam__0(lean_object* v_stopPos_170_, lean_object* v_startPos_171_, lean_object* v_str_172_, uint32_t v_c_173_, lean_object* v___x_174_, lean_object* v_it_175_, lean_object* v_acc_176_, lean_object* v_hP_177_, lean_object* v_recur_178_){
_start:
{
lean_object* v___x_179_; uint8_t v_decide_180_; 
v___x_179_ = lean_nat_sub(v_stopPos_170_, v_startPos_171_);
v_decide_180_ = lean_nat_dec_eq(v_it_175_, v___x_179_);
lean_dec(v___x_179_);
if (v_decide_180_ == 0)
{
lean_object* v___x_181_; uint32_t v___x_182_; uint8_t v___x_183_; 
v___x_181_ = lean_nat_add(v_startPos_171_, v_it_175_);
v___x_182_ = lean_string_utf8_get_fast(v_str_172_, v___x_181_);
v___x_183_ = lean_uint32_dec_eq(v___x_182_, v_c_173_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
lean_dec(v_it_175_);
v___x_184_ = lean_string_utf8_next_fast(v_str_172_, v___x_181_);
lean_dec(v___x_181_);
v___x_185_ = lean_nat_sub(v___x_184_, v_startPos_171_);
v___x_186_ = lean_apply_4(v_recur_178_, v___x_185_, v___x_174_, lean_box(0), lean_box(0));
return v___x_186_;
}
else
{
lean_object* v___x_187_; 
lean_dec(v___x_181_);
lean_dec_ref(v_recur_178_);
lean_dec(v___x_174_);
v___x_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_187_, 0, v_it_175_);
return v___x_187_;
}
}
else
{
lean_dec_ref(v_recur_178_);
lean_dec(v_it_175_);
lean_dec(v___x_174_);
lean_inc(v_acc_176_);
return v_acc_176_;
}
}
}
LEAN_EXPORT void l_Substring_Raw_posOf___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_stopPos_170_ = stack[0].m_obj;
lean_object* v_startPos_171_ = stack[1].m_obj;
lean_object* v_str_172_ = stack[2].m_obj;
uint32_t v_c_173_ = stack[3].m_num;
lean_object* v___x_174_ = stack[4].m_obj;
lean_object* v_it_175_ = stack[5].m_obj;
lean_object* v_acc_176_ = stack[6].m_obj;
lean_object* v_recur_178_ = stack[8].m_obj;
lean_object* v_res_188_;
v_res_188_ = l_Substring_Raw_posOf___lam__0(v_stopPos_170_, v_startPos_171_, v_str_172_, v_c_173_, v___x_174_, v_it_175_, v_acc_176_, lean_box(0), v_recur_178_);
stack->m_obj
 = v_res_188_;
}
LEAN_EXPORT lean_object* l_Substring_Raw_posOf___lam__0___boxed(lean_object* v_stopPos_189_, lean_object* v_startPos_190_, lean_object* v_str_191_, lean_object* v_c_192_, lean_object* v___x_193_, lean_object* v_it_194_, lean_object* v_acc_195_, lean_object* v_hP_196_, lean_object* v_recur_197_){
_start:
{
uint32_t v_c_boxed_198_; lean_object* v_res_199_; 
v_c_boxed_198_ = lean_unbox_uint32(v_c_192_);
lean_dec(v_c_192_);
v_res_199_ = l_Substring_Raw_posOf___lam__0(v_stopPos_189_, v_startPos_190_, v_str_191_, v_c_boxed_198_, v___x_193_, v_it_194_, v_acc_195_, v_hP_196_, v_recur_197_);
lean_dec(v_acc_195_);
lean_dec_ref(v_str_191_);
lean_dec(v_startPos_190_);
lean_dec(v_stopPos_189_);
return v_res_199_;
}
}
lean_object* l_Substring_Raw_posOf(lean_object* v_s_200_, uint32_t v_c_201_){
_start:
{
lean_object* v_str_202_; lean_object* v_startPos_203_; lean_object* v_stopPos_204_; uint8_t v___y_206_; uint8_t v___x_215_; 
v_str_202_ = lean_ctor_get(v_s_200_, 0);
lean_inc_ref(v_str_202_);
v_startPos_203_ = lean_ctor_get(v_s_200_, 1);
lean_inc(v_startPos_203_);
v_stopPos_204_ = lean_ctor_get(v_s_200_, 2);
lean_inc(v_stopPos_204_);
lean_dec_ref(v_s_200_);
v___x_215_ = lean_string_is_valid_pos(v_str_202_, v_startPos_203_);
if (v___x_215_ == 0)
{
v___y_206_ = v___x_215_;
goto v___jp_205_;
}
else
{
uint8_t v___x_216_; 
v___x_216_ = lean_string_is_valid_pos(v_str_202_, v_stopPos_204_);
if (v___x_216_ == 0)
{
v___y_206_ = v___x_216_;
goto v___jp_205_;
}
else
{
uint8_t v___x_217_; 
v___x_217_ = lean_nat_dec_le(v_startPos_203_, v_stopPos_204_);
v___y_206_ = v___x_217_;
goto v___jp_205_;
}
}
v___jp_205_:
{
if (v___y_206_ == 0)
{
lean_object* v___x_207_; 
lean_dec_ref(v_str_202_);
v___x_207_ = lean_nat_sub(v_stopPos_204_, v_startPos_203_);
lean_dec(v_startPos_203_);
lean_dec(v_stopPos_204_);
return v___x_207_;
}
else
{
lean_object* v_searcher_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___f_211_; lean_object* v___x_212_; 
v_searcher_208_ = lean_unsigned_to_nat(0u);
v___x_209_ = lean_box(0);
v___x_210_ = lean_box_uint32(v_c_201_);
lean_inc(v_startPos_203_);
lean_inc(v_stopPos_204_);
v___f_211_ = lean_alloc_closure((void*)(l_Substring_Raw_posOf___lam__0___boxed), 9, 5);
lean_closure_set(v___f_211_, 0, v_stopPos_204_);
lean_closure_set(v___f_211_, 1, v_startPos_203_);
lean_closure_set(v___f_211_, 2, v_str_202_);
lean_closure_set(v___f_211_, 3, v___x_210_);
lean_closure_set(v___f_211_, 4, v___x_209_);
v___x_212_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_211_, v_searcher_208_, v___x_209_, lean_box(0));
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v___x_213_; 
v___x_213_ = lean_nat_sub(v_stopPos_204_, v_startPos_203_);
lean_dec(v_startPos_203_);
lean_dec(v_stopPos_204_);
return v___x_213_;
}
else
{
lean_object* v_val_214_; 
lean_dec(v_stopPos_204_);
lean_dec(v_startPos_203_);
v_val_214_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_val_214_);
lean_dec_ref_known(v___x_212_, 1);
return v_val_214_;
}
}
}
}
}
LEAN_EXPORT void l_Substring_Raw_posOf_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_200_ = stack[0].m_obj;
uint32_t v_c_201_ = stack[1].m_num;
lean_object* v_res_218_;
v_res_218_ = l_Substring_Raw_posOf(v_s_200_, v_c_201_);
stack->m_obj
 = v_res_218_;
}
LEAN_EXPORT lean_object* l_Substring_Raw_posOf___boxed(lean_object* v_s_219_, lean_object* v_c_220_){
_start:
{
uint32_t v_c_boxed_221_; lean_object* v_res_222_; 
v_c_boxed_221_ = lean_unbox_uint32(v_c_220_);
lean_dec(v_c_220_);
v_res_222_ = l_Substring_Raw_posOf(v_s_219_, v_c_boxed_221_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_drop(lean_object* v_x_223_, lean_object* v_x_224_){
_start:
{
lean_object* v_str_225_; lean_object* v_startPos_226_; lean_object* v_stopPos_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_237_; 
v_str_225_ = lean_ctor_get(v_x_223_, 0);
lean_inc_ref(v_str_225_);
v_startPos_226_ = lean_ctor_get(v_x_223_, 1);
lean_inc(v_startPos_226_);
v_stopPos_227_ = lean_ctor_get(v_x_223_, 2);
lean_inc(v_stopPos_227_);
v___x_228_ = lean_unsigned_to_nat(0u);
v___x_229_ = l_Substring_Raw_nextn(v_x_223_, v_x_224_, v___x_228_);
v_isSharedCheck_237_ = !lean_is_exclusive(v_x_223_);
if (v_isSharedCheck_237_ == 0)
{
lean_object* v_unused_238_; lean_object* v_unused_239_; lean_object* v_unused_240_; 
v_unused_238_ = lean_ctor_get(v_x_223_, 2);
lean_dec(v_unused_238_);
v_unused_239_ = lean_ctor_get(v_x_223_, 1);
lean_dec(v_unused_239_);
v_unused_240_ = lean_ctor_get(v_x_223_, 0);
lean_dec(v_unused_240_);
v___x_231_ = v_x_223_;
v_isShared_232_ = v_isSharedCheck_237_;
goto v_resetjp_230_;
}
else
{
lean_dec(v_x_223_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_237_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; lean_object* v___x_235_; 
v___x_233_ = lean_nat_add(v_startPos_226_, v___x_229_);
lean_dec(v___x_229_);
lean_dec(v_startPos_226_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 1, v___x_233_);
v___x_235_ = v___x_231_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_str_225_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_236_, 2, v_stopPos_227_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
LEAN_EXPORT lean_object* lean_substring_drop(lean_object* v_a_241_, lean_object* v_a_242_){
_start:
{
lean_object* v_str_243_; lean_object* v_startPos_244_; lean_object* v_stopPos_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_255_; 
v_str_243_ = lean_ctor_get(v_a_241_, 0);
lean_inc_ref(v_str_243_);
v_startPos_244_ = lean_ctor_get(v_a_241_, 1);
lean_inc(v_startPos_244_);
v_stopPos_245_ = lean_ctor_get(v_a_241_, 2);
lean_inc(v_stopPos_245_);
v___x_246_ = lean_unsigned_to_nat(0u);
v___x_247_ = l_Substring_Raw_nextn(v_a_241_, v_a_242_, v___x_246_);
v_isSharedCheck_255_ = !lean_is_exclusive(v_a_241_);
if (v_isSharedCheck_255_ == 0)
{
lean_object* v_unused_256_; lean_object* v_unused_257_; lean_object* v_unused_258_; 
v_unused_256_ = lean_ctor_get(v_a_241_, 2);
lean_dec(v_unused_256_);
v_unused_257_ = lean_ctor_get(v_a_241_, 1);
lean_dec(v_unused_257_);
v_unused_258_ = lean_ctor_get(v_a_241_, 0);
lean_dec(v_unused_258_);
v___x_249_ = v_a_241_;
v_isShared_250_ = v_isSharedCheck_255_;
goto v_resetjp_248_;
}
else
{
lean_dec(v_a_241_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_255_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_251_; lean_object* v___x_253_; 
v___x_251_ = lean_nat_add(v_startPos_244_, v___x_247_);
lean_dec(v___x_247_);
lean_dec(v_startPos_244_);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 1, v___x_251_);
v___x_253_ = v___x_249_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_str_243_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v___x_251_);
lean_ctor_set(v_reuseFailAlloc_254_, 2, v_stopPos_245_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropRight(lean_object* v_x_259_, lean_object* v_x_260_){
_start:
{
lean_object* v_str_261_; lean_object* v_startPos_262_; lean_object* v_stopPos_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_273_; 
v_str_261_ = lean_ctor_get(v_x_259_, 0);
lean_inc_ref(v_str_261_);
v_startPos_262_ = lean_ctor_get(v_x_259_, 1);
lean_inc(v_startPos_262_);
v_stopPos_263_ = lean_ctor_get(v_x_259_, 2);
v___x_264_ = lean_nat_sub(v_stopPos_263_, v_startPos_262_);
v___x_265_ = l_Substring_Raw_prevn(v_x_259_, v_x_260_, v___x_264_);
v_isSharedCheck_273_ = !lean_is_exclusive(v_x_259_);
if (v_isSharedCheck_273_ == 0)
{
lean_object* v_unused_274_; lean_object* v_unused_275_; lean_object* v_unused_276_; 
v_unused_274_ = lean_ctor_get(v_x_259_, 2);
lean_dec(v_unused_274_);
v_unused_275_ = lean_ctor_get(v_x_259_, 1);
lean_dec(v_unused_275_);
v_unused_276_ = lean_ctor_get(v_x_259_, 0);
lean_dec(v_unused_276_);
v___x_267_ = v_x_259_;
v_isShared_268_ = v_isSharedCheck_273_;
goto v_resetjp_266_;
}
else
{
lean_dec(v_x_259_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_273_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_269_ = lean_nat_add(v_startPos_262_, v___x_265_);
lean_dec(v___x_265_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 2, v___x_269_);
v___x_271_ = v___x_267_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_str_261_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_startPos_262_);
lean_ctor_set(v_reuseFailAlloc_272_, 2, v___x_269_);
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
LEAN_EXPORT lean_object* l_Substring_Raw_take(lean_object* v_x_277_, lean_object* v_x_278_){
_start:
{
lean_object* v_str_279_; lean_object* v_startPos_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_290_; 
v_str_279_ = lean_ctor_get(v_x_277_, 0);
lean_inc_ref(v_str_279_);
v_startPos_280_ = lean_ctor_get(v_x_277_, 1);
lean_inc(v_startPos_280_);
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = l_Substring_Raw_nextn(v_x_277_, v_x_278_, v___x_281_);
v_isSharedCheck_290_ = !lean_is_exclusive(v_x_277_);
if (v_isSharedCheck_290_ == 0)
{
lean_object* v_unused_291_; lean_object* v_unused_292_; lean_object* v_unused_293_; 
v_unused_291_ = lean_ctor_get(v_x_277_, 2);
lean_dec(v_unused_291_);
v_unused_292_ = lean_ctor_get(v_x_277_, 1);
lean_dec(v_unused_292_);
v_unused_293_ = lean_ctor_get(v_x_277_, 0);
lean_dec(v_unused_293_);
v___x_284_ = v_x_277_;
v_isShared_285_ = v_isSharedCheck_290_;
goto v_resetjp_283_;
}
else
{
lean_dec(v_x_277_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_290_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_286_; lean_object* v___x_288_; 
v___x_286_ = lean_nat_add(v_startPos_280_, v___x_282_);
lean_dec(v___x_282_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 2, v___x_286_);
v___x_288_ = v___x_284_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_str_279_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v_startPos_280_);
lean_ctor_set(v_reuseFailAlloc_289_, 2, v___x_286_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRight(lean_object* v_x_294_, lean_object* v_x_295_){
_start:
{
lean_object* v_str_296_; lean_object* v_startPos_297_; lean_object* v_stopPos_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_308_; 
v_str_296_ = lean_ctor_get(v_x_294_, 0);
lean_inc_ref(v_str_296_);
v_startPos_297_ = lean_ctor_get(v_x_294_, 1);
lean_inc(v_startPos_297_);
v_stopPos_298_ = lean_ctor_get(v_x_294_, 2);
lean_inc(v_stopPos_298_);
v___x_299_ = lean_nat_sub(v_stopPos_298_, v_startPos_297_);
v___x_300_ = l_Substring_Raw_prevn(v_x_294_, v_x_295_, v___x_299_);
v_isSharedCheck_308_ = !lean_is_exclusive(v_x_294_);
if (v_isSharedCheck_308_ == 0)
{
lean_object* v_unused_309_; lean_object* v_unused_310_; lean_object* v_unused_311_; 
v_unused_309_ = lean_ctor_get(v_x_294_, 2);
lean_dec(v_unused_309_);
v_unused_310_ = lean_ctor_get(v_x_294_, 1);
lean_dec(v_unused_310_);
v_unused_311_ = lean_ctor_get(v_x_294_, 0);
lean_dec(v_unused_311_);
v___x_302_ = v_x_294_;
v_isShared_303_ = v_isSharedCheck_308_;
goto v_resetjp_301_;
}
else
{
lean_dec(v_x_294_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_308_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_304_; lean_object* v___x_306_; 
v___x_304_ = lean_nat_add(v_startPos_297_, v___x_300_);
lean_dec(v___x_300_);
lean_dec(v_startPos_297_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 1, v___x_304_);
v___x_306_ = v___x_302_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_str_296_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v___x_304_);
lean_ctor_set(v_reuseFailAlloc_307_, 2, v_stopPos_298_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
}
uint8_t l_Substring_Raw_atEnd(lean_object* v_x_312_, lean_object* v_x_313_){
_start:
{
lean_object* v_startPos_314_; lean_object* v_stopPos_315_; lean_object* v___x_316_; uint8_t v_decide_317_; 
v_startPos_314_ = lean_ctor_get(v_x_312_, 1);
v_stopPos_315_ = lean_ctor_get(v_x_312_, 2);
v___x_316_ = lean_nat_add(v_startPos_314_, v_x_313_);
v_decide_317_ = lean_nat_dec_eq(v___x_316_, v_stopPos_315_);
lean_dec(v___x_316_);
return v_decide_317_;
}
}
LEAN_EXPORT void l_Substring_Raw_atEnd_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_312_ = stack[0].m_obj;
lean_object* v_x_313_ = stack[1].m_obj;
uint8_t v_res_318_;
v_res_318_ = l_Substring_Raw_atEnd(v_x_312_, v_x_313_);
stack->m_num = v_res_318_;
}
LEAN_EXPORT lean_object* l_Substring_Raw_atEnd___boxed(lean_object* v_x_319_, lean_object* v_x_320_){
_start:
{
uint8_t v_res_321_; lean_object* v_r_322_; 
v_res_321_ = l_Substring_Raw_atEnd(v_x_319_, v_x_320_);
lean_dec(v_x_320_);
lean_dec_ref(v_x_319_);
v_r_322_ = lean_box(v_res_321_);
return v_r_322_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_extract(lean_object* v_x_327_, lean_object* v_x_328_, lean_object* v_x_329_){
_start:
{
lean_object* v_str_330_; lean_object* v_startPos_331_; lean_object* v_stopPos_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_350_; 
v_str_330_ = lean_ctor_get(v_x_327_, 0);
v_startPos_331_ = lean_ctor_get(v_x_327_, 1);
v_stopPos_332_ = lean_ctor_get(v_x_327_, 2);
v_isSharedCheck_350_ = !lean_is_exclusive(v_x_327_);
if (v_isSharedCheck_350_ == 0)
{
v___x_334_ = v_x_327_;
v_isShared_335_ = v_isSharedCheck_350_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_stopPos_332_);
lean_inc(v_startPos_331_);
lean_inc(v_str_330_);
lean_dec(v_x_327_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_350_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___y_337_; uint8_t v___x_346_; 
v___x_346_ = lean_nat_dec_le(v_x_329_, v_x_328_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_347_ = lean_nat_add(v_startPos_331_, v_x_328_);
v___x_348_ = lean_nat_dec_le(v_stopPos_332_, v___x_347_);
if (v___x_348_ == 0)
{
v___y_337_ = v___x_347_;
goto v___jp_336_;
}
else
{
lean_dec(v___x_347_);
lean_inc(v_stopPos_332_);
v___y_337_ = v_stopPos_332_;
goto v___jp_336_;
}
}
else
{
lean_object* v___x_349_; 
lean_del_object(v___x_334_);
lean_dec(v_stopPos_332_);
lean_dec(v_startPos_331_);
lean_dec_ref(v_str_330_);
v___x_349_ = ((lean_object*)(l_Substring_Raw_extract___closed__1));
return v___x_349_;
}
v___jp_336_:
{
lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_338_ = lean_nat_add(v_startPos_331_, v_x_329_);
lean_dec(v_startPos_331_);
v___x_339_ = lean_nat_dec_le(v_stopPos_332_, v___x_338_);
if (v___x_339_ == 0)
{
lean_object* v___x_341_; 
lean_dec(v_stopPos_332_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 2, v___x_338_);
lean_ctor_set(v___x_334_, 1, v___y_337_);
v___x_341_ = v___x_334_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_str_330_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v___y_337_);
lean_ctor_set(v_reuseFailAlloc_342_, 2, v___x_338_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
else
{
lean_object* v___x_344_; 
lean_dec(v___x_338_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 1, v___y_337_);
v___x_344_ = v___x_334_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_str_330_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v___y_337_);
lean_ctor_set(v_reuseFailAlloc_345_, 2, v_stopPos_332_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_extract___boxed(lean_object* v_x_351_, lean_object* v_x_352_, lean_object* v_x_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Substring_Raw_extract(v_x_351_, v_x_352_, v_x_353_);
lean_dec(v_x_353_);
lean_dec(v_x_352_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* lean_substring_extract(lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_){
_start:
{
lean_object* v_str_358_; lean_object* v_startPos_359_; lean_object* v_stopPos_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_378_; 
v_str_358_ = lean_ctor_get(v_a_355_, 0);
v_startPos_359_ = lean_ctor_get(v_a_355_, 1);
v_stopPos_360_ = lean_ctor_get(v_a_355_, 2);
v_isSharedCheck_378_ = !lean_is_exclusive(v_a_355_);
if (v_isSharedCheck_378_ == 0)
{
v___x_362_ = v_a_355_;
v_isShared_363_ = v_isSharedCheck_378_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_stopPos_360_);
lean_inc(v_startPos_359_);
lean_inc(v_str_358_);
lean_dec(v_a_355_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_378_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___y_365_; uint8_t v___x_374_; 
v___x_374_ = lean_nat_dec_le(v_a_357_, v_a_356_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_375_ = lean_nat_add(v_startPos_359_, v_a_356_);
lean_dec(v_a_356_);
v___x_376_ = lean_nat_dec_le(v_stopPos_360_, v___x_375_);
if (v___x_376_ == 0)
{
v___y_365_ = v___x_375_;
goto v___jp_364_;
}
else
{
lean_dec(v___x_375_);
lean_inc(v_stopPos_360_);
v___y_365_ = v_stopPos_360_;
goto v___jp_364_;
}
}
else
{
lean_object* v___x_377_; 
lean_del_object(v___x_362_);
lean_dec(v_stopPos_360_);
lean_dec(v_startPos_359_);
lean_dec_ref(v_str_358_);
lean_dec(v_a_357_);
lean_dec(v_a_356_);
v___x_377_ = ((lean_object*)(l_Substring_Raw_extract___closed__1));
return v___x_377_;
}
v___jp_364_:
{
lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_366_ = lean_nat_add(v_startPos_359_, v_a_357_);
lean_dec(v_a_357_);
lean_dec(v_startPos_359_);
v___x_367_ = lean_nat_dec_le(v_stopPos_360_, v___x_366_);
if (v___x_367_ == 0)
{
lean_object* v___x_369_; 
lean_dec(v_stopPos_360_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 2, v___x_366_);
lean_ctor_set(v___x_362_, 1, v___y_365_);
v___x_369_ = v___x_362_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_str_358_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v___y_365_);
lean_ctor_set(v_reuseFailAlloc_370_, 2, v___x_366_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
else
{
lean_object* v___x_372_; 
lean_dec(v___x_366_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 1, v___y_365_);
v___x_372_ = v___x_362_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_str_358_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v___y_365_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v_stopPos_360_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop(lean_object* v_s_379_, lean_object* v_sep_380_, lean_object* v_b_381_, lean_object* v_i_382_, lean_object* v_j_383_, lean_object* v_r_384_){
_start:
{
lean_object* v___y_386_; lean_object* v___y_390_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v_str_399_; lean_object* v_startPos_400_; lean_object* v_stopPos_401_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v___y_412_; lean_object* v___y_423_; lean_object* v___x_428_; uint8_t v___x_429_; 
v_str_399_ = lean_ctor_get(v_s_379_, 0);
v_startPos_400_ = lean_ctor_get(v_s_379_, 1);
v_stopPos_401_ = lean_ctor_get(v_s_379_, 2);
v___x_428_ = lean_nat_sub(v_stopPos_401_, v_startPos_400_);
v___x_429_ = lean_nat_dec_lt(v_i_382_, v___x_428_);
lean_dec(v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_458_; 
lean_inc(v_stopPos_401_);
lean_inc(v_startPos_400_);
lean_inc_ref(v_str_399_);
v_isSharedCheck_458_ = !lean_is_exclusive(v_s_379_);
if (v_isSharedCheck_458_ == 0)
{
lean_object* v_unused_459_; lean_object* v_unused_460_; lean_object* v_unused_461_; 
v_unused_459_ = lean_ctor_get(v_s_379_, 2);
lean_dec(v_unused_459_);
v_unused_460_ = lean_ctor_get(v_s_379_, 1);
lean_dec(v_unused_460_);
v_unused_461_ = lean_ctor_get(v_s_379_, 0);
lean_dec(v_unused_461_);
v___x_431_ = v_s_379_;
v_isShared_432_ = v_isSharedCheck_458_;
goto v_resetjp_430_;
}
else
{
lean_dec(v_s_379_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_458_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
uint8_t v___x_433_; 
v___x_433_ = lean_string_utf8_at_end(v_sep_380_, v_j_383_);
if (v___x_433_ == 0)
{
uint8_t v___x_434_; 
lean_del_object(v___x_431_);
lean_dec(v_j_383_);
v___x_434_ = lean_nat_dec_le(v_i_382_, v_b_381_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; uint8_t v___x_436_; 
v___x_435_ = lean_nat_add(v_startPos_400_, v_b_381_);
lean_dec(v_b_381_);
v___x_436_ = lean_nat_dec_le(v_stopPos_401_, v___x_435_);
if (v___x_436_ == 0)
{
v___y_423_ = v___x_435_;
goto v___jp_422_;
}
else
{
lean_dec(v___x_435_);
lean_inc(v_stopPos_401_);
v___y_423_ = v_stopPos_401_;
goto v___jp_422_;
}
}
else
{
lean_object* v___x_437_; 
lean_dec(v_stopPos_401_);
lean_dec(v_startPos_400_);
lean_dec_ref(v_str_399_);
lean_dec(v_i_382_);
lean_dec(v_b_381_);
v___x_437_ = ((lean_object*)(l_Substring_Raw_extract___closed__1));
v___y_386_ = v___x_437_;
goto v___jp_385_;
}
}
else
{
lean_object* v___x_438_; lean_object* v___y_440_; lean_object* v___x_444_; lean_object* v___y_446_; uint8_t v___x_455_; 
v___x_438_ = ((lean_object*)(l_Substring_Raw_extract___closed__1));
v___x_444_ = lean_nat_sub(v_i_382_, v_j_383_);
lean_dec(v_j_383_);
lean_dec(v_i_382_);
v___x_455_ = lean_nat_dec_le(v___x_444_, v_b_381_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_456_ = lean_nat_add(v_startPos_400_, v_b_381_);
lean_dec(v_b_381_);
v___x_457_ = lean_nat_dec_le(v_stopPos_401_, v___x_456_);
if (v___x_457_ == 0)
{
v___y_446_ = v___x_456_;
goto v___jp_445_;
}
else
{
lean_dec(v___x_456_);
lean_inc(v_stopPos_401_);
v___y_446_ = v_stopPos_401_;
goto v___jp_445_;
}
}
else
{
lean_dec(v___x_444_);
lean_del_object(v___x_431_);
lean_dec(v_stopPos_401_);
lean_dec(v_startPos_400_);
lean_dec_ref(v_str_399_);
lean_dec(v_b_381_);
v___y_440_ = v___x_438_;
goto v___jp_439_;
}
v___jp_439_:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_441_, 0, v___y_440_);
lean_ctor_set(v___x_441_, 1, v_r_384_);
v___x_442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_438_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
v___x_443_ = l_List_reverse___redArg(v___x_442_);
return v___x_443_;
}
v___jp_445_:
{
lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_447_ = lean_nat_add(v_startPos_400_, v___x_444_);
lean_dec(v___x_444_);
lean_dec(v_startPos_400_);
v___x_448_ = lean_nat_dec_le(v_stopPos_401_, v___x_447_);
if (v___x_448_ == 0)
{
lean_object* v___x_450_; 
lean_dec(v_stopPos_401_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 2, v___x_447_);
lean_ctor_set(v___x_431_, 1, v___y_446_);
v___x_450_ = v___x_431_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_str_399_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v___y_446_);
lean_ctor_set(v_reuseFailAlloc_451_, 2, v___x_447_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
v___y_440_ = v___x_450_;
goto v___jp_439_;
}
}
else
{
lean_object* v___x_453_; 
lean_dec(v___x_447_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 1, v___y_446_);
v___x_453_ = v___x_431_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_str_399_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v___y_446_);
lean_ctor_set(v_reuseFailAlloc_454_, 2, v_stopPos_401_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
v___y_440_ = v___x_453_;
goto v___jp_439_;
}
}
}
}
}
}
else
{
lean_object* v___x_462_; uint32_t v___x_463_; uint32_t v___x_464_; uint8_t v___x_465_; 
v___x_462_ = lean_nat_add(v_startPos_400_, v_i_382_);
v___x_463_ = lean_string_utf8_get(v_str_399_, v___x_462_);
v___x_464_ = lean_string_utf8_get(v_sep_380_, v_j_383_);
v___x_465_ = lean_uint32_dec_eq(v___x_463_, v___x_464_);
if (v___x_465_ == 0)
{
uint8_t v_decide_466_; 
lean_dec(v_j_383_);
v_decide_466_ = lean_nat_dec_eq(v___x_462_, v_stopPos_401_);
if (v_decide_466_ == 0)
{
lean_object* v___x_467_; lean_object* v___x_468_; 
lean_dec(v_i_382_);
v___x_467_ = lean_string_utf8_next(v_str_399_, v___x_462_);
lean_dec(v___x_462_);
v___x_468_ = lean_nat_sub(v___x_467_, v_startPos_400_);
lean_dec(v___x_467_);
v___y_390_ = v___x_468_;
goto v___jp_389_;
}
else
{
lean_dec(v___x_462_);
v___y_390_ = v_i_382_;
goto v___jp_389_;
}
}
else
{
uint8_t v_decide_469_; 
v_decide_469_ = lean_nat_dec_eq(v___x_462_, v_stopPos_401_);
if (v_decide_469_ == 0)
{
lean_object* v___x_470_; lean_object* v___x_471_; 
lean_dec(v_i_382_);
v___x_470_ = lean_string_utf8_next(v_str_399_, v___x_462_);
lean_dec(v___x_462_);
v___x_471_ = lean_nat_sub(v___x_470_, v_startPos_400_);
lean_dec(v___x_470_);
v___y_412_ = v___x_471_;
goto v___jp_411_;
}
else
{
lean_dec(v___x_462_);
v___y_412_ = v_i_382_;
goto v___jp_411_;
}
}
}
v___jp_385_:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_387_, 0, v___y_386_);
lean_ctor_set(v___x_387_, 1, v_r_384_);
v___x_388_ = l_List_reverse___redArg(v___x_387_);
return v___x_388_;
}
v___jp_389_:
{
lean_object* v___x_391_; 
v___x_391_ = lean_unsigned_to_nat(0u);
v_i_382_ = v___y_390_;
v_j_383_ = v___x_391_;
goto _start;
}
v___jp_393_:
{
lean_object* v___x_397_; 
v___x_397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_397_, 0, v___y_396_);
lean_ctor_set(v___x_397_, 1, v_r_384_);
lean_inc(v___y_395_);
v_b_381_ = v___y_395_;
v_i_382_ = v___y_395_;
v_j_383_ = v___y_394_;
v_r_384_ = v___x_397_;
goto _start;
}
v___jp_402_:
{
lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_407_ = lean_nat_add(v_startPos_400_, v___y_403_);
lean_dec(v___y_403_);
v___x_408_ = lean_nat_dec_le(v_stopPos_401_, v___x_407_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; 
lean_inc_ref(v_str_399_);
v___x_409_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_409_, 0, v_str_399_);
lean_ctor_set(v___x_409_, 1, v___y_406_);
lean_ctor_set(v___x_409_, 2, v___x_407_);
v___y_394_ = v___y_404_;
v___y_395_ = v___y_405_;
v___y_396_ = v___x_409_;
goto v___jp_393_;
}
else
{
lean_object* v___x_410_; 
lean_dec(v___x_407_);
lean_inc(v_stopPos_401_);
lean_inc_ref(v_str_399_);
v___x_410_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_410_, 0, v_str_399_);
lean_ctor_set(v___x_410_, 1, v___y_406_);
lean_ctor_set(v___x_410_, 2, v_stopPos_401_);
v___y_394_ = v___y_404_;
v___y_395_ = v___y_405_;
v___y_396_ = v___x_410_;
goto v___jp_393_;
}
}
v___jp_411_:
{
lean_object* v_j_413_; uint8_t v___x_414_; 
v_j_413_ = lean_string_utf8_next(v_sep_380_, v_j_383_);
lean_dec(v_j_383_);
v___x_414_ = lean_string_utf8_at_end(v_sep_380_, v_j_413_);
if (v___x_414_ == 0)
{
v_i_382_ = v___y_412_;
v_j_383_ = v_j_413_;
goto _start;
}
else
{
lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_416_ = lean_unsigned_to_nat(0u);
v___x_417_ = lean_nat_sub(v___y_412_, v_j_413_);
lean_dec(v_j_413_);
v___x_418_ = lean_nat_dec_le(v___x_417_, v_b_381_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; uint8_t v___x_420_; 
v___x_419_ = lean_nat_add(v_startPos_400_, v_b_381_);
lean_dec(v_b_381_);
v___x_420_ = lean_nat_dec_le(v_stopPos_401_, v___x_419_);
if (v___x_420_ == 0)
{
v___y_403_ = v___x_417_;
v___y_404_ = v___x_416_;
v___y_405_ = v___y_412_;
v___y_406_ = v___x_419_;
goto v___jp_402_;
}
else
{
lean_dec(v___x_419_);
lean_inc(v_stopPos_401_);
v___y_403_ = v___x_417_;
v___y_404_ = v___x_416_;
v___y_405_ = v___y_412_;
v___y_406_ = v_stopPos_401_;
goto v___jp_402_;
}
}
else
{
lean_object* v___x_421_; 
lean_dec(v___x_417_);
lean_dec(v_b_381_);
v___x_421_ = ((lean_object*)(l_Substring_Raw_extract___closed__1));
v___y_394_ = v___x_416_;
v___y_395_ = v___y_412_;
v___y_396_ = v___x_421_;
goto v___jp_393_;
}
}
}
v___jp_422_:
{
lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_424_ = lean_nat_add(v_startPos_400_, v_i_382_);
lean_dec(v_i_382_);
lean_dec(v_startPos_400_);
v___x_425_ = lean_nat_dec_le(v_stopPos_401_, v___x_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; 
lean_dec(v_stopPos_401_);
v___x_426_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_426_, 0, v_str_399_);
lean_ctor_set(v___x_426_, 1, v___y_423_);
lean_ctor_set(v___x_426_, 2, v___x_424_);
v___y_386_ = v___x_426_;
goto v___jp_385_;
}
else
{
lean_object* v___x_427_; 
lean_dec(v___x_424_);
v___x_427_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_427_, 0, v_str_399_);
lean_ctor_set(v___x_427_, 1, v___y_423_);
lean_ctor_set(v___x_427_, 2, v_stopPos_401_);
v___y_386_ = v___x_427_;
goto v___jp_385_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___boxed(lean_object* v_s_472_, lean_object* v_sep_473_, lean_object* v_b_474_, lean_object* v_i_475_, lean_object* v_j_476_, lean_object* v_r_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop(v_s_472_, v_sep_473_, v_b_474_, v_i_475_, v_j_476_, v_r_477_);
lean_dec_ref(v_sep_473_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_splitOn(lean_object* v_s_479_, lean_object* v_sep_480_){
_start:
{
lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_481_ = ((lean_object*)(l_Substring_Raw_extract___closed__0));
v___x_482_ = lean_string_dec_eq(v_sep_480_, v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_483_ = lean_unsigned_to_nat(0u);
v___x_484_ = lean_box(0);
v___x_485_ = l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop(v_s_479_, v_sep_480_, v___x_483_, v___x_483_, v___x_483_, v___x_484_);
return v___x_485_;
}
else
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_box(0);
v___x_487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_487_, 0, v_s_479_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
return v___x_487_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_splitOn___boxed(lean_object* v_s_488_, lean_object* v_sep_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Substring_Raw_splitOn(v_s_488_, v_sep_489_);
lean_dec_ref(v_sep_489_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldl___redArg___lam__0(lean_object* v___y_491_, lean_object* v_f_492_, lean_object* v_it_493_, lean_object* v_acc_494_, lean_object* v_hP_495_, lean_object* v_recur_496_){
_start:
{
lean_object* v_str_497_; lean_object* v_startInclusive_498_; lean_object* v_endExclusive_499_; lean_object* v___x_500_; uint8_t v_decide_501_; 
v_str_497_ = lean_ctor_get(v___y_491_, 0);
v_startInclusive_498_ = lean_ctor_get(v___y_491_, 1);
v_endExclusive_499_ = lean_ctor_get(v___y_491_, 2);
v___x_500_ = lean_nat_sub(v_endExclusive_499_, v_startInclusive_498_);
v_decide_501_ = lean_nat_dec_eq(v_it_493_, v___x_500_);
lean_dec(v___x_500_);
if (v_decide_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; uint32_t v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_502_ = lean_nat_add(v_startInclusive_498_, v_it_493_);
v___x_503_ = lean_string_utf8_next_fast(v_str_497_, v___x_502_);
v___x_504_ = lean_nat_sub(v___x_503_, v_startInclusive_498_);
v___x_505_ = lean_string_utf8_get_fast(v_str_497_, v___x_502_);
lean_dec(v___x_502_);
v___x_506_ = lean_box_uint32(v___x_505_);
v___x_507_ = lean_apply_2(v_f_492_, v_acc_494_, v___x_506_);
v___x_508_ = lean_apply_4(v_recur_496_, v___x_504_, v___x_507_, lean_box(0), lean_box(0));
return v___x_508_;
}
else
{
lean_dec(v_recur_496_);
lean_dec(v_f_492_);
return v_acc_494_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldl___redArg___lam__0___boxed(lean_object* v___y_509_, lean_object* v_f_510_, lean_object* v_it_511_, lean_object* v_acc_512_, lean_object* v_hP_513_, lean_object* v_recur_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Substring_Raw_foldl___redArg___lam__0(v___y_509_, v_f_510_, v_it_511_, v_acc_512_, v_hP_513_, v_recur_514_);
lean_dec(v_it_511_);
lean_dec_ref(v___y_509_);
return v_res_515_;
}
}
static lean_object* _init_l_Substring_Raw_foldl___redArg___closed__3(void){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_519_ = ((lean_object*)(l_Substring_Raw_foldl___redArg___closed__2));
v___x_520_ = lean_unsigned_to_nat(14u);
v___x_521_ = lean_unsigned_to_nat(22u);
v___x_522_ = ((lean_object*)(l_Substring_Raw_foldl___redArg___closed__1));
v___x_523_ = ((lean_object*)(l_Substring_Raw_foldl___redArg___closed__0));
v___x_524_ = l_mkPanicMessageWithDecl(v___x_523_, v___x_522_, v___x_521_, v___x_520_, v___x_519_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldl___redArg(lean_object* v_f_525_, lean_object* v_init_526_, lean_object* v_s_527_){
_start:
{
lean_object* v___y_529_; lean_object* v_str_533_; lean_object* v_startPos_534_; lean_object* v_stopPos_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_550_; 
v_str_533_ = lean_ctor_get(v_s_527_, 0);
v_startPos_534_ = lean_ctor_get(v_s_527_, 1);
v_stopPos_535_ = lean_ctor_get(v_s_527_, 2);
v_isSharedCheck_550_ = !lean_is_exclusive(v_s_527_);
if (v_isSharedCheck_550_ == 0)
{
v___x_537_ = v_s_527_;
v_isShared_538_ = v_isSharedCheck_550_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_stopPos_535_);
lean_inc(v_startPos_534_);
lean_inc(v_str_533_);
lean_dec(v_s_527_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_550_;
goto v_resetjp_536_;
}
v___jp_528_:
{
lean_object* v___f_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___f_530_ = lean_alloc_closure((void*)(l_Substring_Raw_foldl___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_530_, 0, v___y_529_);
lean_closure_set(v___f_530_, 1, v_f_525_);
v___x_531_ = lean_unsigned_to_nat(0u);
v___x_532_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_530_, v___x_531_, v_init_526_, lean_box(0));
return v___x_532_;
}
v_resetjp_536_:
{
lean_object* v___x_539_; uint8_t v___y_541_; uint8_t v___x_547_; 
v___x_539_ = l_String_instInhabitedSlice;
v___x_547_ = lean_string_is_valid_pos(v_str_533_, v_startPos_534_);
if (v___x_547_ == 0)
{
v___y_541_ = v___x_547_;
goto v___jp_540_;
}
else
{
uint8_t v___x_548_; 
v___x_548_ = lean_string_is_valid_pos(v_str_533_, v_stopPos_535_);
if (v___x_548_ == 0)
{
v___y_541_ = v___x_548_;
goto v___jp_540_;
}
else
{
uint8_t v___x_549_; 
v___x_549_ = lean_nat_dec_le(v_startPos_534_, v_stopPos_535_);
v___y_541_ = v___x_549_;
goto v___jp_540_;
}
}
v___jp_540_:
{
if (v___y_541_ == 0)
{
lean_object* v___x_542_; lean_object* v___x_543_; 
lean_del_object(v___x_537_);
lean_dec(v_stopPos_535_);
lean_dec(v_startPos_534_);
lean_dec_ref(v_str_533_);
v___x_542_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_543_ = l_panic___redArg(v___x_539_, v___x_542_);
v___y_529_ = v___x_543_;
goto v___jp_528_;
}
else
{
lean_object* v___x_545_; 
if (v_isShared_538_ == 0)
{
v___x_545_ = v___x_537_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_str_533_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_startPos_534_);
lean_ctor_set(v_reuseFailAlloc_546_, 2, v_stopPos_535_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
v___y_529_ = v___x_545_;
goto v___jp_528_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldl(lean_object* v_00_u03b1_551_, lean_object* v_f_552_, lean_object* v_init_553_, lean_object* v_s_554_){
_start:
{
lean_object* v___y_556_; lean_object* v_str_560_; lean_object* v_startPos_561_; lean_object* v_stopPos_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_577_; 
v_str_560_ = lean_ctor_get(v_s_554_, 0);
v_startPos_561_ = lean_ctor_get(v_s_554_, 1);
v_stopPos_562_ = lean_ctor_get(v_s_554_, 2);
v_isSharedCheck_577_ = !lean_is_exclusive(v_s_554_);
if (v_isSharedCheck_577_ == 0)
{
v___x_564_ = v_s_554_;
v_isShared_565_ = v_isSharedCheck_577_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_stopPos_562_);
lean_inc(v_startPos_561_);
lean_inc(v_str_560_);
lean_dec(v_s_554_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_577_;
goto v_resetjp_563_;
}
v___jp_555_:
{
lean_object* v___f_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___f_557_ = lean_alloc_closure((void*)(l_Substring_Raw_foldl___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_557_, 0, v___y_556_);
lean_closure_set(v___f_557_, 1, v_f_552_);
v___x_558_ = lean_unsigned_to_nat(0u);
v___x_559_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_557_, v___x_558_, v_init_553_, lean_box(0));
return v___x_559_;
}
v_resetjp_563_:
{
lean_object* v___x_566_; uint8_t v___y_568_; uint8_t v___x_574_; 
v___x_566_ = l_String_instInhabitedSlice;
v___x_574_ = lean_string_is_valid_pos(v_str_560_, v_startPos_561_);
if (v___x_574_ == 0)
{
v___y_568_ = v___x_574_;
goto v___jp_567_;
}
else
{
uint8_t v___x_575_; 
v___x_575_ = lean_string_is_valid_pos(v_str_560_, v_stopPos_562_);
if (v___x_575_ == 0)
{
v___y_568_ = v___x_575_;
goto v___jp_567_;
}
else
{
uint8_t v___x_576_; 
v___x_576_ = lean_nat_dec_le(v_startPos_561_, v_stopPos_562_);
v___y_568_ = v___x_576_;
goto v___jp_567_;
}
}
v___jp_567_:
{
if (v___y_568_ == 0)
{
lean_object* v___x_569_; lean_object* v___x_570_; 
lean_del_object(v___x_564_);
lean_dec(v_stopPos_562_);
lean_dec(v_startPos_561_);
lean_dec_ref(v_str_560_);
v___x_569_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_570_ = l_panic___redArg(v___x_566_, v___x_569_);
v___y_556_ = v___x_570_;
goto v___jp_555_;
}
else
{
lean_object* v___x_572_; 
if (v_isShared_565_ == 0)
{
v___x_572_ = v___x_564_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_str_560_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_startPos_561_);
lean_ctor_set(v_reuseFailAlloc_573_, 2, v_stopPos_562_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
v___y_556_ = v___x_572_;
goto v___jp_555_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr___redArg___lam__0(lean_object* v___y_578_, lean_object* v_f_579_, lean_object* v_it_580_, lean_object* v_acc_581_, lean_object* v_hP_582_, lean_object* v_recur_583_){
_start:
{
lean_object* v___x_584_; uint8_t v_decide_585_; 
v___x_584_ = lean_unsigned_to_nat(0u);
v_decide_585_ = lean_nat_dec_eq(v_it_580_, v___x_584_);
if (v_decide_585_ == 0)
{
lean_object* v_str_586_; lean_object* v_startInclusive_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v_prevPos_590_; lean_object* v___x_591_; uint32_t v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v_str_586_ = lean_ctor_get(v___y_578_, 0);
v_startInclusive_587_ = lean_ctor_get(v___y_578_, 1);
v___x_588_ = lean_unsigned_to_nat(1u);
v___x_589_ = lean_nat_sub(v_it_580_, v___x_588_);
v_prevPos_590_ = l_String_Slice_posLE(v___y_578_, v___x_589_);
v___x_591_ = lean_nat_add(v_startInclusive_587_, v_prevPos_590_);
v___x_592_ = lean_string_utf8_get_fast(v_str_586_, v___x_591_);
lean_dec(v___x_591_);
v___x_593_ = lean_box_uint32(v___x_592_);
v___x_594_ = lean_apply_2(v_f_579_, v___x_593_, v_acc_581_);
v___x_595_ = lean_apply_4(v_recur_583_, v_prevPos_590_, v___x_594_, lean_box(0), lean_box(0));
return v___x_595_;
}
else
{
lean_dec(v_recur_583_);
lean_dec(v_f_579_);
return v_acc_581_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr___redArg___lam__0___boxed(lean_object* v___y_596_, lean_object* v_f_597_, lean_object* v_it_598_, lean_object* v_acc_599_, lean_object* v_hP_600_, lean_object* v_recur_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Substring_Raw_foldr___redArg___lam__0(v___y_596_, v_f_597_, v_it_598_, v_acc_599_, v_hP_600_, v_recur_601_);
lean_dec(v_it_598_);
lean_dec_ref(v___y_596_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr___redArg(lean_object* v_f_603_, lean_object* v_init_604_, lean_object* v_s_605_){
_start:
{
lean_object* v___y_607_; lean_object* v_str_611_; lean_object* v_startPos_612_; lean_object* v_stopPos_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_628_; 
v_str_611_ = lean_ctor_get(v_s_605_, 0);
v_startPos_612_ = lean_ctor_get(v_s_605_, 1);
v_stopPos_613_ = lean_ctor_get(v_s_605_, 2);
v_isSharedCheck_628_ = !lean_is_exclusive(v_s_605_);
if (v_isSharedCheck_628_ == 0)
{
v___x_615_ = v_s_605_;
v_isShared_616_ = v_isSharedCheck_628_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_stopPos_613_);
lean_inc(v_startPos_612_);
lean_inc(v_str_611_);
lean_dec(v_s_605_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_628_;
goto v_resetjp_614_;
}
v___jp_606_:
{
lean_object* v___f_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
lean_inc_ref(v___y_607_);
v___f_608_ = lean_alloc_closure((void*)(l_Substring_Raw_foldr___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_608_, 0, v___y_607_);
lean_closure_set(v___f_608_, 1, v_f_603_);
v___x_609_ = l_String_Slice_revPositions(v___y_607_);
lean_dec_ref(v___y_607_);
v___x_610_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_608_, v___x_609_, v_init_604_, lean_box(0));
return v___x_610_;
}
v_resetjp_614_:
{
lean_object* v___x_617_; uint8_t v___y_619_; uint8_t v___x_625_; 
v___x_617_ = l_String_instInhabitedSlice;
v___x_625_ = lean_string_is_valid_pos(v_str_611_, v_startPos_612_);
if (v___x_625_ == 0)
{
v___y_619_ = v___x_625_;
goto v___jp_618_;
}
else
{
uint8_t v___x_626_; 
v___x_626_ = lean_string_is_valid_pos(v_str_611_, v_stopPos_613_);
if (v___x_626_ == 0)
{
v___y_619_ = v___x_626_;
goto v___jp_618_;
}
else
{
uint8_t v___x_627_; 
v___x_627_ = lean_nat_dec_le(v_startPos_612_, v_stopPos_613_);
v___y_619_ = v___x_627_;
goto v___jp_618_;
}
}
v___jp_618_:
{
if (v___y_619_ == 0)
{
lean_object* v___x_620_; lean_object* v___x_621_; 
lean_del_object(v___x_615_);
lean_dec(v_stopPos_613_);
lean_dec(v_startPos_612_);
lean_dec_ref(v_str_611_);
v___x_620_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_621_ = l_panic___redArg(v___x_617_, v___x_620_);
v___y_607_ = v___x_621_;
goto v___jp_606_;
}
else
{
lean_object* v___x_623_; 
if (v_isShared_616_ == 0)
{
v___x_623_ = v___x_615_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_str_611_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_startPos_612_);
lean_ctor_set(v_reuseFailAlloc_624_, 2, v_stopPos_613_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
v___y_607_ = v___x_623_;
goto v___jp_606_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr(lean_object* v_00_u03b1_629_, lean_object* v_f_630_, lean_object* v_init_631_, lean_object* v_s_632_){
_start:
{
lean_object* v___y_634_; lean_object* v_str_638_; lean_object* v_startPos_639_; lean_object* v_stopPos_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_655_; 
v_str_638_ = lean_ctor_get(v_s_632_, 0);
v_startPos_639_ = lean_ctor_get(v_s_632_, 1);
v_stopPos_640_ = lean_ctor_get(v_s_632_, 2);
v_isSharedCheck_655_ = !lean_is_exclusive(v_s_632_);
if (v_isSharedCheck_655_ == 0)
{
v___x_642_ = v_s_632_;
v_isShared_643_ = v_isSharedCheck_655_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_stopPos_640_);
lean_inc(v_startPos_639_);
lean_inc(v_str_638_);
lean_dec(v_s_632_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_655_;
goto v_resetjp_641_;
}
v___jp_633_:
{
lean_object* v___f_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
lean_inc_ref(v___y_634_);
v___f_635_ = lean_alloc_closure((void*)(l_Substring_Raw_foldr___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_635_, 0, v___y_634_);
lean_closure_set(v___f_635_, 1, v_f_630_);
v___x_636_ = l_String_Slice_revPositions(v___y_634_);
lean_dec_ref(v___y_634_);
v___x_637_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_635_, v___x_636_, v_init_631_, lean_box(0));
return v___x_637_;
}
v_resetjp_641_:
{
lean_object* v___x_644_; uint8_t v___y_646_; uint8_t v___x_652_; 
v___x_644_ = l_String_instInhabitedSlice;
v___x_652_ = lean_string_is_valid_pos(v_str_638_, v_startPos_639_);
if (v___x_652_ == 0)
{
v___y_646_ = v___x_652_;
goto v___jp_645_;
}
else
{
uint8_t v___x_653_; 
v___x_653_ = lean_string_is_valid_pos(v_str_638_, v_stopPos_640_);
if (v___x_653_ == 0)
{
v___y_646_ = v___x_653_;
goto v___jp_645_;
}
else
{
uint8_t v___x_654_; 
v___x_654_ = lean_nat_dec_le(v_startPos_639_, v_stopPos_640_);
v___y_646_ = v___x_654_;
goto v___jp_645_;
}
}
v___jp_645_:
{
if (v___y_646_ == 0)
{
lean_object* v___x_647_; lean_object* v___x_648_; 
lean_del_object(v___x_642_);
lean_dec(v_stopPos_640_);
lean_dec(v_startPos_639_);
lean_dec_ref(v_str_638_);
v___x_647_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_648_ = l_panic___redArg(v___x_644_, v___x_647_);
v___y_634_ = v___x_648_;
goto v___jp_633_;
}
else
{
lean_object* v___x_650_; 
if (v_isShared_643_ == 0)
{
v___x_650_ = v___x_642_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_str_638_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_startPos_639_);
lean_ctor_set(v_reuseFailAlloc_651_, 2, v_stopPos_640_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
v___y_634_ = v___x_650_;
goto v___jp_633_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_any___lam__0(lean_object* v___x_656_, lean_object* v_s_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(v_s_657_, v___x_656_, v___y_658_, lean_box(0), lean_box(0), v___y_661_, v___y_662_, v___y_663_);
return v___x_664_;
}
}
uint8_t l_Substring_Raw_any(lean_object* v_s_665_, lean_object* v_p_666_){
_start:
{
lean_object* v___x_667_; lean_object* v_str_668_; lean_object* v_startPos_669_; lean_object* v_stopPos_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_689_; 
lean_inc_ref(v_p_666_);
v___x_667_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v_p_666_);
v_str_668_ = lean_ctor_get(v_s_665_, 0);
v_startPos_669_ = lean_ctor_get(v_s_665_, 1);
v_stopPos_670_ = lean_ctor_get(v_s_665_, 2);
v_isSharedCheck_689_ = !lean_is_exclusive(v_s_665_);
if (v_isSharedCheck_689_ == 0)
{
v___x_672_ = v_s_665_;
v_isShared_673_ = v_isSharedCheck_689_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_stopPos_670_);
lean_inc(v_startPos_669_);
lean_inc(v_str_668_);
lean_dec(v_s_665_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_689_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_674_; lean_object* v___f_675_; lean_object* v___x_676_; uint8_t v___y_678_; uint8_t v___x_686_; 
v___x_674_ = l_String_instInhabitedSlice;
v___f_675_ = lean_alloc_closure((void*)(l_Substring_Raw_any___lam__0), 8, 1);
lean_closure_set(v___f_675_, 0, v___x_667_);
v___x_676_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_676_, 0, lean_box(0));
lean_closure_set(v___x_676_, 1, v_p_666_);
v___x_686_ = lean_string_is_valid_pos(v_str_668_, v_startPos_669_);
if (v___x_686_ == 0)
{
v___y_678_ = v___x_686_;
goto v___jp_677_;
}
else
{
uint8_t v___x_687_; 
v___x_687_ = lean_string_is_valid_pos(v_str_668_, v_stopPos_670_);
if (v___x_687_ == 0)
{
v___y_678_ = v___x_687_;
goto v___jp_677_;
}
else
{
uint8_t v___x_688_; 
v___x_688_ = lean_nat_dec_le(v_startPos_669_, v_stopPos_670_);
v___y_678_ = v___x_688_;
goto v___jp_677_;
}
}
v___jp_677_:
{
if (v___y_678_ == 0)
{
lean_object* v___x_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
lean_del_object(v___x_672_);
lean_dec(v_stopPos_670_);
lean_dec(v_startPos_669_);
lean_dec_ref(v_str_668_);
v___x_679_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_680_ = l_panic___redArg(v___x_674_, v___x_679_);
v___x_681_ = l_String_Slice_contains___redArg(v___f_675_, v___x_680_, v___x_676_);
return v___x_681_;
}
else
{
lean_object* v___x_683_; 
if (v_isShared_673_ == 0)
{
v___x_683_ = v___x_672_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_str_668_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_startPos_669_);
lean_ctor_set(v_reuseFailAlloc_685_, 2, v_stopPos_670_);
v___x_683_ = v_reuseFailAlloc_685_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
uint8_t v___x_684_; 
v___x_684_ = l_String_Slice_contains___redArg(v___f_675_, v___x_683_, v___x_676_);
return v___x_684_;
}
}
}
}
}
}
LEAN_EXPORT void l_Substring_Raw_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_665_ = stack[0].m_obj;
lean_object* v_p_666_ = stack[1].m_obj;
uint8_t v_res_690_;
v_res_690_ = l_Substring_Raw_any(v_s_665_, v_p_666_);
stack->m_num = v_res_690_;
}
LEAN_EXPORT lean_object* l_Substring_Raw_any___boxed(lean_object* v_s_691_, lean_object* v_p_692_){
_start:
{
uint8_t v_res_693_; lean_object* v_r_694_; 
v_res_693_ = l_Substring_Raw_any(v_s_691_, v_p_692_);
v_r_694_ = lean_box(v_res_693_);
return v_r_694_;
}
}
uint8_t l_Substring_Raw_all(lean_object* v_s_695_, lean_object* v_p_696_){
_start:
{
lean_object* v___y_698_; lean_object* v_startInclusive_699_; lean_object* v_endExclusive_700_; lean_object* v_str_706_; lean_object* v_startPos_707_; lean_object* v_stopPos_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_725_; 
v_str_706_ = lean_ctor_get(v_s_695_, 0);
v_startPos_707_ = lean_ctor_get(v_s_695_, 1);
v_stopPos_708_ = lean_ctor_get(v_s_695_, 2);
v_isSharedCheck_725_ = !lean_is_exclusive(v_s_695_);
if (v_isSharedCheck_725_ == 0)
{
v___x_710_ = v_s_695_;
v_isShared_711_ = v_isSharedCheck_725_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_stopPos_708_);
lean_inc(v_startPos_707_);
lean_inc(v_str_706_);
lean_dec(v_s_695_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_725_;
goto v_resetjp_709_;
}
v___jp_697_:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; uint8_t v_decide_705_; 
v___x_701_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v_p_696_);
v___x_702_ = lean_unsigned_to_nat(0u);
v___x_703_ = l_String_Slice_Pos_skipWhile___redArg(v___y_698_, v___x_702_, v___x_701_);
lean_dec_ref(v___y_698_);
v___x_704_ = lean_nat_sub(v_endExclusive_700_, v_startInclusive_699_);
lean_dec(v_startInclusive_699_);
lean_dec(v_endExclusive_700_);
v_decide_705_ = lean_nat_dec_eq(v___x_703_, v___x_704_);
lean_dec(v___x_704_);
lean_dec(v___x_703_);
return v_decide_705_;
}
v_resetjp_709_:
{
lean_object* v___x_712_; uint8_t v___y_714_; uint8_t v___x_722_; 
v___x_712_ = l_String_instInhabitedSlice;
v___x_722_ = lean_string_is_valid_pos(v_str_706_, v_startPos_707_);
if (v___x_722_ == 0)
{
v___y_714_ = v___x_722_;
goto v___jp_713_;
}
else
{
uint8_t v___x_723_; 
v___x_723_ = lean_string_is_valid_pos(v_str_706_, v_stopPos_708_);
if (v___x_723_ == 0)
{
v___y_714_ = v___x_723_;
goto v___jp_713_;
}
else
{
uint8_t v___x_724_; 
v___x_724_ = lean_nat_dec_le(v_startPos_707_, v_stopPos_708_);
v___y_714_ = v___x_724_;
goto v___jp_713_;
}
}
v___jp_713_:
{
if (v___y_714_ == 0)
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v_startInclusive_717_; lean_object* v_endExclusive_718_; 
lean_del_object(v___x_710_);
lean_dec(v_stopPos_708_);
lean_dec(v_startPos_707_);
lean_dec_ref(v_str_706_);
v___x_715_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_716_ = l_panic___redArg(v___x_712_, v___x_715_);
v_startInclusive_717_ = lean_ctor_get(v___x_716_, 1);
lean_inc(v_startInclusive_717_);
v_endExclusive_718_ = lean_ctor_get(v___x_716_, 2);
lean_inc(v_endExclusive_718_);
v___y_698_ = v___x_716_;
v_startInclusive_699_ = v_startInclusive_717_;
v_endExclusive_700_ = v_endExclusive_718_;
goto v___jp_697_;
}
else
{
lean_object* v___x_720_; 
lean_inc(v_stopPos_708_);
lean_inc(v_startPos_707_);
if (v_isShared_711_ == 0)
{
v___x_720_ = v___x_710_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_str_706_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_startPos_707_);
lean_ctor_set(v_reuseFailAlloc_721_, 2, v_stopPos_708_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
v___y_698_ = v___x_720_;
v_startInclusive_699_ = v_startPos_707_;
v_endExclusive_700_ = v_stopPos_708_;
goto v___jp_697_;
}
}
}
}
}
}
LEAN_EXPORT void l_Substring_Raw_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_695_ = stack[0].m_obj;
lean_object* v_p_696_ = stack[1].m_obj;
uint8_t v_res_726_;
v_res_726_ = l_Substring_Raw_all(v_s_695_, v_p_696_);
stack->m_num = v_res_726_;
}
LEAN_EXPORT lean_object* l_Substring_Raw_all___boxed(lean_object* v_s_727_, lean_object* v_p_728_){
_start:
{
uint8_t v_res_729_; lean_object* v_r_730_; 
v_res_729_ = l_Substring_Raw_all(v_s_727_, v_p_728_);
v_r_730_ = lean_box(v_res_729_);
return v_r_730_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(lean_object* v_msg_731_){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = l_String_instInhabitedSlice;
v___x_733_ = lean_panic_fn_borrowed(v___x_732_, v_msg_731_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0(lean_object* v_p_734_, lean_object* v_s_735_, lean_object* v_pos_736_){
_start:
{
lean_object* v_str_737_; lean_object* v_startInclusive_738_; lean_object* v_endExclusive_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; uint8_t v_decide_743_; 
v_str_737_ = lean_ctor_get(v_s_735_, 0);
v_startInclusive_738_ = lean_ctor_get(v_s_735_, 1);
v_endExclusive_739_ = lean_ctor_get(v_s_735_, 2);
v___x_740_ = lean_nat_add(v_startInclusive_738_, v_pos_736_);
v___x_741_ = lean_unsigned_to_nat(0u);
v___x_742_ = lean_nat_sub(v_endExclusive_739_, v___x_740_);
v_decide_743_ = lean_nat_dec_eq(v___x_741_, v___x_742_);
lean_dec(v___x_742_);
if (v_decide_743_ == 0)
{
uint32_t v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_744_ = lean_string_utf8_get_fast(v_str_737_, v___x_740_);
v___x_745_ = lean_box_uint32(v___x_744_);
lean_inc_ref(v_p_734_);
v___x_746_ = lean_apply_1(v_p_734_, v___x_745_);
v___x_747_ = lean_unbox(v___x_746_);
if (v___x_747_ == 0)
{
lean_dec(v___x_740_);
lean_dec_ref(v_p_734_);
return v_pos_736_;
}
else
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; uint8_t v___x_753_; 
v___x_748_ = lean_string_utf8_next_fast(v_str_737_, v___x_740_);
v___x_749_ = lean_nat_sub(v___x_748_, v___x_740_);
lean_dec(v___x_740_);
v___x_750_ = lean_nat_add(v_pos_736_, v___x_749_);
lean_dec(v___x_749_);
v___x_751_ = lean_unsigned_to_nat(1u);
v___x_752_ = lean_nat_add(v_pos_736_, v___x_751_);
v___x_753_ = lean_nat_dec_le(v___x_752_, v___x_750_);
lean_dec(v___x_752_);
if (v___x_753_ == 0)
{
lean_dec(v___x_750_);
lean_dec_ref(v_p_734_);
return v_pos_736_;
}
else
{
lean_dec(v_pos_736_);
v_pos_736_ = v___x_750_;
goto _start;
}
}
}
else
{
lean_dec(v___x_740_);
lean_dec_ref(v_p_734_);
return v_pos_736_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0___boxed(lean_object* v_p_755_, lean_object* v_s_756_, lean_object* v_pos_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0(v_p_755_, v_s_756_, v_pos_757_);
lean_dec_ref(v_s_756_);
return v_res_758_;
}
}
uint8_t lean_substring_all(lean_object* v_s_759_, lean_object* v_p_760_){
_start:
{
lean_object* v___y_762_; lean_object* v_startInclusive_763_; lean_object* v_endExclusive_764_; lean_object* v_str_769_; lean_object* v_startPos_770_; lean_object* v_stopPos_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_787_; 
v_str_769_ = lean_ctor_get(v_s_759_, 0);
v_startPos_770_ = lean_ctor_get(v_s_759_, 1);
v_stopPos_771_ = lean_ctor_get(v_s_759_, 2);
v_isSharedCheck_787_ = !lean_is_exclusive(v_s_759_);
if (v_isSharedCheck_787_ == 0)
{
v___x_773_ = v_s_759_;
v_isShared_774_ = v_isSharedCheck_787_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_stopPos_771_);
lean_inc(v_startPos_770_);
lean_inc(v_str_769_);
lean_dec(v_s_759_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_787_;
goto v_resetjp_772_;
}
v___jp_761_:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v_decide_768_; 
v___x_765_ = lean_unsigned_to_nat(0u);
v___x_766_ = l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0(v_p_760_, v___y_762_, v___x_765_);
lean_dec_ref(v___y_762_);
v___x_767_ = lean_nat_sub(v_endExclusive_764_, v_startInclusive_763_);
lean_dec(v_startInclusive_763_);
lean_dec(v_endExclusive_764_);
v_decide_768_ = lean_nat_dec_eq(v___x_766_, v___x_767_);
lean_dec(v___x_767_);
lean_dec(v___x_766_);
return v_decide_768_;
}
v_resetjp_772_:
{
uint8_t v___y_776_; uint8_t v___x_784_; 
v___x_784_ = lean_string_is_valid_pos(v_str_769_, v_startPos_770_);
if (v___x_784_ == 0)
{
v___y_776_ = v___x_784_;
goto v___jp_775_;
}
else
{
uint8_t v___x_785_; 
v___x_785_ = lean_string_is_valid_pos(v_str_769_, v_stopPos_771_);
if (v___x_785_ == 0)
{
v___y_776_ = v___x_785_;
goto v___jp_775_;
}
else
{
uint8_t v___x_786_; 
v___x_786_ = lean_nat_dec_le(v_startPos_770_, v_stopPos_771_);
v___y_776_ = v___x_786_;
goto v___jp_775_;
}
}
v___jp_775_:
{
if (v___y_776_ == 0)
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v_startInclusive_779_; lean_object* v_endExclusive_780_; 
lean_del_object(v___x_773_);
lean_dec(v_stopPos_771_);
lean_dec(v_startPos_770_);
lean_dec_ref(v_str_769_);
v___x_777_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_778_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_777_);
v_startInclusive_779_ = lean_ctor_get(v___x_778_, 1);
lean_inc(v_startInclusive_779_);
v_endExclusive_780_ = lean_ctor_get(v___x_778_, 2);
lean_inc(v_endExclusive_780_);
v___y_762_ = v___x_778_;
v_startInclusive_763_ = v_startInclusive_779_;
v_endExclusive_764_ = v_endExclusive_780_;
goto v___jp_761_;
}
else
{
lean_object* v___x_782_; 
lean_inc(v_stopPos_771_);
lean_inc(v_startPos_770_);
if (v_isShared_774_ == 0)
{
v___x_782_ = v___x_773_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_str_769_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_startPos_770_);
lean_ctor_set(v_reuseFailAlloc_783_, 2, v_stopPos_771_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
v___y_762_ = v___x_782_;
v_startInclusive_763_ = v_startPos_770_;
v_endExclusive_764_ = v_stopPos_771_;
goto v___jp_761_;
}
}
}
}
}
}
LEAN_EXPORT void lean_substring_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_759_ = stack[0].m_obj;
lean_object* v_p_760_ = stack[1].m_obj;
uint8_t v_res_788_;
v_res_788_ = lean_substring_all(v_s_759_, v_p_760_);
stack->m_num = v_res_788_;
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_allImpl___boxed(lean_object* v_s_789_, lean_object* v_p_790_){
_start:
{
uint8_t v_res_791_; lean_object* v_r_792_; 
v_res_791_ = lean_substring_all(v_s_789_, v_p_790_);
v_r_792_ = lean_box(v_res_791_);
return v_r_792_;
}
}
uint8_t l_Substring_Raw_contains___lam__0(uint32_t v_c_793_, uint32_t v_a_794_){
_start:
{
uint8_t v___x_795_; 
v___x_795_ = lean_uint32_dec_eq(v_a_794_, v_c_793_);
return v___x_795_;
}
}
LEAN_EXPORT void l_Substring_Raw_contains___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_793_ = stack[0].m_num;
uint32_t v_a_794_ = stack[1].m_num;
uint8_t v_res_796_;
v_res_796_ = l_Substring_Raw_contains___lam__0(v_c_793_, v_a_794_);
stack->m_num = v_res_796_;
}
LEAN_EXPORT lean_object* l_Substring_Raw_contains___lam__0___boxed(lean_object* v_c_797_, lean_object* v_a_798_){
_start:
{
uint32_t v_c_boxed_799_; uint32_t v_a_boxed_800_; uint8_t v_res_801_; lean_object* v_r_802_; 
v_c_boxed_799_ = lean_unbox_uint32(v_c_797_);
lean_dec(v_c_797_);
v_a_boxed_800_ = lean_unbox_uint32(v_a_798_);
lean_dec(v_a_798_);
v_res_801_ = l_Substring_Raw_contains___lam__0(v_c_boxed_799_, v_a_boxed_800_);
v_r_802_ = lean_box(v_res_801_);
return v_r_802_;
}
}
uint8_t l_Substring_Raw_contains(lean_object* v_s_803_, uint32_t v_c_804_){
_start:
{
lean_object* v___x_805_; lean_object* v___f_806_; lean_object* v___x_807_; lean_object* v_str_808_; lean_object* v_startPos_809_; lean_object* v_stopPos_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_829_; 
v___x_805_ = lean_box_uint32(v_c_804_);
v___f_806_ = lean_alloc_closure((void*)(l_Substring_Raw_contains___lam__0___boxed), 2, 1);
lean_closure_set(v___f_806_, 0, v___x_805_);
lean_inc_ref(v___f_806_);
v___x_807_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___f_806_);
v_str_808_ = lean_ctor_get(v_s_803_, 0);
v_startPos_809_ = lean_ctor_get(v_s_803_, 1);
v_stopPos_810_ = lean_ctor_get(v_s_803_, 2);
v_isSharedCheck_829_ = !lean_is_exclusive(v_s_803_);
if (v_isSharedCheck_829_ == 0)
{
v___x_812_ = v_s_803_;
v_isShared_813_ = v_isSharedCheck_829_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_stopPos_810_);
lean_inc(v_startPos_809_);
lean_inc(v_str_808_);
lean_dec(v_s_803_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_829_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_814_; lean_object* v___f_815_; lean_object* v___x_816_; uint8_t v___y_818_; uint8_t v___x_826_; 
v___x_814_ = l_String_instInhabitedSlice;
v___f_815_ = lean_alloc_closure((void*)(l_Substring_Raw_any___lam__0), 8, 1);
lean_closure_set(v___f_815_, 0, v___x_807_);
v___x_816_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_816_, 0, lean_box(0));
lean_closure_set(v___x_816_, 1, v___f_806_);
v___x_826_ = lean_string_is_valid_pos(v_str_808_, v_startPos_809_);
if (v___x_826_ == 0)
{
v___y_818_ = v___x_826_;
goto v___jp_817_;
}
else
{
uint8_t v___x_827_; 
v___x_827_ = lean_string_is_valid_pos(v_str_808_, v_stopPos_810_);
if (v___x_827_ == 0)
{
v___y_818_ = v___x_827_;
goto v___jp_817_;
}
else
{
uint8_t v___x_828_; 
v___x_828_ = lean_nat_dec_le(v_startPos_809_, v_stopPos_810_);
v___y_818_ = v___x_828_;
goto v___jp_817_;
}
}
v___jp_817_:
{
if (v___y_818_ == 0)
{
lean_object* v___x_819_; lean_object* v___x_820_; uint8_t v___x_821_; 
lean_del_object(v___x_812_);
lean_dec(v_stopPos_810_);
lean_dec(v_startPos_809_);
lean_dec_ref(v_str_808_);
v___x_819_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_820_ = l_panic___redArg(v___x_814_, v___x_819_);
v___x_821_ = l_String_Slice_contains___redArg(v___f_815_, v___x_820_, v___x_816_);
return v___x_821_;
}
else
{
lean_object* v___x_823_; 
if (v_isShared_813_ == 0)
{
v___x_823_ = v___x_812_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_str_808_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v_startPos_809_);
lean_ctor_set(v_reuseFailAlloc_825_, 2, v_stopPos_810_);
v___x_823_ = v_reuseFailAlloc_825_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
uint8_t v___x_824_; 
v___x_824_ = l_String_Slice_contains___redArg(v___f_815_, v___x_823_, v___x_816_);
return v___x_824_;
}
}
}
}
}
}
LEAN_EXPORT void l_Substring_Raw_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_803_ = stack[0].m_obj;
uint32_t v_c_804_ = stack[1].m_num;
uint8_t v_res_830_;
v_res_830_ = l_Substring_Raw_contains(v_s_803_, v_c_804_);
stack->m_num = v_res_830_;
}
LEAN_EXPORT lean_object* l_Substring_Raw_contains___boxed(lean_object* v_s_831_, lean_object* v_c_832_){
_start:
{
uint32_t v_c_boxed_833_; uint8_t v_res_834_; lean_object* v_r_835_; 
v_c_boxed_833_ = lean_unbox_uint32(v_c_832_);
lean_dec(v_c_832_);
v_res_834_ = l_Substring_Raw_contains(v_s_831_, v_c_boxed_833_);
v_r_835_ = lean_box(v_res_834_);
return v_r_835_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux(lean_object* v_s_836_, lean_object* v_stopPos_837_, lean_object* v_p_838_, lean_object* v_i_839_){
_start:
{
uint8_t v___y_841_; lean_object* v___x_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_844_ = lean_unsigned_to_nat(1u);
v___x_845_ = lean_nat_add(v_i_839_, v___x_844_);
v___x_846_ = lean_nat_dec_le(v___x_845_, v_stopPos_837_);
lean_dec(v___x_845_);
if (v___x_846_ == 0)
{
lean_dec_ref(v_p_838_);
return v_i_839_;
}
else
{
if (v___x_846_ == 0)
{
v___y_841_ = v___x_846_;
goto v___jp_840_;
}
else
{
uint32_t v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; uint8_t v___x_850_; 
v___x_847_ = lean_string_utf8_get(v_s_836_, v_i_839_);
v___x_848_ = lean_box_uint32(v___x_847_);
lean_inc_ref(v_p_838_);
v___x_849_ = lean_apply_1(v_p_838_, v___x_848_);
v___x_850_ = lean_unbox(v___x_849_);
v___y_841_ = v___x_850_;
goto v___jp_840_;
}
}
v___jp_840_:
{
if (v___y_841_ == 0)
{
lean_dec_ref(v_p_838_);
return v_i_839_;
}
else
{
lean_object* v___x_842_; 
v___x_842_ = lean_string_utf8_next(v_s_836_, v_i_839_);
lean_dec(v_i_839_);
v_i_839_ = v___x_842_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___boxed(lean_object* v_s_851_, lean_object* v_stopPos_852_, lean_object* v_p_853_, lean_object* v_i_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Substring_Raw_takeWhileAux(v_s_851_, v_stopPos_852_, v_p_853_, v_i_854_);
lean_dec(v_stopPos_852_);
lean_dec_ref(v_s_851_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhile(lean_object* v_x_856_, lean_object* v_x_857_){
_start:
{
lean_object* v_str_858_; lean_object* v_startPos_859_; lean_object* v_stopPos_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_868_; 
v_str_858_ = lean_ctor_get(v_x_856_, 0);
v_startPos_859_ = lean_ctor_get(v_x_856_, 1);
v_stopPos_860_ = lean_ctor_get(v_x_856_, 2);
v_isSharedCheck_868_ = !lean_is_exclusive(v_x_856_);
if (v_isSharedCheck_868_ == 0)
{
v___x_862_ = v_x_856_;
v_isShared_863_ = v_isSharedCheck_868_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_stopPos_860_);
lean_inc(v_startPos_859_);
lean_inc(v_str_858_);
lean_dec(v_x_856_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_868_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v_e_864_; lean_object* v___x_866_; 
lean_inc(v_startPos_859_);
v_e_864_ = l_Substring_Raw_takeWhileAux(v_str_858_, v_stopPos_860_, v_x_857_, v_startPos_859_);
lean_dec(v_stopPos_860_);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 2, v_e_864_);
v___x_866_ = v___x_862_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_str_858_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v_startPos_859_);
lean_ctor_set(v_reuseFailAlloc_867_, 2, v_e_864_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(lean_object* v_a_869_, lean_object* v_s_870_, lean_object* v_stopPos_871_, lean_object* v_i_872_){
_start:
{
uint8_t v___y_874_; lean_object* v___x_877_; lean_object* v___x_878_; uint8_t v___x_879_; 
v___x_877_ = lean_unsigned_to_nat(1u);
v___x_878_ = lean_nat_add(v_i_872_, v___x_877_);
v___x_879_ = lean_nat_dec_le(v___x_878_, v_stopPos_871_);
lean_dec(v___x_878_);
if (v___x_879_ == 0)
{
lean_dec_ref(v_a_869_);
return v_i_872_;
}
else
{
if (v___x_879_ == 0)
{
v___y_874_ = v___x_879_;
goto v___jp_873_;
}
else
{
uint32_t v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; uint8_t v___x_883_; 
v___x_880_ = lean_string_utf8_get(v_s_870_, v_i_872_);
v___x_881_ = lean_box_uint32(v___x_880_);
lean_inc_ref(v_a_869_);
v___x_882_ = lean_apply_1(v_a_869_, v___x_881_);
v___x_883_ = lean_unbox(v___x_882_);
v___y_874_ = v___x_883_;
goto v___jp_873_;
}
}
v___jp_873_:
{
if (v___y_874_ == 0)
{
lean_dec_ref(v_a_869_);
return v_i_872_;
}
else
{
lean_object* v___x_875_; 
v___x_875_ = lean_string_utf8_next(v_s_870_, v_i_872_);
lean_dec(v_i_872_);
v_i_872_ = v___x_875_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0___boxed(lean_object* v_a_884_, lean_object* v_s_885_, lean_object* v_stopPos_886_, lean_object* v_i_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(v_a_884_, v_s_885_, v_stopPos_886_, v_i_887_);
lean_dec(v_stopPos_886_);
lean_dec_ref(v_s_885_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* lean_substring_takewhile(lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v_str_891_; lean_object* v_startPos_892_; lean_object* v_stopPos_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_901_; 
v_str_891_ = lean_ctor_get(v_a_889_, 0);
v_startPos_892_ = lean_ctor_get(v_a_889_, 1);
v_stopPos_893_ = lean_ctor_get(v_a_889_, 2);
v_isSharedCheck_901_ = !lean_is_exclusive(v_a_889_);
if (v_isSharedCheck_901_ == 0)
{
v___x_895_ = v_a_889_;
v_isShared_896_ = v_isSharedCheck_901_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_stopPos_893_);
lean_inc(v_startPos_892_);
lean_inc(v_str_891_);
lean_dec(v_a_889_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_901_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v_e_897_; lean_object* v___x_899_; 
lean_inc(v_startPos_892_);
v_e_897_ = l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(v_a_890_, v_str_891_, v_stopPos_893_, v_startPos_892_);
lean_dec(v_stopPos_893_);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 2, v_e_897_);
v___x_899_ = v___x_895_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_str_891_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_startPos_892_);
lean_ctor_set(v_reuseFailAlloc_900_, 2, v_e_897_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropWhile(lean_object* v_x_902_, lean_object* v_x_903_){
_start:
{
lean_object* v_str_904_; lean_object* v_startPos_905_; lean_object* v_stopPos_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_914_; 
v_str_904_ = lean_ctor_get(v_x_902_, 0);
v_startPos_905_ = lean_ctor_get(v_x_902_, 1);
v_stopPos_906_ = lean_ctor_get(v_x_902_, 2);
v_isSharedCheck_914_ = !lean_is_exclusive(v_x_902_);
if (v_isSharedCheck_914_ == 0)
{
v___x_908_ = v_x_902_;
v_isShared_909_ = v_isSharedCheck_914_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_stopPos_906_);
lean_inc(v_startPos_905_);
lean_inc(v_str_904_);
lean_dec(v_x_902_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_914_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v_b_910_; lean_object* v___x_912_; 
v_b_910_ = l_Substring_Raw_takeWhileAux(v_str_904_, v_stopPos_906_, v_x_903_, v_startPos_905_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 1, v_b_910_);
v___x_912_ = v___x_908_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_str_904_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_b_910_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v_stopPos_906_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux(lean_object* v_s_915_, lean_object* v_begPos_916_, lean_object* v_p_917_, lean_object* v_i_918_){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; uint8_t v___x_921_; 
v___x_919_ = lean_unsigned_to_nat(1u);
v___x_920_ = lean_nat_add(v_begPos_916_, v___x_919_);
v___x_921_ = lean_nat_dec_le(v___x_920_, v_i_918_);
lean_dec(v___x_920_);
if (v___x_921_ == 0)
{
lean_dec_ref(v_p_917_);
return v_i_918_;
}
else
{
lean_object* v_i_x27_922_; uint8_t v___y_924_; uint8_t v___y_927_; uint32_t v_c_928_; lean_object* v___x_929_; lean_object* v___x_930_; uint8_t v___x_931_; 
v_i_x27_922_ = lean_string_utf8_prev(v_s_915_, v_i_918_);
v_c_928_ = lean_string_utf8_get(v_s_915_, v_i_x27_922_);
v___x_929_ = lean_box_uint32(v_c_928_);
lean_inc_ref(v_p_917_);
v___x_930_ = lean_apply_1(v_p_917_, v___x_929_);
v___x_931_ = lean_unbox(v___x_930_);
if (v___x_931_ == 0)
{
v___y_927_ = v___x_921_;
goto v___jp_926_;
}
else
{
uint8_t v___x_932_; 
v___x_932_ = 0;
v___y_927_ = v___x_932_;
goto v___jp_926_;
}
v___jp_923_:
{
if (v___y_924_ == 0)
{
lean_dec(v_i_918_);
v_i_918_ = v_i_x27_922_;
goto _start;
}
else
{
lean_dec(v_i_x27_922_);
lean_dec_ref(v_p_917_);
return v_i_918_;
}
}
v___jp_926_:
{
if (v___x_921_ == 0)
{
v___y_924_ = v___x_921_;
goto v___jp_923_;
}
else
{
v___y_924_ = v___y_927_;
goto v___jp_923_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux___boxed(lean_object* v_s_933_, lean_object* v_begPos_934_, lean_object* v_p_935_, lean_object* v_i_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Substring_Raw_takeRightWhileAux(v_s_933_, v_begPos_934_, v_p_935_, v_i_936_);
lean_dec(v_begPos_934_);
lean_dec_ref(v_s_933_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhile(lean_object* v_x_938_, lean_object* v_x_939_){
_start:
{
lean_object* v_str_940_; lean_object* v_startPos_941_; lean_object* v_stopPos_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_950_; 
v_str_940_ = lean_ctor_get(v_x_938_, 0);
v_startPos_941_ = lean_ctor_get(v_x_938_, 1);
v_stopPos_942_ = lean_ctor_get(v_x_938_, 2);
v_isSharedCheck_950_ = !lean_is_exclusive(v_x_938_);
if (v_isSharedCheck_950_ == 0)
{
v___x_944_ = v_x_938_;
v_isShared_945_ = v_isSharedCheck_950_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_stopPos_942_);
lean_inc(v_startPos_941_);
lean_inc(v_str_940_);
lean_dec(v_x_938_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_950_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v_b_946_; lean_object* v___x_948_; 
lean_inc(v_stopPos_942_);
v_b_946_ = l_Substring_Raw_takeRightWhileAux(v_str_940_, v_startPos_941_, v_x_939_, v_stopPos_942_);
lean_dec(v_startPos_941_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 1, v_b_946_);
v___x_948_ = v___x_944_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_str_940_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_b_946_);
lean_ctor_set(v_reuseFailAlloc_949_, 2, v_stopPos_942_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropRightWhile(lean_object* v_x_951_, lean_object* v_x_952_){
_start:
{
lean_object* v_str_953_; lean_object* v_startPos_954_; lean_object* v_stopPos_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_963_; 
v_str_953_ = lean_ctor_get(v_x_951_, 0);
v_startPos_954_ = lean_ctor_get(v_x_951_, 1);
v_stopPos_955_ = lean_ctor_get(v_x_951_, 2);
v_isSharedCheck_963_ = !lean_is_exclusive(v_x_951_);
if (v_isSharedCheck_963_ == 0)
{
v___x_957_ = v_x_951_;
v_isShared_958_ = v_isSharedCheck_963_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_stopPos_955_);
lean_inc(v_startPos_954_);
lean_inc(v_str_953_);
lean_dec(v_x_951_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_963_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v_e_959_; lean_object* v___x_961_; 
v_e_959_ = l_Substring_Raw_takeRightWhileAux(v_str_953_, v_startPos_954_, v_x_952_, v_stopPos_955_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 2, v_e_959_);
v___x_961_ = v___x_957_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_str_953_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_startPos_954_);
lean_ctor_set(v_reuseFailAlloc_962_, 2, v_e_959_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_trimLeft(lean_object* v_s_965_){
_start:
{
lean_object* v_str_966_; lean_object* v_startPos_967_; lean_object* v_stopPos_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_977_; 
v_str_966_ = lean_ctor_get(v_s_965_, 0);
v_startPos_967_ = lean_ctor_get(v_s_965_, 1);
v_stopPos_968_ = lean_ctor_get(v_s_965_, 2);
v_isSharedCheck_977_ = !lean_is_exclusive(v_s_965_);
if (v_isSharedCheck_977_ == 0)
{
v___x_970_ = v_s_965_;
v_isShared_971_ = v_isSharedCheck_977_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_stopPos_968_);
lean_inc(v_startPos_967_);
lean_inc(v_str_966_);
lean_dec(v_s_965_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_977_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; lean_object* v_b_973_; lean_object* v___x_975_; 
v___x_972_ = ((lean_object*)(l_Substring_Raw_trimLeft___closed__0));
v_b_973_ = l_Substring_Raw_takeWhileAux(v_str_966_, v_stopPos_968_, v___x_972_, v_startPos_967_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 1, v_b_973_);
v___x_975_ = v___x_970_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_str_966_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_b_973_);
lean_ctor_set(v_reuseFailAlloc_976_, 2, v_stopPos_968_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_trimRight(lean_object* v_s_978_){
_start:
{
lean_object* v_str_979_; lean_object* v_startPos_980_; lean_object* v_stopPos_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_990_; 
v_str_979_ = lean_ctor_get(v_s_978_, 0);
v_startPos_980_ = lean_ctor_get(v_s_978_, 1);
v_stopPos_981_ = lean_ctor_get(v_s_978_, 2);
v_isSharedCheck_990_ = !lean_is_exclusive(v_s_978_);
if (v_isSharedCheck_990_ == 0)
{
v___x_983_ = v_s_978_;
v_isShared_984_ = v_isSharedCheck_990_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_stopPos_981_);
lean_inc(v_startPos_980_);
lean_inc(v_str_979_);
lean_dec(v_s_978_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_990_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_985_; lean_object* v_e_986_; lean_object* v___x_988_; 
v___x_985_ = ((lean_object*)(l_Substring_Raw_trimLeft___closed__0));
v_e_986_ = l_Substring_Raw_takeRightWhileAux(v_str_979_, v_startPos_980_, v___x_985_, v_stopPos_981_);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 2, v_e_986_);
v___x_988_ = v___x_983_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_str_979_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_startPos_980_);
lean_ctor_set(v_reuseFailAlloc_989_, 2, v_e_986_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_trim(lean_object* v_x_991_){
_start:
{
lean_object* v_str_992_; lean_object* v_startPos_993_; lean_object* v_stopPos_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1004_; 
v_str_992_ = lean_ctor_get(v_x_991_, 0);
v_startPos_993_ = lean_ctor_get(v_x_991_, 1);
v_stopPos_994_ = lean_ctor_get(v_x_991_, 2);
v_isSharedCheck_1004_ = !lean_is_exclusive(v_x_991_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_996_ = v_x_991_;
v_isShared_997_ = v_isSharedCheck_1004_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_stopPos_994_);
lean_inc(v_startPos_993_);
lean_inc(v_str_992_);
lean_dec(v_x_991_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1004_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_998_; lean_object* v_b_999_; lean_object* v_e_1000_; lean_object* v___x_1002_; 
v___x_998_ = ((lean_object*)(l_Substring_Raw_trimLeft___closed__0));
v_b_999_ = l_Substring_Raw_takeWhileAux(v_str_992_, v_stopPos_994_, v___x_998_, v_startPos_993_);
v_e_1000_ = l_Substring_Raw_takeRightWhileAux(v_str_992_, v_b_999_, v___x_998_, v_stopPos_994_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 2, v_e_1000_);
lean_ctor_set(v___x_996_, 1, v_b_999_);
v___x_1002_ = v___x_996_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_str_992_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v_b_999_);
lean_ctor_set(v_reuseFailAlloc_1003_, 2, v_e_1000_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
lean_object* l_Substring_Raw_isNat___lam__0(lean_object* v___y_1005_, uint8_t v___x_1006_, uint8_t v___x_1007_, lean_object* v_it_1008_, lean_object* v_acc_1009_, lean_object* v_hP_1010_, lean_object* v_recur_1011_){
_start:
{
lean_object* v_str_1012_; lean_object* v_startInclusive_1013_; lean_object* v_endExclusive_1014_; lean_object* v___x_1015_; uint8_t v_decide_1016_; 
v_str_1012_ = lean_ctor_get(v___y_1005_, 0);
v_startInclusive_1013_ = lean_ctor_get(v___y_1005_, 1);
v_endExclusive_1014_ = lean_ctor_get(v___y_1005_, 2);
v___x_1015_ = lean_nat_sub(v_endExclusive_1014_, v_startInclusive_1013_);
v_decide_1016_ = lean_nat_dec_eq(v_it_1008_, v___x_1015_);
lean_dec(v___x_1015_);
if (v_decide_1016_ == 0)
{
lean_object* v_snd_1017_; lean_object* v_snd_1018_; lean_object* v_fst_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1079_; 
v_snd_1017_ = lean_ctor_get(v_acc_1009_, 1);
lean_inc(v_snd_1017_);
v_snd_1018_ = lean_ctor_get(v_snd_1017_, 1);
lean_inc(v_snd_1018_);
v_fst_1019_ = lean_ctor_get(v_acc_1009_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v_acc_1009_);
if (v_isSharedCheck_1079_ == 0)
{
lean_object* v_unused_1080_; 
v_unused_1080_ = lean_ctor_get(v_acc_1009_, 1);
lean_dec(v_unused_1080_);
v___x_1021_ = v_acc_1009_;
v_isShared_1022_ = v_isSharedCheck_1079_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_fst_1019_);
lean_dec(v_acc_1009_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1079_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v_fst_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1077_; 
v_fst_1023_ = lean_ctor_get(v_snd_1017_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_snd_1017_);
if (v_isSharedCheck_1077_ == 0)
{
lean_object* v_unused_1078_; 
v_unused_1078_ = lean_ctor_get(v_snd_1017_, 1);
lean_dec(v_unused_1078_);
v___x_1025_ = v_snd_1017_;
v_isShared_1026_ = v_isSharedCheck_1077_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_fst_1023_);
lean_dec(v_snd_1017_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1077_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v_snd_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1075_; 
v_snd_1027_ = lean_ctor_get(v_snd_1018_, 1);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_snd_1018_);
if (v_isSharedCheck_1075_ == 0)
{
lean_object* v_unused_1076_; 
v_unused_1076_ = lean_ctor_get(v_snd_1018_, 0);
lean_dec(v_unused_1076_);
v___x_1029_ = v_snd_1018_;
v_isShared_1030_ = v_isSharedCheck_1075_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_snd_1027_);
lean_dec(v_snd_1018_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1075_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1031_; uint32_t v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; uint8_t v___y_1036_; uint8_t v___y_1037_; uint8_t v___y_1055_; uint8_t v___y_1056_; uint8_t v___y_1061_; uint8_t v___y_1062_; uint8_t v___y_1067_; uint32_t v___x_1071_; uint8_t v___x_1072_; 
v___x_1031_ = lean_nat_add(v_startInclusive_1013_, v_it_1008_);
v___x_1032_ = lean_string_utf8_get_fast(v_str_1012_, v___x_1031_);
v___x_1033_ = lean_string_utf8_next_fast(v_str_1012_, v___x_1031_);
lean_dec(v___x_1031_);
v___x_1034_ = lean_nat_sub(v___x_1033_, v_startInclusive_1013_);
v___x_1071_ = 48;
v___x_1072_ = lean_uint32_dec_le(v___x_1071_, v___x_1032_);
if (v___x_1072_ == 0)
{
v___y_1067_ = v___x_1072_;
goto v___jp_1066_;
}
else
{
uint32_t v___x_1073_; uint8_t v___x_1074_; 
v___x_1073_ = 57;
v___x_1074_ = lean_uint32_dec_le(v___x_1032_, v___x_1073_);
v___y_1067_ = v___x_1074_;
goto v___jp_1066_;
}
v___jp_1035_:
{
uint32_t v___x_1038_; uint8_t v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1043_; 
v___x_1038_ = 95;
v___x_1039_ = lean_uint32_dec_eq(v___x_1032_, v___x_1038_);
v___x_1040_ = lean_box(v___y_1036_);
v___x_1041_ = lean_box(v___y_1037_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 1, v___x_1041_);
lean_ctor_set(v___x_1029_, 0, v___x_1040_);
v___x_1043_ = v___x_1029_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
lean_object* v___x_1044_; lean_object* v___x_1046_; 
v___x_1044_ = lean_box(v___x_1039_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 1, v___x_1043_);
lean_ctor_set(v___x_1025_, 0, v___x_1044_);
v___x_1046_ = v___x_1025_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v___x_1043_);
v___x_1046_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1047_; lean_object* v___x_1049_; 
v___x_1047_ = lean_box(v___x_1006_);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 1, v___x_1046_);
lean_ctor_set(v___x_1021_, 0, v___x_1047_);
v___x_1049_ = v___x_1021_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v___x_1046_);
v___x_1049_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_apply_4(v_recur_1011_, v___x_1034_, v___x_1049_, lean_box(0), lean_box(0));
return v___x_1050_;
}
}
}
}
v___jp_1054_:
{
uint8_t v___x_1057_; 
v___x_1057_ = lean_unbox(v_fst_1023_);
lean_dec(v_fst_1023_);
if (v___x_1057_ == 0)
{
v___y_1036_ = v___y_1055_;
v___y_1037_ = v___y_1056_;
goto v___jp_1035_;
}
else
{
uint32_t v___x_1058_; uint8_t v___x_1059_; 
v___x_1058_ = 95;
v___x_1059_ = lean_uint32_dec_eq(v___x_1032_, v___x_1058_);
if (v___x_1059_ == 0)
{
v___y_1036_ = v___y_1055_;
v___y_1037_ = v___y_1056_;
goto v___jp_1035_;
}
else
{
v___y_1036_ = v___y_1055_;
v___y_1037_ = v___x_1006_;
goto v___jp_1035_;
}
}
}
v___jp_1060_:
{
uint8_t v___x_1063_; 
v___x_1063_ = lean_unbox(v_fst_1019_);
lean_dec(v_fst_1019_);
if (v___x_1063_ == 0)
{
v___y_1055_ = v___y_1061_;
v___y_1056_ = v___y_1062_;
goto v___jp_1054_;
}
else
{
uint32_t v___x_1064_; uint8_t v___x_1065_; 
v___x_1064_ = 95;
v___x_1065_ = lean_uint32_dec_eq(v___x_1032_, v___x_1064_);
if (v___x_1065_ == 0)
{
v___y_1055_ = v___y_1061_;
v___y_1056_ = v___y_1062_;
goto v___jp_1054_;
}
else
{
lean_dec(v_fst_1023_);
v___y_1036_ = v___y_1061_;
v___y_1037_ = v___x_1006_;
goto v___jp_1035_;
}
}
}
v___jp_1066_:
{
uint8_t v___x_1068_; 
v___x_1068_ = lean_unbox(v_snd_1027_);
lean_dec(v_snd_1027_);
if (v___x_1068_ == 0)
{
lean_dec(v_fst_1023_);
lean_dec(v_fst_1019_);
v___y_1036_ = v___y_1067_;
v___y_1037_ = v___x_1006_;
goto v___jp_1035_;
}
else
{
if (v___y_1067_ == 0)
{
uint32_t v___x_1069_; uint8_t v___x_1070_; 
v___x_1069_ = 95;
v___x_1070_ = lean_uint32_dec_eq(v___x_1032_, v___x_1069_);
if (v___x_1070_ == 0)
{
lean_dec(v_fst_1023_);
lean_dec(v_fst_1019_);
v___y_1036_ = v___y_1067_;
v___y_1037_ = v___x_1006_;
goto v___jp_1035_;
}
else
{
v___y_1061_ = v___y_1067_;
v___y_1062_ = v___x_1070_;
goto v___jp_1060_;
}
}
else
{
v___y_1061_ = v___y_1067_;
v___y_1062_ = v___x_1007_;
goto v___jp_1060_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_recur_1011_);
return v_acc_1009_;
}
}
}
LEAN_EXPORT void l_Substring_Raw_isNat___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1005_ = stack[0].m_obj;
uint8_t v___x_1006_ = stack[1].m_num;
uint8_t v___x_1007_ = stack[2].m_num;
lean_object* v_it_1008_ = stack[3].m_obj;
lean_object* v_acc_1009_ = stack[4].m_obj;
lean_object* v_recur_1011_ = stack[6].m_obj;
lean_object* v_res_1081_;
v_res_1081_ = l_Substring_Raw_isNat___lam__0(v___y_1005_, v___x_1006_, v___x_1007_, v_it_1008_, v_acc_1009_, lean_box(0), v_recur_1011_);
stack->m_obj
 = v_res_1081_;
}
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___lam__0___boxed(lean_object* v___y_1082_, lean_object* v___x_1083_, lean_object* v___x_1084_, lean_object* v_it_1085_, lean_object* v_acc_1086_, lean_object* v_hP_1087_, lean_object* v_recur_1088_){
_start:
{
uint8_t v___x_792__boxed_1089_; uint8_t v___x_793__boxed_1090_; lean_object* v_res_1091_; 
v___x_792__boxed_1089_ = lean_unbox(v___x_1083_);
v___x_793__boxed_1090_ = lean_unbox(v___x_1084_);
v_res_1091_ = l_Substring_Raw_isNat___lam__0(v___y_1082_, v___x_792__boxed_1089_, v___x_793__boxed_1090_, v_it_1085_, v_acc_1086_, v_hP_1087_, v_recur_1088_);
lean_dec(v_it_1085_);
lean_dec_ref(v___y_1082_);
return v_res_1091_;
}
}
uint8_t l_Substring_Raw_isNat(lean_object* v_s_1092_){
_start:
{
lean_object* v_str_1093_; lean_object* v_startPos_1094_; lean_object* v_stopPos_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1134_; 
v_str_1093_ = lean_ctor_get(v_s_1092_, 0);
v_startPos_1094_ = lean_ctor_get(v_s_1092_, 1);
v_stopPos_1095_ = lean_ctor_get(v_s_1092_, 2);
v_isSharedCheck_1134_ = !lean_is_exclusive(v_s_1092_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1097_ = v_s_1092_;
v_isShared_1098_ = v_isSharedCheck_1134_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_stopPos_1095_);
lean_inc(v_startPos_1094_);
lean_inc(v_str_1093_);
lean_dec(v_s_1092_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1134_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; 
v___x_1099_ = lean_nat_sub(v_stopPos_1095_, v_startPos_1094_);
v___x_1100_ = lean_unsigned_to_nat(0u);
v___x_1101_ = lean_nat_dec_eq(v___x_1099_, v___x_1100_);
lean_dec(v___x_1099_);
if (v___x_1101_ == 0)
{
uint8_t v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___y_1111_; lean_object* v___x_1122_; uint8_t v___y_1124_; uint8_t v___x_1130_; 
v___x_1102_ = 1;
v___x_1103_ = lean_box(v___x_1101_);
v___x_1104_ = lean_box(v___x_1102_);
v___x_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1103_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
v___x_1106_ = lean_box(v___x_1101_);
v___x_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
lean_ctor_set(v___x_1107_, 1, v___x_1105_);
v___x_1108_ = lean_box(v___x_1102_);
v___x_1109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
lean_ctor_set(v___x_1109_, 1, v___x_1107_);
v___x_1122_ = l_String_instInhabitedSlice;
v___x_1130_ = lean_string_is_valid_pos(v_str_1093_, v_startPos_1094_);
if (v___x_1130_ == 0)
{
v___y_1124_ = v___x_1130_;
goto v___jp_1123_;
}
else
{
uint8_t v___x_1131_; 
v___x_1131_ = lean_string_is_valid_pos(v_str_1093_, v_stopPos_1095_);
if (v___x_1131_ == 0)
{
v___y_1124_ = v___x_1131_;
goto v___jp_1123_;
}
else
{
uint8_t v___x_1132_; 
v___x_1132_ = lean_nat_dec_le(v_startPos_1094_, v_stopPos_1095_);
v___y_1124_ = v___x_1132_;
goto v___jp_1123_;
}
}
v___jp_1110_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___f_1114_; lean_object* v___x_1115_; lean_object* v_snd_1116_; lean_object* v_snd_1117_; lean_object* v_snd_1118_; uint8_t v___x_1119_; 
v___x_1112_ = lean_box(v___x_1101_);
v___x_1113_ = lean_box(v___x_1102_);
v___f_1114_ = lean_alloc_closure((void*)(l_Substring_Raw_isNat___lam__0___boxed), 7, 3);
lean_closure_set(v___f_1114_, 0, v___y_1111_);
lean_closure_set(v___f_1114_, 1, v___x_1112_);
lean_closure_set(v___f_1114_, 2, v___x_1113_);
v___x_1115_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1114_, v___x_1100_, v___x_1109_, lean_box(0));
v_snd_1116_ = lean_ctor_get(v___x_1115_, 1);
lean_inc(v_snd_1116_);
lean_dec(v___x_1115_);
v_snd_1117_ = lean_ctor_get(v_snd_1116_, 1);
lean_inc(v_snd_1117_);
lean_dec(v_snd_1116_);
v_snd_1118_ = lean_ctor_get(v_snd_1117_, 1);
v___x_1119_ = lean_unbox(v_snd_1118_);
if (v___x_1119_ == 0)
{
lean_dec(v_snd_1117_);
return v___x_1101_;
}
else
{
lean_object* v_fst_1120_; uint8_t v___x_1121_; 
v_fst_1120_ = lean_ctor_get(v_snd_1117_, 0);
lean_inc(v_fst_1120_);
lean_dec(v_snd_1117_);
v___x_1121_ = lean_unbox(v_fst_1120_);
lean_dec(v_fst_1120_);
return v___x_1121_;
}
}
v___jp_1123_:
{
if (v___y_1124_ == 0)
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
lean_del_object(v___x_1097_);
lean_dec(v_stopPos_1095_);
lean_dec(v_startPos_1094_);
lean_dec_ref(v_str_1093_);
v___x_1125_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_1126_ = l_panic___redArg(v___x_1122_, v___x_1125_);
v___y_1111_ = v___x_1126_;
goto v___jp_1110_;
}
else
{
lean_object* v___x_1128_; 
if (v_isShared_1098_ == 0)
{
v___x_1128_ = v___x_1097_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_str_1093_);
lean_ctor_set(v_reuseFailAlloc_1129_, 1, v_startPos_1094_);
lean_ctor_set(v_reuseFailAlloc_1129_, 2, v_stopPos_1095_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
v___y_1111_ = v___x_1128_;
goto v___jp_1110_;
}
}
}
}
else
{
uint8_t v___x_1133_; 
lean_del_object(v___x_1097_);
lean_dec(v_stopPos_1095_);
lean_dec(v_startPos_1094_);
lean_dec_ref(v_str_1093_);
v___x_1133_ = 0;
return v___x_1133_;
}
}
}
}
LEAN_EXPORT void l_Substring_Raw_isNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1092_ = stack[0].m_obj;
uint8_t v_res_1135_;
v_res_1135_ = l_Substring_Raw_isNat(v_s_1092_);
stack->m_num = v_res_1135_;
}
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___boxed(lean_object* v_s_1136_){
_start:
{
uint8_t v_res_1137_; lean_object* v_r_1138_; 
v_res_1137_ = l_Substring_Raw_isNat(v_s_1136_);
v_r_1138_ = lean_box(v_res_1137_);
return v_r_1138_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(lean_object* v___y_1139_, lean_object* v_a_1140_, lean_object* v_b_1141_){
_start:
{
lean_object* v_str_1142_; lean_object* v_startInclusive_1143_; lean_object* v_endExclusive_1144_; lean_object* v___x_1145_; uint8_t v_decide_1146_; 
v_str_1142_ = lean_ctor_get(v___y_1139_, 0);
v_startInclusive_1143_ = lean_ctor_get(v___y_1139_, 1);
v_endExclusive_1144_ = lean_ctor_get(v___y_1139_, 2);
v___x_1145_ = lean_nat_sub(v_endExclusive_1144_, v_startInclusive_1143_);
v_decide_1146_ = lean_nat_dec_eq(v_a_1140_, v___x_1145_);
lean_dec(v___x_1145_);
if (v_decide_1146_ == 0)
{
lean_object* v___x_1147_; uint32_t v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; uint32_t v___x_1151_; uint8_t v___x_1152_; 
v___x_1147_ = lean_nat_add(v_startInclusive_1143_, v_a_1140_);
lean_dec(v_a_1140_);
v___x_1148_ = lean_string_utf8_get_fast(v_str_1142_, v___x_1147_);
v___x_1149_ = lean_string_utf8_next_fast(v_str_1142_, v___x_1147_);
lean_dec(v___x_1147_);
v___x_1150_ = lean_nat_sub(v___x_1149_, v_startInclusive_1143_);
v___x_1151_ = 95;
v___x_1152_ = lean_uint32_dec_eq(v___x_1148_, v___x_1151_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1153_ = lean_unsigned_to_nat(10u);
v___x_1154_ = lean_nat_mul(v_b_1141_, v___x_1153_);
lean_dec(v_b_1141_);
v___x_1155_ = lean_uint32_to_nat(v___x_1148_);
v___x_1156_ = lean_unsigned_to_nat(48u);
v___x_1157_ = lean_nat_sub(v___x_1155_, v___x_1156_);
lean_dec(v___x_1155_);
v___x_1158_ = lean_nat_add(v___x_1154_, v___x_1157_);
lean_dec(v___x_1157_);
lean_dec(v___x_1154_);
v_a_1140_ = v___x_1150_;
v_b_1141_ = v___x_1158_;
goto _start;
}
else
{
v_a_1140_ = v___x_1150_;
goto _start;
}
}
else
{
lean_dec(v_a_1140_);
return v_b_1141_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg___boxed(lean_object* v___y_1161_, lean_object* v_a_1162_, lean_object* v_b_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(v___y_1161_, v_a_1162_, v_b_1163_);
lean_dec_ref(v___y_1161_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(lean_object* v___x_1165_, lean_object* v___y_1166_, lean_object* v_a_1167_, lean_object* v_b_1168_){
_start:
{
lean_object* v_str_1169_; lean_object* v_startInclusive_1170_; lean_object* v_endExclusive_1171_; lean_object* v___x_1172_; uint8_t v_decide_1173_; 
v_str_1169_ = lean_ctor_get(v___y_1166_, 0);
v_startInclusive_1170_ = lean_ctor_get(v___y_1166_, 1);
v_endExclusive_1171_ = lean_ctor_get(v___y_1166_, 2);
v___x_1172_ = lean_nat_sub(v_endExclusive_1171_, v_startInclusive_1170_);
v_decide_1173_ = lean_nat_dec_eq(v_a_1167_, v___x_1172_);
lean_dec(v___x_1172_);
if (v_decide_1173_ == 0)
{
lean_object* v_snd_1174_; lean_object* v_snd_1175_; lean_object* v_fst_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1239_; 
v_snd_1174_ = lean_ctor_get(v_b_1168_, 1);
lean_inc(v_snd_1174_);
v_snd_1175_ = lean_ctor_get(v_snd_1174_, 1);
lean_inc(v_snd_1175_);
v_fst_1176_ = lean_ctor_get(v_b_1168_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v_b_1168_);
if (v_isSharedCheck_1239_ == 0)
{
lean_object* v_unused_1240_; 
v_unused_1240_ = lean_ctor_get(v_b_1168_, 1);
lean_dec(v_unused_1240_);
v___x_1178_ = v_b_1168_;
v_isShared_1179_ = v_isSharedCheck_1239_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_fst_1176_);
lean_dec(v_b_1168_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1239_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v_fst_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1237_; 
v_fst_1180_ = lean_ctor_get(v_snd_1174_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_snd_1174_);
if (v_isSharedCheck_1237_ == 0)
{
lean_object* v_unused_1238_; 
v_unused_1238_ = lean_ctor_get(v_snd_1174_, 1);
lean_dec(v_unused_1238_);
v___x_1182_ = v_snd_1174_;
v_isShared_1183_ = v_isSharedCheck_1237_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_fst_1180_);
lean_dec(v_snd_1174_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1237_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v_snd_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1235_; 
v_snd_1184_ = lean_ctor_get(v_snd_1175_, 1);
v_isSharedCheck_1235_ = !lean_is_exclusive(v_snd_1175_);
if (v_isSharedCheck_1235_ == 0)
{
lean_object* v_unused_1236_; 
v_unused_1236_ = lean_ctor_get(v_snd_1175_, 0);
lean_dec(v_unused_1236_);
v___x_1186_ = v_snd_1175_;
v_isShared_1187_ = v_isSharedCheck_1235_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_snd_1184_);
lean_dec(v_snd_1175_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1235_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1188_; uint8_t v___x_1189_; uint8_t v___x_1190_; lean_object* v___x_1191_; uint32_t v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; uint8_t v___y_1196_; uint8_t v___y_1197_; uint8_t v___y_1215_; uint8_t v___y_1216_; uint8_t v___y_1221_; uint8_t v___y_1222_; uint8_t v___y_1227_; uint32_t v___x_1231_; uint8_t v___x_1232_; 
v___x_1188_ = lean_unsigned_to_nat(0u);
v___x_1189_ = lean_nat_dec_eq(v___x_1165_, v___x_1188_);
v___x_1190_ = 1;
v___x_1191_ = lean_nat_add(v_startInclusive_1170_, v_a_1167_);
lean_dec(v_a_1167_);
v___x_1192_ = lean_string_utf8_get_fast(v_str_1169_, v___x_1191_);
v___x_1193_ = lean_string_utf8_next_fast(v_str_1169_, v___x_1191_);
lean_dec(v___x_1191_);
v___x_1194_ = lean_nat_sub(v___x_1193_, v_startInclusive_1170_);
v___x_1231_ = 48;
v___x_1232_ = lean_uint32_dec_le(v___x_1231_, v___x_1192_);
if (v___x_1232_ == 0)
{
v___y_1227_ = v___x_1232_;
goto v___jp_1226_;
}
else
{
uint32_t v___x_1233_; uint8_t v___x_1234_; 
v___x_1233_ = 57;
v___x_1234_ = lean_uint32_dec_le(v___x_1192_, v___x_1233_);
v___y_1227_ = v___x_1234_;
goto v___jp_1226_;
}
v___jp_1195_:
{
uint32_t v___x_1198_; uint8_t v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1203_; 
v___x_1198_ = 95;
v___x_1199_ = lean_uint32_dec_eq(v___x_1192_, v___x_1198_);
v___x_1200_ = lean_box(v___y_1196_);
v___x_1201_ = lean_box(v___y_1197_);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 1, v___x_1201_);
lean_ctor_set(v___x_1186_, 0, v___x_1200_);
v___x_1203_ = v___x_1186_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1200_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v___x_1201_);
v___x_1203_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1204_ = lean_box(v___x_1199_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 1, v___x_1203_);
lean_ctor_set(v___x_1182_, 0, v___x_1204_);
v___x_1206_ = v___x_1182_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1204_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v___x_1203_);
v___x_1206_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
lean_object* v___x_1207_; lean_object* v___x_1209_; 
v___x_1207_ = lean_box(v___x_1189_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 1, v___x_1206_);
lean_ctor_set(v___x_1178_, 0, v___x_1207_);
v___x_1209_ = v___x_1178_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v___x_1206_);
v___x_1209_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
v_a_1167_ = v___x_1194_;
v_b_1168_ = v___x_1209_;
goto _start;
}
}
}
}
v___jp_1214_:
{
uint8_t v___x_1217_; 
v___x_1217_ = lean_unbox(v_fst_1180_);
lean_dec(v_fst_1180_);
if (v___x_1217_ == 0)
{
v___y_1196_ = v___y_1215_;
v___y_1197_ = v___y_1216_;
goto v___jp_1195_;
}
else
{
uint32_t v___x_1218_; uint8_t v___x_1219_; 
v___x_1218_ = 95;
v___x_1219_ = lean_uint32_dec_eq(v___x_1192_, v___x_1218_);
if (v___x_1219_ == 0)
{
v___y_1196_ = v___y_1215_;
v___y_1197_ = v___y_1216_;
goto v___jp_1195_;
}
else
{
v___y_1196_ = v___y_1215_;
v___y_1197_ = v___x_1189_;
goto v___jp_1195_;
}
}
}
v___jp_1220_:
{
uint8_t v___x_1223_; 
v___x_1223_ = lean_unbox(v_fst_1176_);
lean_dec(v_fst_1176_);
if (v___x_1223_ == 0)
{
v___y_1215_ = v___y_1221_;
v___y_1216_ = v___y_1222_;
goto v___jp_1214_;
}
else
{
uint32_t v___x_1224_; uint8_t v___x_1225_; 
v___x_1224_ = 95;
v___x_1225_ = lean_uint32_dec_eq(v___x_1192_, v___x_1224_);
if (v___x_1225_ == 0)
{
v___y_1215_ = v___y_1221_;
v___y_1216_ = v___y_1222_;
goto v___jp_1214_;
}
else
{
lean_dec(v_fst_1180_);
v___y_1196_ = v___y_1221_;
v___y_1197_ = v___x_1189_;
goto v___jp_1195_;
}
}
}
v___jp_1226_:
{
uint8_t v___x_1228_; 
v___x_1228_ = lean_unbox(v_snd_1184_);
lean_dec(v_snd_1184_);
if (v___x_1228_ == 0)
{
lean_dec(v_fst_1180_);
lean_dec(v_fst_1176_);
v___y_1196_ = v___y_1227_;
v___y_1197_ = v___x_1189_;
goto v___jp_1195_;
}
else
{
if (v___y_1227_ == 0)
{
uint32_t v___x_1229_; uint8_t v___x_1230_; 
v___x_1229_ = 95;
v___x_1230_ = lean_uint32_dec_eq(v___x_1192_, v___x_1229_);
if (v___x_1230_ == 0)
{
lean_dec(v_fst_1180_);
lean_dec(v_fst_1176_);
v___y_1196_ = v___y_1227_;
v___y_1197_ = v___x_1189_;
goto v___jp_1195_;
}
else
{
v___y_1221_ = v___y_1227_;
v___y_1222_ = v___x_1230_;
goto v___jp_1220_;
}
}
else
{
v___y_1221_ = v___y_1227_;
v___y_1222_ = v___x_1190_;
goto v___jp_1220_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1167_);
return v_b_1168_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg___boxed(lean_object* v___x_1241_, lean_object* v___y_1242_, lean_object* v_a_1243_, lean_object* v_b_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(v___x_1241_, v___y_1242_, v_a_1243_, v_b_1244_);
lean_dec_ref(v___y_1242_);
lean_dec(v___x_1241_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toNat_x3f(lean_object* v_s_1246_){
_start:
{
lean_object* v_str_1247_; lean_object* v_startPos_1248_; lean_object* v_stopPos_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1298_; 
v_str_1247_ = lean_ctor_get(v_s_1246_, 0);
v_startPos_1248_ = lean_ctor_get(v_s_1246_, 1);
v_stopPos_1249_ = lean_ctor_get(v_s_1246_, 2);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_s_1246_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1251_ = v_s_1246_;
v_isShared_1252_ = v_isSharedCheck_1298_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_stopPos_1249_);
lean_inc(v_startPos_1248_);
lean_inc(v_str_1247_);
lean_dec(v_s_1246_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1298_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___y_1256_; uint8_t v___y_1260_; uint8_t v___x_1266_; 
v___x_1253_ = lean_nat_sub(v_stopPos_1249_, v_startPos_1248_);
v___x_1254_ = lean_unsigned_to_nat(0u);
v___x_1266_ = lean_nat_dec_eq(v___x_1253_, v___x_1254_);
if (v___x_1266_ == 0)
{
uint8_t v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___y_1276_; uint8_t v___y_1290_; uint8_t v___x_1294_; 
v___x_1267_ = 1;
v___x_1268_ = lean_box(v___x_1266_);
v___x_1269_ = lean_box(v___x_1267_);
v___x_1270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1268_);
lean_ctor_set(v___x_1270_, 1, v___x_1269_);
v___x_1271_ = lean_box(v___x_1266_);
v___x_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
lean_ctor_set(v___x_1272_, 1, v___x_1270_);
v___x_1273_ = lean_box(v___x_1267_);
v___x_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1273_);
lean_ctor_set(v___x_1274_, 1, v___x_1272_);
v___x_1294_ = lean_string_is_valid_pos(v_str_1247_, v_startPos_1248_);
if (v___x_1294_ == 0)
{
v___y_1290_ = v___x_1294_;
goto v___jp_1289_;
}
else
{
uint8_t v___x_1295_; 
v___x_1295_ = lean_string_is_valid_pos(v_str_1247_, v_stopPos_1249_);
if (v___x_1295_ == 0)
{
v___y_1290_ = v___x_1295_;
goto v___jp_1289_;
}
else
{
uint8_t v___x_1296_; 
v___x_1296_ = lean_nat_dec_le(v_startPos_1248_, v_stopPos_1249_);
v___y_1290_ = v___x_1296_;
goto v___jp_1289_;
}
}
v___jp_1275_:
{
lean_object* v___x_1277_; lean_object* v_snd_1278_; lean_object* v_snd_1279_; lean_object* v_snd_1280_; uint8_t v___x_1281_; 
v___x_1277_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(v___x_1253_, v___y_1276_, v___x_1254_, v___x_1274_);
lean_dec_ref(v___y_1276_);
lean_dec(v___x_1253_);
v_snd_1278_ = lean_ctor_get(v___x_1277_, 1);
lean_inc(v_snd_1278_);
lean_dec_ref(v___x_1277_);
v_snd_1279_ = lean_ctor_get(v_snd_1278_, 1);
lean_inc(v_snd_1279_);
lean_dec(v_snd_1278_);
v_snd_1280_ = lean_ctor_get(v_snd_1279_, 1);
v___x_1281_ = lean_unbox(v_snd_1280_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; 
lean_dec(v_snd_1279_);
lean_del_object(v___x_1251_);
lean_dec(v_stopPos_1249_);
lean_dec(v_startPos_1248_);
lean_dec_ref(v_str_1247_);
v___x_1282_ = lean_box(0);
return v___x_1282_;
}
else
{
lean_object* v_fst_1283_; uint8_t v___x_1284_; 
v_fst_1283_ = lean_ctor_get(v_snd_1279_, 0);
lean_inc(v_fst_1283_);
lean_dec(v_snd_1279_);
v___x_1284_ = lean_unbox(v_fst_1283_);
lean_dec(v_fst_1283_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1285_; 
lean_del_object(v___x_1251_);
lean_dec(v_stopPos_1249_);
lean_dec(v_startPos_1248_);
lean_dec_ref(v_str_1247_);
v___x_1285_ = lean_box(0);
return v___x_1285_;
}
else
{
uint8_t v___x_1286_; 
v___x_1286_ = lean_string_is_valid_pos(v_str_1247_, v_startPos_1248_);
if (v___x_1286_ == 0)
{
v___y_1260_ = v___x_1286_;
goto v___jp_1259_;
}
else
{
uint8_t v___x_1287_; 
v___x_1287_ = lean_string_is_valid_pos(v_str_1247_, v_stopPos_1249_);
if (v___x_1287_ == 0)
{
v___y_1260_ = v___x_1287_;
goto v___jp_1259_;
}
else
{
uint8_t v___x_1288_; 
v___x_1288_ = lean_nat_dec_le(v_startPos_1248_, v_stopPos_1249_);
v___y_1260_ = v___x_1288_;
goto v___jp_1259_;
}
}
}
}
}
v___jp_1289_:
{
if (v___y_1290_ == 0)
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_1292_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_1291_);
v___y_1276_ = v___x_1292_;
goto v___jp_1275_;
}
else
{
lean_object* v___x_1293_; 
lean_inc(v_stopPos_1249_);
lean_inc(v_startPos_1248_);
lean_inc_ref(v_str_1247_);
v___x_1293_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1293_, 0, v_str_1247_);
lean_ctor_set(v___x_1293_, 1, v_startPos_1248_);
lean_ctor_set(v___x_1293_, 2, v_stopPos_1249_);
v___y_1276_ = v___x_1293_;
goto v___jp_1275_;
}
}
}
else
{
lean_object* v___x_1297_; 
lean_dec(v___x_1253_);
lean_del_object(v___x_1251_);
lean_dec(v_stopPos_1249_);
lean_dec(v_startPos_1248_);
lean_dec_ref(v_str_1247_);
v___x_1297_ = lean_box(0);
return v___x_1297_;
}
v___jp_1255_:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(v___y_1256_, v___x_1254_, v___x_1254_);
lean_dec_ref(v___y_1256_);
v___x_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
return v___x_1258_;
}
v___jp_1259_:
{
if (v___y_1260_ == 0)
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
lean_del_object(v___x_1251_);
lean_dec(v_stopPos_1249_);
lean_dec(v_startPos_1248_);
lean_dec_ref(v_str_1247_);
v___x_1261_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_1262_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_1261_);
v___y_1256_ = v___x_1262_;
goto v___jp_1255_;
}
else
{
lean_object* v___x_1264_; 
if (v_isShared_1252_ == 0)
{
v___x_1264_ = v___x_1251_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_str_1247_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v_startPos_1248_);
lean_ctor_set(v_reuseFailAlloc_1265_, 2, v_stopPos_1249_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
v___y_1256_ = v___x_1264_;
goto v___jp_1255_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0(lean_object* v___x_1299_, lean_object* v___y_1300_, lean_object* v_inst_1301_, lean_object* v_R_1302_, lean_object* v_a_1303_, lean_object* v_b_1304_, lean_object* v_c_1305_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(v___x_1299_, v___y_1300_, v_a_1303_, v_b_1304_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___boxed(lean_object* v___x_1307_, lean_object* v___y_1308_, lean_object* v_inst_1309_, lean_object* v_R_1310_, lean_object* v_a_1311_, lean_object* v_b_1312_, lean_object* v_c_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0(v___x_1307_, v___y_1308_, v_inst_1309_, v_R_1310_, v_a_1311_, v_b_1312_, v_c_1313_);
lean_dec_ref(v___y_1308_);
lean_dec(v___x_1307_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1(lean_object* v___y_1315_, lean_object* v_inst_1316_, lean_object* v_R_1317_, lean_object* v_a_1318_, lean_object* v_b_1319_, lean_object* v_c_1320_){
_start:
{
lean_object* v___x_1321_; 
v___x_1321_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(v___y_1315_, v_a_1318_, v_b_1319_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___boxed(lean_object* v___y_1322_, lean_object* v_inst_1323_, lean_object* v_R_1324_, lean_object* v_a_1325_, lean_object* v_b_1326_, lean_object* v_c_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1(v___y_1322_, v_inst_1323_, v_R_1324_, v_a_1325_, v_b_1326_, v_c_1327_);
lean_dec_ref(v___y_1322_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_repair(lean_object* v_x_1329_){
_start:
{
lean_object* v_str_1330_; lean_object* v_startPos_1331_; lean_object* v_stopPos_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1348_; 
v_str_1330_ = lean_ctor_get(v_x_1329_, 0);
v_startPos_1331_ = lean_ctor_get(v_x_1329_, 1);
v_stopPos_1332_ = lean_ctor_get(v_x_1329_, 2);
v_isSharedCheck_1348_ = !lean_is_exclusive(v_x_1329_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1334_ = v_x_1329_;
v_isShared_1335_ = v_isSharedCheck_1348_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_stopPos_1332_);
lean_inc(v_startPos_1331_);
lean_inc(v_str_1330_);
lean_dec(v_x_1329_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1348_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___y_1337_; uint8_t v___x_1346_; 
v___x_1346_ = lean_string_is_valid_pos(v_str_1330_, v_startPos_1331_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; 
lean_dec(v_startPos_1331_);
v___x_1347_ = lean_string_utf8_byte_size(v_str_1330_);
v___y_1337_ = v___x_1347_;
goto v___jp_1336_;
}
else
{
v___y_1337_ = v_startPos_1331_;
goto v___jp_1336_;
}
v___jp_1336_:
{
uint8_t v___x_1338_; 
v___x_1338_ = lean_string_is_valid_pos(v_str_1330_, v_stopPos_1332_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; lean_object* v___x_1341_; 
lean_dec(v_stopPos_1332_);
v___x_1339_ = lean_string_utf8_byte_size(v_str_1330_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 2, v___x_1339_);
lean_ctor_set(v___x_1334_, 1, v___y_1337_);
v___x_1341_ = v___x_1334_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_str_1330_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v___y_1337_);
lean_ctor_set(v_reuseFailAlloc_1342_, 2, v___x_1339_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
else
{
lean_object* v___x_1344_; 
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 1, v___y_1337_);
v___x_1344_ = v___x_1334_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_str_1330_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v___y_1337_);
lean_ctor_set(v_reuseFailAlloc_1345_, 2, v_stopPos_1332_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
}
}
uint8_t l_Substring_Raw_beq(lean_object* v_ss1_1349_, lean_object* v_ss2_1350_){
_start:
{
lean_object* v_ss1_1351_; lean_object* v_str_1352_; lean_object* v_startPos_1353_; lean_object* v_stopPos_1354_; lean_object* v_ss2_1355_; lean_object* v_str_1356_; lean_object* v_startPos_1357_; lean_object* v_stopPos_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; uint8_t v___x_1361_; 
v_ss1_1351_ = l_Substring_Raw_repair(v_ss1_1349_);
v_str_1352_ = lean_ctor_get(v_ss1_1351_, 0);
lean_inc_ref(v_str_1352_);
v_startPos_1353_ = lean_ctor_get(v_ss1_1351_, 1);
lean_inc(v_startPos_1353_);
v_stopPos_1354_ = lean_ctor_get(v_ss1_1351_, 2);
lean_inc(v_stopPos_1354_);
lean_dec_ref(v_ss1_1351_);
v_ss2_1355_ = l_Substring_Raw_repair(v_ss2_1350_);
v_str_1356_ = lean_ctor_get(v_ss2_1355_, 0);
lean_inc_ref(v_str_1356_);
v_startPos_1357_ = lean_ctor_get(v_ss2_1355_, 1);
lean_inc(v_startPos_1357_);
v_stopPos_1358_ = lean_ctor_get(v_ss2_1355_, 2);
lean_inc(v_stopPos_1358_);
lean_dec_ref(v_ss2_1355_);
v___x_1359_ = lean_nat_sub(v_stopPos_1354_, v_startPos_1353_);
lean_dec(v_stopPos_1354_);
v___x_1360_ = lean_nat_sub(v_stopPos_1358_, v_startPos_1357_);
lean_dec(v_stopPos_1358_);
v___x_1361_ = lean_nat_dec_eq(v___x_1359_, v___x_1360_);
lean_dec(v___x_1360_);
if (v___x_1361_ == 0)
{
lean_dec(v___x_1359_);
lean_dec(v_startPos_1357_);
lean_dec_ref(v_str_1356_);
lean_dec(v_startPos_1353_);
lean_dec_ref(v_str_1352_);
return v___x_1361_;
}
else
{
uint8_t v___x_1362_; 
v___x_1362_ = l_String_Pos_Raw_substrEq(v_str_1352_, v_startPos_1353_, v_str_1356_, v_startPos_1357_, v___x_1359_);
lean_dec(v___x_1359_);
lean_dec_ref(v_str_1356_);
lean_dec_ref(v_str_1352_);
return v___x_1362_;
}
}
}
LEAN_EXPORT void l_Substring_Raw_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_ss1_1349_ = stack[0].m_obj;
lean_object* v_ss2_1350_ = stack[1].m_obj;
uint8_t v_res_1363_;
v_res_1363_ = l_Substring_Raw_beq(v_ss1_1349_, v_ss2_1350_);
stack->m_num = v_res_1363_;
}
LEAN_EXPORT lean_object* l_Substring_Raw_beq___boxed(lean_object* v_ss1_1364_, lean_object* v_ss2_1365_){
_start:
{
uint8_t v_res_1366_; lean_object* v_r_1367_; 
v_res_1366_ = l_Substring_Raw_beq(v_ss1_1364_, v_ss2_1365_);
v_r_1367_ = lean_box(v_res_1366_);
return v_r_1367_;
}
}
uint8_t lean_substring_beq(lean_object* v_ss1_1368_, lean_object* v_ss2_1369_){
_start:
{
uint8_t v___x_1370_; 
v___x_1370_ = l_Substring_Raw_beq(v_ss1_1368_, v_ss2_1369_);
return v___x_1370_;
}
}
LEAN_EXPORT void lean_substring_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_ss1_1368_ = stack[0].m_obj;
lean_object* v_ss2_1369_ = stack[1].m_obj;
uint8_t v_res_1371_;
v_res_1371_ = lean_substring_beq(v_ss1_1368_, v_ss2_1369_);
stack->m_num = v_res_1371_;
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_beqImpl___boxed(lean_object* v_ss1_1372_, lean_object* v_ss2_1373_){
_start:
{
uint8_t v_res_1374_; lean_object* v_r_1375_; 
v_res_1374_ = lean_substring_beq(v_ss1_1372_, v_ss2_1373_);
v_r_1375_ = lean_box(v_res_1374_);
return v_r_1375_;
}
}
uint8_t l_Substring_Raw_sameAs(lean_object* v_ss1_1378_, lean_object* v_ss2_1379_){
_start:
{
lean_object* v_startPos_1380_; lean_object* v_startPos_1381_; uint8_t v_decide_1382_; 
v_startPos_1380_ = lean_ctor_get(v_ss1_1378_, 1);
v_startPos_1381_ = lean_ctor_get(v_ss2_1379_, 1);
v_decide_1382_ = lean_nat_dec_eq(v_startPos_1380_, v_startPos_1381_);
if (v_decide_1382_ == 0)
{
lean_dec_ref(v_ss2_1379_);
lean_dec_ref(v_ss1_1378_);
return v_decide_1382_;
}
else
{
uint8_t v___x_1383_; 
v___x_1383_ = l_Substring_Raw_beq(v_ss1_1378_, v_ss2_1379_);
return v___x_1383_;
}
}
}
LEAN_EXPORT void l_Substring_Raw_sameAs_0interp(lean_interpreter_value* stack)
{
lean_object* v_ss1_1378_ = stack[0].m_obj;
lean_object* v_ss2_1379_ = stack[1].m_obj;
uint8_t v_res_1384_;
v_res_1384_ = l_Substring_Raw_sameAs(v_ss1_1378_, v_ss2_1379_);
stack->m_num = v_res_1384_;
}
LEAN_EXPORT lean_object* l_Substring_Raw_sameAs___boxed(lean_object* v_ss1_1385_, lean_object* v_ss2_1386_){
_start:
{
uint8_t v_res_1387_; lean_object* v_r_1388_; 
v_res_1387_ = l_Substring_Raw_sameAs(v_ss1_1385_, v_ss2_1386_);
v_r_1388_ = lean_box(v_res_1387_);
return v_r_1388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(lean_object* v_s_1389_, lean_object* v_t_1390_, lean_object* v_spos_1391_, lean_object* v_tpos_1392_){
_start:
{
lean_object* v_str_1393_; lean_object* v_stopPos_1394_; uint8_t v___y_1396_; lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; 
v_str_1393_ = lean_ctor_get(v_s_1389_, 0);
v_stopPos_1394_ = lean_ctor_get(v_s_1389_, 2);
v___x_1404_ = lean_unsigned_to_nat(1u);
v___x_1405_ = lean_nat_add(v_spos_1391_, v___x_1404_);
v___x_1406_ = lean_nat_dec_le(v___x_1405_, v_stopPos_1394_);
lean_dec(v___x_1405_);
if (v___x_1406_ == 0)
{
v___y_1396_ = v___x_1406_;
goto v___jp_1395_;
}
else
{
lean_object* v_stopPos_1407_; lean_object* v___x_1408_; uint8_t v___x_1409_; 
v_stopPos_1407_ = lean_ctor_get(v_t_1390_, 2);
v___x_1408_ = lean_nat_add(v_tpos_1392_, v___x_1404_);
v___x_1409_ = lean_nat_dec_le(v___x_1408_, v_stopPos_1407_);
lean_dec(v___x_1408_);
v___y_1396_ = v___x_1409_;
goto v___jp_1395_;
}
v___jp_1395_:
{
if (v___y_1396_ == 0)
{
lean_dec(v_tpos_1392_);
return v_spos_1391_;
}
else
{
lean_object* v_str_1397_; uint32_t v___x_1398_; uint32_t v___x_1399_; uint8_t v___x_1400_; 
v_str_1397_ = lean_ctor_get(v_t_1390_, 0);
v___x_1398_ = lean_string_utf8_get(v_str_1393_, v_spos_1391_);
v___x_1399_ = lean_string_utf8_get(v_str_1397_, v_tpos_1392_);
v___x_1400_ = lean_uint32_dec_eq(v___x_1398_, v___x_1399_);
if (v___x_1400_ == 0)
{
lean_dec(v_tpos_1392_);
return v_spos_1391_;
}
else
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = lean_string_utf8_next(v_str_1393_, v_spos_1391_);
lean_dec(v_spos_1391_);
v___x_1402_ = lean_string_utf8_next(v_str_1397_, v_tpos_1392_);
lean_dec(v_tpos_1392_);
v_spos_1391_ = v___x_1401_;
v_tpos_1392_ = v___x_1402_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop___boxed(lean_object* v_s_1410_, lean_object* v_t_1411_, lean_object* v_spos_1412_, lean_object* v_tpos_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(v_s_1410_, v_t_1411_, v_spos_1412_, v_tpos_1413_);
lean_dec_ref(v_t_1411_);
lean_dec_ref(v_s_1410_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_commonPrefix(lean_object* v_s_1415_, lean_object* v_t_1416_){
_start:
{
lean_object* v_str_1417_; lean_object* v_startPos_1418_; lean_object* v_startPos_1419_; lean_object* v___x_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
v_str_1417_ = lean_ctor_get(v_s_1415_, 0);
lean_inc_ref(v_str_1417_);
v_startPos_1418_ = lean_ctor_get(v_s_1415_, 1);
lean_inc_n(v_startPos_1418_, 2);
v_startPos_1419_ = lean_ctor_get(v_t_1416_, 1);
lean_inc(v_startPos_1419_);
v___x_1420_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(v_s_1415_, v_t_1416_, v_startPos_1418_, v_startPos_1419_);
lean_dec_ref(v_s_1415_);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_t_1416_);
if (v_isSharedCheck_1427_ == 0)
{
lean_object* v_unused_1428_; lean_object* v_unused_1429_; lean_object* v_unused_1430_; 
v_unused_1428_ = lean_ctor_get(v_t_1416_, 2);
lean_dec(v_unused_1428_);
v_unused_1429_ = lean_ctor_get(v_t_1416_, 1);
lean_dec(v_unused_1429_);
v_unused_1430_ = lean_ctor_get(v_t_1416_, 0);
lean_dec(v_unused_1430_);
v___x_1422_ = v_t_1416_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_dec(v_t_1416_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 2, v___x_1420_);
lean_ctor_set(v___x_1422_, 1, v_startPos_1418_);
lean_ctor_set(v___x_1422_, 0, v_str_1417_);
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_str_1417_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_startPos_1418_);
lean_ctor_set(v_reuseFailAlloc_1426_, 2, v___x_1420_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(lean_object* v_s_1431_, lean_object* v_t_1432_, lean_object* v_spos_1433_, lean_object* v_tpos_1434_){
_start:
{
lean_object* v_str_1435_; lean_object* v_startPos_1436_; uint8_t v___y_1438_; lean_object* v___x_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; 
v_str_1435_ = lean_ctor_get(v_s_1431_, 0);
v_startPos_1436_ = lean_ctor_get(v_s_1431_, 1);
v___x_1446_ = lean_unsigned_to_nat(1u);
v___x_1447_ = lean_nat_add(v_startPos_1436_, v___x_1446_);
v___x_1448_ = lean_nat_dec_le(v___x_1447_, v_spos_1433_);
lean_dec(v___x_1447_);
if (v___x_1448_ == 0)
{
v___y_1438_ = v___x_1448_;
goto v___jp_1437_;
}
else
{
lean_object* v_startPos_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; 
v_startPos_1449_ = lean_ctor_get(v_t_1432_, 1);
v___x_1450_ = lean_nat_add(v_startPos_1449_, v___x_1446_);
v___x_1451_ = lean_nat_dec_le(v___x_1450_, v_tpos_1434_);
lean_dec(v___x_1450_);
v___y_1438_ = v___x_1451_;
goto v___jp_1437_;
}
v___jp_1437_:
{
if (v___y_1438_ == 0)
{
lean_dec(v_tpos_1434_);
return v_spos_1433_;
}
else
{
lean_object* v_str_1439_; lean_object* v_spos_x27_1440_; lean_object* v_tpos_x27_1441_; uint32_t v___x_1442_; uint32_t v___x_1443_; uint8_t v___x_1444_; 
v_str_1439_ = lean_ctor_get(v_t_1432_, 0);
v_spos_x27_1440_ = lean_string_utf8_prev(v_str_1435_, v_spos_1433_);
v_tpos_x27_1441_ = lean_string_utf8_prev(v_str_1439_, v_tpos_1434_);
lean_dec(v_tpos_1434_);
v___x_1442_ = lean_string_utf8_get(v_str_1435_, v_spos_x27_1440_);
v___x_1443_ = lean_string_utf8_get(v_str_1439_, v_tpos_x27_1441_);
v___x_1444_ = lean_uint32_dec_eq(v___x_1442_, v___x_1443_);
if (v___x_1444_ == 0)
{
lean_dec(v_tpos_x27_1441_);
lean_dec(v_spos_x27_1440_);
return v_spos_1433_;
}
else
{
lean_dec(v_spos_1433_);
v_spos_1433_ = v_spos_x27_1440_;
v_tpos_1434_ = v_tpos_x27_1441_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop___boxed(lean_object* v_s_1452_, lean_object* v_t_1453_, lean_object* v_spos_1454_, lean_object* v_tpos_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(v_s_1452_, v_t_1453_, v_spos_1454_, v_tpos_1455_);
lean_dec_ref(v_t_1453_);
lean_dec_ref(v_s_1452_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_commonSuffix(lean_object* v_s_1457_, lean_object* v_t_1458_){
_start:
{
lean_object* v_str_1459_; lean_object* v_stopPos_1460_; lean_object* v_stopPos_1461_; lean_object* v___x_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
v_str_1459_ = lean_ctor_get(v_s_1457_, 0);
lean_inc_ref(v_str_1459_);
v_stopPos_1460_ = lean_ctor_get(v_s_1457_, 2);
lean_inc_n(v_stopPos_1460_, 2);
v_stopPos_1461_ = lean_ctor_get(v_t_1458_, 2);
lean_inc(v_stopPos_1461_);
v___x_1462_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(v_s_1457_, v_t_1458_, v_stopPos_1460_, v_stopPos_1461_);
lean_dec_ref(v_s_1457_);
v_isSharedCheck_1469_ = !lean_is_exclusive(v_t_1458_);
if (v_isSharedCheck_1469_ == 0)
{
lean_object* v_unused_1470_; lean_object* v_unused_1471_; lean_object* v_unused_1472_; 
v_unused_1470_ = lean_ctor_get(v_t_1458_, 2);
lean_dec(v_unused_1470_);
v_unused_1471_ = lean_ctor_get(v_t_1458_, 1);
lean_dec(v_unused_1471_);
v_unused_1472_ = lean_ctor_get(v_t_1458_, 0);
lean_dec(v_unused_1472_);
v___x_1464_ = v_t_1458_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_dec(v_t_1458_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 2, v_stopPos_1460_);
lean_ctor_set(v___x_1464_, 1, v___x_1462_);
lean_ctor_set(v___x_1464_, 0, v_str_1459_);
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_str_1459_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v___x_1462_);
lean_ctor_set(v_reuseFailAlloc_1468_, 2, v_stopPos_1460_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropPrefix_x3f(lean_object* v_s_1473_, lean_object* v_pre_1474_){
_start:
{
lean_object* v_t_1475_; lean_object* v_startPos_1476_; lean_object* v_stopPos_1477_; lean_object* v_startPos_1478_; lean_object* v_stopPos_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; uint8_t v___x_1482_; 
lean_inc_ref(v_pre_1474_);
lean_inc_ref(v_s_1473_);
v_t_1475_ = l_Substring_Raw_commonPrefix(v_s_1473_, v_pre_1474_);
v_startPos_1476_ = lean_ctor_get(v_t_1475_, 1);
lean_inc(v_startPos_1476_);
v_stopPos_1477_ = lean_ctor_get(v_t_1475_, 2);
lean_inc(v_stopPos_1477_);
lean_dec_ref(v_t_1475_);
v_startPos_1478_ = lean_ctor_get(v_pre_1474_, 1);
lean_inc(v_startPos_1478_);
v_stopPos_1479_ = lean_ctor_get(v_pre_1474_, 2);
lean_inc(v_stopPos_1479_);
lean_dec_ref(v_pre_1474_);
v___x_1480_ = lean_nat_sub(v_stopPos_1477_, v_startPos_1476_);
lean_dec(v_startPos_1476_);
v___x_1481_ = lean_nat_sub(v_stopPos_1479_, v_startPos_1478_);
lean_dec(v_startPos_1478_);
lean_dec(v_stopPos_1479_);
v___x_1482_ = lean_nat_dec_eq(v___x_1480_, v___x_1481_);
lean_dec(v___x_1481_);
lean_dec(v___x_1480_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; 
lean_dec(v_stopPos_1477_);
lean_dec_ref(v_s_1473_);
v___x_1483_ = lean_box(0);
return v___x_1483_;
}
else
{
lean_object* v_str_1484_; lean_object* v_stopPos_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1493_; 
v_str_1484_ = lean_ctor_get(v_s_1473_, 0);
v_stopPos_1485_ = lean_ctor_get(v_s_1473_, 2);
v_isSharedCheck_1493_ = !lean_is_exclusive(v_s_1473_);
if (v_isSharedCheck_1493_ == 0)
{
lean_object* v_unused_1494_; 
v_unused_1494_ = lean_ctor_get(v_s_1473_, 1);
lean_dec(v_unused_1494_);
v___x_1487_ = v_s_1473_;
v_isShared_1488_ = v_isSharedCheck_1493_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_stopPos_1485_);
lean_inc(v_str_1484_);
lean_dec(v_s_1473_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1493_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 1, v_stopPos_1477_);
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_str_1484_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v_stopPos_1477_);
lean_ctor_set(v_reuseFailAlloc_1492_, 2, v_stopPos_1485_);
v___x_1490_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
lean_object* v___x_1491_; 
v___x_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1490_);
return v___x_1491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropSuffix_x3f(lean_object* v_s_1495_, lean_object* v_suff_1496_){
_start:
{
lean_object* v_t_1497_; lean_object* v_startPos_1498_; lean_object* v_stopPos_1499_; lean_object* v_startPos_1500_; lean_object* v_stopPos_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; uint8_t v___x_1504_; 
lean_inc_ref(v_suff_1496_);
lean_inc_ref(v_s_1495_);
v_t_1497_ = l_Substring_Raw_commonSuffix(v_s_1495_, v_suff_1496_);
v_startPos_1498_ = lean_ctor_get(v_t_1497_, 1);
lean_inc(v_startPos_1498_);
v_stopPos_1499_ = lean_ctor_get(v_t_1497_, 2);
lean_inc(v_stopPos_1499_);
lean_dec_ref(v_t_1497_);
v_startPos_1500_ = lean_ctor_get(v_suff_1496_, 1);
lean_inc(v_startPos_1500_);
v_stopPos_1501_ = lean_ctor_get(v_suff_1496_, 2);
lean_inc(v_stopPos_1501_);
lean_dec_ref(v_suff_1496_);
v___x_1502_ = lean_nat_sub(v_stopPos_1499_, v_startPos_1498_);
lean_dec(v_stopPos_1499_);
v___x_1503_ = lean_nat_sub(v_stopPos_1501_, v_startPos_1500_);
lean_dec(v_startPos_1500_);
lean_dec(v_stopPos_1501_);
v___x_1504_ = lean_nat_dec_eq(v___x_1502_, v___x_1503_);
lean_dec(v___x_1503_);
lean_dec(v___x_1502_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; 
lean_dec(v_startPos_1498_);
lean_dec_ref(v_s_1495_);
v___x_1505_ = lean_box(0);
return v___x_1505_;
}
else
{
lean_object* v_str_1506_; lean_object* v_startPos_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1515_; 
v_str_1506_ = lean_ctor_get(v_s_1495_, 0);
v_startPos_1507_ = lean_ctor_get(v_s_1495_, 1);
v_isSharedCheck_1515_ = !lean_is_exclusive(v_s_1495_);
if (v_isSharedCheck_1515_ == 0)
{
lean_object* v_unused_1516_; 
v_unused_1516_ = lean_ctor_get(v_s_1495_, 2);
lean_dec(v_unused_1516_);
v___x_1509_ = v_s_1495_;
v_isShared_1510_ = v_isSharedCheck_1515_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_startPos_1507_);
lean_inc(v_str_1506_);
lean_dec(v_s_1495_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1515_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1512_; 
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 2, v_startPos_1498_);
v___x_1512_ = v___x_1509_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_str_1506_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_startPos_1507_);
lean_ctor_set(v_reuseFailAlloc_1514_, 2, v_startPos_1498_);
v___x_1512_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1513_; 
v___x_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
return v___x_1513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_bsize(lean_object* v_a_1517_){
_start:
{
lean_object* v_startPos_1518_; lean_object* v_stopPos_1519_; lean_object* v___x_1520_; 
v_startPos_1518_ = lean_ctor_get(v_a_1517_, 1);
v_stopPos_1519_ = lean_ctor_get(v_a_1517_, 2);
v___x_1520_ = lean_nat_sub(v_stopPos_1519_, v_startPos_1518_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Substring_bsize___boxed(lean_object* v_a_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Substring_bsize(v_a_1521_);
lean_dec_ref(v_a_1521_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Substring_toString(lean_object* v_a_1523_){
_start:
{
lean_object* v_str_1524_; lean_object* v_startPos_1525_; lean_object* v_stopPos_1526_; lean_object* v___x_1527_; 
v_str_1524_ = lean_ctor_get(v_a_1523_, 0);
v_startPos_1525_ = lean_ctor_get(v_a_1523_, 1);
v_stopPos_1526_ = lean_ctor_get(v_a_1523_, 2);
v___x_1527_ = lean_string_utf8_extract(v_str_1524_, v_startPos_1525_, v_stopPos_1526_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l_Substring_toString___boxed(lean_object* v_a_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_Substring_toString(v_a_1528_);
lean_dec_ref(v_a_1528_);
return v_res_1529_;
}
}
uint8_t l_Substring_isEmpty(lean_object* v_ss_1530_){
_start:
{
lean_object* v_startPos_1531_; lean_object* v_stopPos_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; uint8_t v___x_1535_; 
v_startPos_1531_ = lean_ctor_get(v_ss_1530_, 1);
v_stopPos_1532_ = lean_ctor_get(v_ss_1530_, 2);
v___x_1533_ = lean_nat_sub(v_stopPos_1532_, v_startPos_1531_);
v___x_1534_ = lean_unsigned_to_nat(0u);
v___x_1535_ = lean_nat_dec_eq(v___x_1533_, v___x_1534_);
lean_dec(v___x_1533_);
return v___x_1535_;
}
}
LEAN_EXPORT void l_Substring_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_ss_1530_ = stack[0].m_obj;
uint8_t v_res_1536_;
v_res_1536_ = l_Substring_isEmpty(v_ss_1530_);
stack->m_num = v_res_1536_;
}
LEAN_EXPORT lean_object* l_Substring_isEmpty___boxed(lean_object* v_ss_1537_){
_start:
{
uint8_t v_res_1538_; lean_object* v_r_1539_; 
v_res_1538_ = l_Substring_isEmpty(v_ss_1537_);
lean_dec_ref(v_ss_1537_);
v_r_1539_ = lean_box(v_res_1538_);
return v_r_1539_;
}
}
LEAN_EXPORT lean_object* l_Substring_next(lean_object* v_a_1540_, lean_object* v_a_1541_){
_start:
{
lean_object* v_str_1542_; lean_object* v_startPos_1543_; lean_object* v_stopPos_1544_; lean_object* v_absP_1545_; uint8_t v_decide_1546_; 
v_str_1542_ = lean_ctor_get(v_a_1540_, 0);
v_startPos_1543_ = lean_ctor_get(v_a_1540_, 1);
v_stopPos_1544_ = lean_ctor_get(v_a_1540_, 2);
v_absP_1545_ = lean_nat_add(v_startPos_1543_, v_a_1541_);
v_decide_1546_ = lean_nat_dec_eq(v_absP_1545_, v_stopPos_1544_);
if (v_decide_1546_ == 0)
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1547_ = lean_string_utf8_next(v_str_1542_, v_absP_1545_);
lean_dec(v_absP_1545_);
v___x_1548_ = lean_nat_sub(v___x_1547_, v_startPos_1543_);
lean_dec(v___x_1547_);
return v___x_1548_;
}
else
{
lean_dec(v_absP_1545_);
lean_inc(v_a_1541_);
return v_a_1541_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_next___boxed(lean_object* v_a_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Substring_next(v_a_1549_, v_a_1550_);
lean_dec(v_a_1550_);
lean_dec_ref(v_a_1549_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Substring_prev(lean_object* v_a_1552_, lean_object* v_a_1553_){
_start:
{
lean_object* v_str_1554_; lean_object* v_startPos_1555_; lean_object* v_absP_1556_; uint8_t v_decide_1557_; 
v_str_1554_ = lean_ctor_get(v_a_1552_, 0);
v_startPos_1555_ = lean_ctor_get(v_a_1552_, 1);
v_absP_1556_ = lean_nat_add(v_startPos_1555_, v_a_1553_);
v_decide_1557_ = lean_nat_dec_eq(v_absP_1556_, v_startPos_1555_);
if (v_decide_1557_ == 0)
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = lean_string_utf8_prev(v_str_1554_, v_absP_1556_);
lean_dec(v_absP_1556_);
v___x_1559_ = lean_nat_sub(v___x_1558_, v_startPos_1555_);
lean_dec(v___x_1558_);
return v___x_1559_;
}
else
{
lean_dec(v_absP_1556_);
lean_inc(v_a_1553_);
return v_a_1553_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_prev___boxed(lean_object* v_a_1560_, lean_object* v_a_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l_Substring_prev(v_a_1560_, v_a_1561_);
lean_dec(v_a_1561_);
lean_dec_ref(v_a_1560_);
return v_res_1562_;
}
}
uint8_t l_Substring_atEnd(lean_object* v_a_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v_startPos_1565_; lean_object* v_stopPos_1566_; lean_object* v___x_1567_; uint8_t v_decide_1568_; 
v_startPos_1565_ = lean_ctor_get(v_a_1563_, 1);
v_stopPos_1566_ = lean_ctor_get(v_a_1563_, 2);
v___x_1567_ = lean_nat_add(v_startPos_1565_, v_a_1564_);
v_decide_1568_ = lean_nat_dec_eq(v___x_1567_, v_stopPos_1566_);
lean_dec(v___x_1567_);
return v_decide_1568_;
}
}
LEAN_EXPORT void l_Substring_atEnd_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1563_ = stack[0].m_obj;
lean_object* v_a_1564_ = stack[1].m_obj;
uint8_t v_res_1569_;
v_res_1569_ = l_Substring_atEnd(v_a_1563_, v_a_1564_);
stack->m_num = v_res_1569_;
}
LEAN_EXPORT lean_object* l_Substring_atEnd___boxed(lean_object* v_a_1570_, lean_object* v_a_1571_){
_start:
{
uint8_t v_res_1572_; lean_object* v_r_1573_; 
v_res_1572_ = l_Substring_atEnd(v_a_1570_, v_a_1571_);
lean_dec(v_a_1571_);
lean_dec_ref(v_a_1570_);
v_r_1573_ = lean_box(v_res_1572_);
return v_r_1573_;
}
}
uint8_t l_Substring_beq(lean_object* v_ss1_1574_, lean_object* v_ss2_1575_){
_start:
{
uint8_t v___x_1576_; 
v___x_1576_ = l_Substring_Raw_beq(v_ss1_1574_, v_ss2_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT void l_Substring_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_ss1_1574_ = stack[0].m_obj;
lean_object* v_ss2_1575_ = stack[1].m_obj;
uint8_t v_res_1577_;
v_res_1577_ = l_Substring_beq(v_ss1_1574_, v_ss2_1575_);
stack->m_num = v_res_1577_;
}
LEAN_EXPORT lean_object* l_Substring_beq___boxed(lean_object* v_ss1_1578_, lean_object* v_ss2_1579_){
_start:
{
uint8_t v_res_1580_; lean_object* v_r_1581_; 
v_res_1580_ = l_Substring_beq(v_ss1_1578_, v_ss2_1579_);
v_r_1581_ = lean_box(v_res_1580_);
return v_r_1581_;
}
}
lean_object* runtime_initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_BasicAux(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Substring(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Substring(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* initialize_Init_Data_Option_BasicAux(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Substring(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Substring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Substring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Substring(builtin);
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Init.Data.String.Substring
// Imports: public import Init.Data.String.Slice.Pattern public import Init.Data.String.Iterate import Init.Data.Option.BasicAux
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
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
uint8_t v___x_19_; 
v___x_19_ = lean_string_is_valid_pos(v_str_13_, v_startPos_14_);
if (v___x_19_ == 0)
{
lean_object* v___x_20_; 
lean_del_object(v___x_17_);
lean_dec(v_stopPos_15_);
lean_dec(v_startPos_14_);
lean_dec_ref(v_str_13_);
v___x_20_ = lean_box(0);
return v___x_20_;
}
else
{
uint8_t v___x_21_; 
v___x_21_ = lean_string_is_valid_pos(v_str_13_, v_stopPos_15_);
if (v___x_21_ == 0)
{
lean_object* v___x_22_; 
lean_del_object(v___x_17_);
lean_dec(v_stopPos_15_);
lean_dec(v_startPos_14_);
lean_dec_ref(v_str_13_);
v___x_22_ = lean_box(0);
return v___x_22_;
}
else
{
uint8_t v___x_23_; 
v___x_23_ = lean_nat_dec_le(v_startPos_14_, v_stopPos_15_);
if (v___x_23_ == 0)
{
lean_object* v___x_24_; 
lean_del_object(v___x_17_);
lean_dec(v_stopPos_15_);
lean_dec(v_startPos_14_);
lean_dec_ref(v_str_13_);
v___x_24_ = lean_box(0);
return v___x_24_;
}
else
{
lean_object* v___x_26_; 
if (v_isShared_18_ == 0)
{
v___x_26_ = v___x_17_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_str_13_);
lean_ctor_set(v_reuseFailAlloc_28_, 1, v_startPos_14_);
lean_ctor_set(v_reuseFailAlloc_28_, 2, v_stopPos_15_);
v___x_26_ = v_reuseFailAlloc_28_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
lean_object* v___x_27_; 
v___x_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
return v___x_27_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_isEmpty(lean_object* v_ss_30_){
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
LEAN_EXPORT lean_object* l_Substring_Raw_isEmpty___boxed(lean_object* v_ss_36_){
_start:
{
uint8_t v_res_37_; lean_object* v_r_38_; 
v_res_37_ = l_Substring_Raw_isEmpty(v_ss_36_);
lean_dec_ref(v_ss_36_);
v_r_38_ = lean_box(v_res_37_);
return v_r_38_;
}
}
LEAN_EXPORT uint8_t lean_substring_isempty(lean_object* v_ss_39_){
_start:
{
lean_object* v_startPos_40_; lean_object* v_stopPos_41_; lean_object* v___x_42_; lean_object* v___x_43_; uint8_t v___x_44_; 
v_startPos_40_ = lean_ctor_get(v_ss_39_, 1);
lean_inc(v_startPos_40_);
v_stopPos_41_ = lean_ctor_get(v_ss_39_, 2);
lean_inc(v_stopPos_41_);
lean_dec_ref(v_ss_39_);
v___x_42_ = lean_nat_sub(v_stopPos_41_, v_startPos_40_);
lean_dec(v_startPos_40_);
lean_dec(v_stopPos_41_);
v___x_43_ = lean_unsigned_to_nat(0u);
v___x_44_ = lean_nat_dec_eq(v___x_42_, v___x_43_);
lean_dec(v___x_42_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_isEmptyImpl___boxed(lean_object* v_ss_45_){
_start:
{
uint8_t v_res_46_; lean_object* v_r_47_; 
v_res_46_ = lean_substring_isempty(v_ss_45_);
v_r_47_ = lean_box(v_res_46_);
return v_r_47_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toString(lean_object* v_x_48_){
_start:
{
lean_object* v_str_49_; lean_object* v_startPos_50_; lean_object* v_stopPos_51_; lean_object* v___x_52_; 
v_str_49_ = lean_ctor_get(v_x_48_, 0);
v_startPos_50_ = lean_ctor_get(v_x_48_, 1);
v_stopPos_51_ = lean_ctor_get(v_x_48_, 2);
v___x_52_ = lean_string_utf8_extract(v_str_49_, v_startPos_50_, v_stopPos_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toString___boxed(lean_object* v_x_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Substring_Raw_toString(v_x_53_);
lean_dec_ref(v_x_53_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* lean_substring_tostring(lean_object* v_a_55_){
_start:
{
lean_object* v_str_56_; lean_object* v_startPos_57_; lean_object* v_stopPos_58_; lean_object* v___x_59_; 
v_str_56_ = lean_ctor_get(v_a_55_, 0);
lean_inc_ref(v_str_56_);
v_startPos_57_ = lean_ctor_get(v_a_55_, 1);
lean_inc(v_startPos_57_);
v_stopPos_58_ = lean_ctor_get(v_a_55_, 2);
lean_inc(v_stopPos_58_);
lean_dec_ref(v_a_55_);
v___x_59_ = lean_string_utf8_extract(v_str_56_, v_startPos_57_, v_stopPos_58_);
lean_dec(v_stopPos_58_);
lean_dec(v_startPos_57_);
lean_dec_ref(v_str_56_);
return v___x_59_;
}
}
LEAN_EXPORT uint32_t l_Substring_Raw_get(lean_object* v_x_60_, lean_object* v_x_61_){
_start:
{
lean_object* v_str_62_; lean_object* v_startPos_63_; lean_object* v___x_64_; uint32_t v___x_65_; 
v_str_62_ = lean_ctor_get(v_x_60_, 0);
v_startPos_63_ = lean_ctor_get(v_x_60_, 1);
v___x_64_ = lean_nat_add(v_startPos_63_, v_x_61_);
v___x_65_ = lean_string_utf8_get(v_str_62_, v___x_64_);
lean_dec(v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_get___boxed(lean_object* v_x_66_, lean_object* v_x_67_){
_start:
{
uint32_t v_res_68_; lean_object* v_r_69_; 
v_res_68_ = l_Substring_Raw_get(v_x_66_, v_x_67_);
lean_dec(v_x_67_);
lean_dec_ref(v_x_66_);
v_r_69_ = lean_box_uint32(v_res_68_);
return v_r_69_;
}
}
LEAN_EXPORT uint32_t lean_substring_get(lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
lean_object* v_str_72_; lean_object* v_startPos_73_; lean_object* v___x_74_; uint32_t v___x_75_; 
v_str_72_ = lean_ctor_get(v_a_70_, 0);
lean_inc_ref(v_str_72_);
v_startPos_73_ = lean_ctor_get(v_a_70_, 1);
lean_inc(v_startPos_73_);
lean_dec_ref(v_a_70_);
v___x_74_ = lean_nat_add(v_startPos_73_, v_a_71_);
lean_dec(v_a_71_);
lean_dec(v_startPos_73_);
v___x_75_ = lean_string_utf8_get(v_str_72_, v___x_74_);
lean_dec(v___x_74_);
lean_dec_ref(v_str_72_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_getImpl___boxed(lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
uint32_t v_res_78_; lean_object* v_r_79_; 
v_res_78_ = lean_substring_get(v_a_76_, v_a_77_);
v_r_79_ = lean_box_uint32(v_res_78_);
return v_r_79_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_next(lean_object* v_x_80_, lean_object* v_x_81_){
_start:
{
lean_object* v_str_82_; lean_object* v_startPos_83_; lean_object* v_stopPos_84_; lean_object* v_absP_85_; uint8_t v_decide_86_; 
v_str_82_ = lean_ctor_get(v_x_80_, 0);
v_startPos_83_ = lean_ctor_get(v_x_80_, 1);
v_stopPos_84_ = lean_ctor_get(v_x_80_, 2);
v_absP_85_ = lean_nat_add(v_startPos_83_, v_x_81_);
v_decide_86_ = lean_nat_dec_eq(v_absP_85_, v_stopPos_84_);
if (v_decide_86_ == 0)
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_string_utf8_next(v_str_82_, v_absP_85_);
lean_dec(v_absP_85_);
v___x_88_ = lean_nat_sub(v___x_87_, v_startPos_83_);
lean_dec(v___x_87_);
return v___x_88_;
}
else
{
lean_dec(v_absP_85_);
lean_inc(v_x_81_);
return v_x_81_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_next___boxed(lean_object* v_x_89_, lean_object* v_x_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Substring_Raw_next(v_x_89_, v_x_90_);
lean_dec(v_x_90_);
lean_dec_ref(v_x_89_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_prev(lean_object* v_x_92_, lean_object* v_x_93_){
_start:
{
lean_object* v_str_94_; lean_object* v_startPos_95_; lean_object* v_absP_96_; uint8_t v_decide_97_; 
v_str_94_ = lean_ctor_get(v_x_92_, 0);
v_startPos_95_ = lean_ctor_get(v_x_92_, 1);
v_absP_96_ = lean_nat_add(v_startPos_95_, v_x_93_);
v_decide_97_ = lean_nat_dec_eq(v_absP_96_, v_startPos_95_);
if (v_decide_97_ == 0)
{
lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_98_ = lean_string_utf8_prev(v_str_94_, v_absP_96_);
lean_dec(v_absP_96_);
v___x_99_ = lean_nat_sub(v___x_98_, v_startPos_95_);
lean_dec(v___x_98_);
return v___x_99_;
}
else
{
lean_dec(v_absP_96_);
lean_inc(v_x_93_);
return v_x_93_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_prev___boxed(lean_object* v_x_100_, lean_object* v_x_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Substring_Raw_prev(v_x_100_, v_x_101_);
lean_dec(v_x_101_);
lean_dec_ref(v_x_100_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* lean_substring_prev(lean_object* v_a_103_, lean_object* v_a_104_){
_start:
{
lean_object* v_str_105_; lean_object* v_startPos_106_; lean_object* v_absP_107_; uint8_t v_decide_108_; 
v_str_105_ = lean_ctor_get(v_a_103_, 0);
lean_inc_ref(v_str_105_);
v_startPos_106_ = lean_ctor_get(v_a_103_, 1);
lean_inc(v_startPos_106_);
lean_dec_ref(v_a_103_);
v_absP_107_ = lean_nat_add(v_startPos_106_, v_a_104_);
v_decide_108_ = lean_nat_dec_eq(v_absP_107_, v_startPos_106_);
if (v_decide_108_ == 0)
{
lean_object* v___x_109_; lean_object* v___x_110_; 
lean_dec(v_a_104_);
v___x_109_ = lean_string_utf8_prev(v_str_105_, v_absP_107_);
lean_dec(v_absP_107_);
lean_dec_ref(v_str_105_);
v___x_110_ = lean_nat_sub(v___x_109_, v_startPos_106_);
lean_dec(v_startPos_106_);
lean_dec(v___x_109_);
return v___x_110_;
}
else
{
lean_dec(v_absP_107_);
lean_dec(v_startPos_106_);
lean_dec_ref(v_str_105_);
return v_a_104_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_nextn(lean_object* v_x_111_, lean_object* v_x_112_, lean_object* v_x_113_){
_start:
{
lean_object* v_zero_114_; uint8_t v_isZero_115_; 
v_zero_114_ = lean_unsigned_to_nat(0u);
v_isZero_115_ = lean_nat_dec_eq(v_x_112_, v_zero_114_);
if (v_isZero_115_ == 1)
{
lean_dec(v_x_112_);
return v_x_113_;
}
else
{
lean_object* v_str_116_; lean_object* v_startPos_117_; lean_object* v_stopPos_118_; lean_object* v_one_119_; lean_object* v_n_120_; lean_object* v_absP_121_; uint8_t v_decide_122_; 
v_str_116_ = lean_ctor_get(v_x_111_, 0);
v_startPos_117_ = lean_ctor_get(v_x_111_, 1);
v_stopPos_118_ = lean_ctor_get(v_x_111_, 2);
v_one_119_ = lean_unsigned_to_nat(1u);
v_n_120_ = lean_nat_sub(v_x_112_, v_one_119_);
lean_dec(v_x_112_);
v_absP_121_ = lean_nat_add(v_startPos_117_, v_x_113_);
v_decide_122_ = lean_nat_dec_eq(v_absP_121_, v_stopPos_118_);
if (v_decide_122_ == 0)
{
lean_object* v___x_123_; lean_object* v___x_124_; 
lean_dec(v_x_113_);
v___x_123_ = lean_string_utf8_next(v_str_116_, v_absP_121_);
lean_dec(v_absP_121_);
v___x_124_ = lean_nat_sub(v___x_123_, v_startPos_117_);
lean_dec(v___x_123_);
v_x_112_ = v_n_120_;
v_x_113_ = v___x_124_;
goto _start;
}
else
{
lean_dec(v_absP_121_);
v_x_112_ = v_n_120_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_nextn___boxed(lean_object* v_x_127_, lean_object* v_x_128_, lean_object* v_x_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Substring_Raw_nextn(v_x_127_, v_x_128_, v_x_129_);
lean_dec_ref(v_x_127_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_prevn(lean_object* v_x_131_, lean_object* v_x_132_, lean_object* v_x_133_){
_start:
{
lean_object* v_zero_134_; uint8_t v_isZero_135_; 
v_zero_134_ = lean_unsigned_to_nat(0u);
v_isZero_135_ = lean_nat_dec_eq(v_x_132_, v_zero_134_);
if (v_isZero_135_ == 1)
{
lean_dec(v_x_132_);
return v_x_133_;
}
else
{
lean_object* v_str_136_; lean_object* v_startPos_137_; lean_object* v_one_138_; lean_object* v_n_139_; lean_object* v_absP_140_; uint8_t v_decide_141_; 
v_str_136_ = lean_ctor_get(v_x_131_, 0);
v_startPos_137_ = lean_ctor_get(v_x_131_, 1);
v_one_138_ = lean_unsigned_to_nat(1u);
v_n_139_ = lean_nat_sub(v_x_132_, v_one_138_);
lean_dec(v_x_132_);
v_absP_140_ = lean_nat_add(v_startPos_137_, v_x_133_);
v_decide_141_ = lean_nat_dec_eq(v_absP_140_, v_startPos_137_);
if (v_decide_141_ == 0)
{
lean_object* v___x_142_; lean_object* v___x_143_; 
lean_dec(v_x_133_);
v___x_142_ = lean_string_utf8_prev(v_str_136_, v_absP_140_);
lean_dec(v_absP_140_);
v___x_143_ = lean_nat_sub(v___x_142_, v_startPos_137_);
lean_dec(v___x_142_);
v_x_132_ = v_n_139_;
v_x_133_ = v___x_143_;
goto _start;
}
else
{
lean_dec(v_absP_140_);
v_x_132_ = v_n_139_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_prevn___boxed(lean_object* v_x_146_, lean_object* v_x_147_, lean_object* v_x_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Substring_Raw_prevn(v_x_146_, v_x_147_, v_x_148_);
lean_dec_ref(v_x_146_);
return v_res_149_;
}
}
LEAN_EXPORT uint32_t l_Substring_Raw_front(lean_object* v_s_150_){
_start:
{
lean_object* v_str_151_; lean_object* v_startPos_152_; uint32_t v___x_153_; 
v_str_151_ = lean_ctor_get(v_s_150_, 0);
v_startPos_152_ = lean_ctor_get(v_s_150_, 1);
v___x_153_ = lean_string_utf8_get(v_str_151_, v_startPos_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_front___boxed(lean_object* v_s_154_){
_start:
{
uint32_t v_res_155_; lean_object* v_r_156_; 
v_res_155_ = l_Substring_Raw_front(v_s_154_);
lean_dec_ref(v_s_154_);
v_r_156_ = lean_box_uint32(v_res_155_);
return v_r_156_;
}
}
LEAN_EXPORT uint32_t lean_substring_front(lean_object* v_s_157_){
_start:
{
lean_object* v_str_158_; lean_object* v_startPos_159_; uint32_t v___x_160_; 
v_str_158_ = lean_ctor_get(v_s_157_, 0);
lean_inc_ref(v_str_158_);
v_startPos_159_ = lean_ctor_get(v_s_157_, 1);
lean_inc(v_startPos_159_);
lean_dec_ref(v_s_157_);
v___x_160_ = lean_string_utf8_get(v_str_158_, v_startPos_159_);
lean_dec(v_startPos_159_);
lean_dec_ref(v_str_158_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_frontImpl___boxed(lean_object* v_s_161_){
_start:
{
uint32_t v_res_162_; lean_object* v_r_163_; 
v_res_162_ = lean_substring_front(v_s_161_);
v_r_163_ = lean_box_uint32(v_res_162_);
return v_r_163_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_posOf___lam__0(lean_object* v_stopPos_164_, lean_object* v_startPos_165_, lean_object* v_str_166_, uint32_t v_c_167_, lean_object* v___x_168_, lean_object* v_it_169_, lean_object* v_acc_170_, lean_object* v_hP_171_, lean_object* v_recur_172_){
_start:
{
lean_object* v___x_173_; uint8_t v_decide_174_; 
v___x_173_ = lean_nat_sub(v_stopPos_164_, v_startPos_165_);
v_decide_174_ = lean_nat_dec_eq(v_it_169_, v___x_173_);
lean_dec(v___x_173_);
if (v_decide_174_ == 0)
{
lean_object* v___x_175_; uint32_t v___x_176_; uint8_t v___x_177_; 
v___x_175_ = lean_nat_add(v_startPos_165_, v_it_169_);
v___x_176_ = lean_string_utf8_get_fast(v_str_166_, v___x_175_);
v___x_177_ = lean_uint32_dec_eq(v___x_176_, v_c_167_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
lean_dec(v_it_169_);
v___x_178_ = lean_string_utf8_next_fast(v_str_166_, v___x_175_);
lean_dec(v___x_175_);
v___x_179_ = lean_nat_sub(v___x_178_, v_startPos_165_);
v___x_180_ = lean_apply_4(v_recur_172_, v___x_179_, v___x_168_, lean_box(0), lean_box(0));
return v___x_180_;
}
else
{
lean_object* v___x_181_; 
lean_dec(v___x_175_);
lean_dec_ref(v_recur_172_);
lean_dec(v___x_168_);
v___x_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_181_, 0, v_it_169_);
return v___x_181_;
}
}
else
{
lean_dec_ref(v_recur_172_);
lean_dec(v_it_169_);
lean_dec(v___x_168_);
lean_inc(v_acc_170_);
return v_acc_170_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_posOf___lam__0___boxed(lean_object* v_stopPos_182_, lean_object* v_startPos_183_, lean_object* v_str_184_, lean_object* v_c_185_, lean_object* v___x_186_, lean_object* v_it_187_, lean_object* v_acc_188_, lean_object* v_hP_189_, lean_object* v_recur_190_){
_start:
{
uint32_t v_c_boxed_191_; lean_object* v_res_192_; 
v_c_boxed_191_ = lean_unbox_uint32(v_c_185_);
lean_dec(v_c_185_);
v_res_192_ = l_Substring_Raw_posOf___lam__0(v_stopPos_182_, v_startPos_183_, v_str_184_, v_c_boxed_191_, v___x_186_, v_it_187_, v_acc_188_, v_hP_189_, v_recur_190_);
lean_dec(v_acc_188_);
lean_dec_ref(v_str_184_);
lean_dec(v_startPos_183_);
lean_dec(v_stopPos_182_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_posOf(lean_object* v_s_193_, uint32_t v_c_194_){
_start:
{
lean_object* v_str_195_; lean_object* v_startPos_196_; lean_object* v_stopPos_197_; uint8_t v___x_198_; 
v_str_195_ = lean_ctor_get(v_s_193_, 0);
lean_inc_ref(v_str_195_);
v_startPos_196_ = lean_ctor_get(v_s_193_, 1);
lean_inc(v_startPos_196_);
v_stopPos_197_ = lean_ctor_get(v_s_193_, 2);
lean_inc(v_stopPos_197_);
lean_dec_ref(v_s_193_);
v___x_198_ = lean_string_is_valid_pos(v_str_195_, v_startPos_196_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; 
lean_dec_ref(v_str_195_);
v___x_199_ = lean_nat_sub(v_stopPos_197_, v_startPos_196_);
lean_dec(v_startPos_196_);
lean_dec(v_stopPos_197_);
return v___x_199_;
}
else
{
uint8_t v___x_200_; 
v___x_200_ = lean_string_is_valid_pos(v_str_195_, v_stopPos_197_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; 
lean_dec_ref(v_str_195_);
v___x_201_ = lean_nat_sub(v_stopPos_197_, v_startPos_196_);
lean_dec(v_startPos_196_);
lean_dec(v_stopPos_197_);
return v___x_201_;
}
else
{
uint8_t v___x_202_; 
v___x_202_ = lean_nat_dec_le(v_startPos_196_, v_stopPos_197_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; 
lean_dec_ref(v_str_195_);
v___x_203_ = lean_nat_sub(v_stopPos_197_, v_startPos_196_);
lean_dec(v_startPos_196_);
lean_dec(v_stopPos_197_);
return v___x_203_;
}
else
{
lean_object* v_searcher_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___f_207_; lean_object* v___x_208_; 
v_searcher_204_ = lean_unsigned_to_nat(0u);
v___x_205_ = lean_box(0);
v___x_206_ = lean_box_uint32(v_c_194_);
lean_inc(v_startPos_196_);
lean_inc(v_stopPos_197_);
v___f_207_ = lean_alloc_closure((void*)(l_Substring_Raw_posOf___lam__0___boxed), 9, 5);
lean_closure_set(v___f_207_, 0, v_stopPos_197_);
lean_closure_set(v___f_207_, 1, v_startPos_196_);
lean_closure_set(v___f_207_, 2, v_str_195_);
lean_closure_set(v___f_207_, 3, v___x_206_);
lean_closure_set(v___f_207_, 4, v___x_205_);
v___x_208_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_207_, v_searcher_204_, v___x_205_, lean_box(0));
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v___x_209_; 
v___x_209_ = lean_nat_sub(v_stopPos_197_, v_startPos_196_);
lean_dec(v_startPos_196_);
lean_dec(v_stopPos_197_);
return v___x_209_;
}
else
{
lean_object* v_val_210_; 
lean_dec(v_stopPos_197_);
lean_dec(v_startPos_196_);
v_val_210_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_val_210_);
lean_dec_ref_known(v___x_208_, 1);
return v_val_210_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_posOf___boxed(lean_object* v_s_211_, lean_object* v_c_212_){
_start:
{
uint32_t v_c_boxed_213_; lean_object* v_res_214_; 
v_c_boxed_213_ = lean_unbox_uint32(v_c_212_);
lean_dec(v_c_212_);
v_res_214_ = l_Substring_Raw_posOf(v_s_211_, v_c_boxed_213_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_drop(lean_object* v_x_215_, lean_object* v_x_216_){
_start:
{
lean_object* v_str_217_; lean_object* v_startPos_218_; lean_object* v_stopPos_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_229_; 
v_str_217_ = lean_ctor_get(v_x_215_, 0);
lean_inc_ref(v_str_217_);
v_startPos_218_ = lean_ctor_get(v_x_215_, 1);
lean_inc(v_startPos_218_);
v_stopPos_219_ = lean_ctor_get(v_x_215_, 2);
lean_inc(v_stopPos_219_);
v___x_220_ = lean_unsigned_to_nat(0u);
v___x_221_ = l_Substring_Raw_nextn(v_x_215_, v_x_216_, v___x_220_);
v_isSharedCheck_229_ = !lean_is_exclusive(v_x_215_);
if (v_isSharedCheck_229_ == 0)
{
lean_object* v_unused_230_; lean_object* v_unused_231_; lean_object* v_unused_232_; 
v_unused_230_ = lean_ctor_get(v_x_215_, 2);
lean_dec(v_unused_230_);
v_unused_231_ = lean_ctor_get(v_x_215_, 1);
lean_dec(v_unused_231_);
v_unused_232_ = lean_ctor_get(v_x_215_, 0);
lean_dec(v_unused_232_);
v___x_223_ = v_x_215_;
v_isShared_224_ = v_isSharedCheck_229_;
goto v_resetjp_222_;
}
else
{
lean_dec(v_x_215_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_229_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_225_; lean_object* v___x_227_; 
v___x_225_ = lean_nat_add(v_startPos_218_, v___x_221_);
lean_dec(v___x_221_);
lean_dec(v_startPos_218_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 1, v___x_225_);
v___x_227_ = v___x_223_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_str_217_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v___x_225_);
lean_ctor_set(v_reuseFailAlloc_228_, 2, v_stopPos_219_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
LEAN_EXPORT lean_object* lean_substring_drop(lean_object* v_a_233_, lean_object* v_a_234_){
_start:
{
lean_object* v_str_235_; lean_object* v_startPos_236_; lean_object* v_stopPos_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_247_; 
v_str_235_ = lean_ctor_get(v_a_233_, 0);
lean_inc_ref(v_str_235_);
v_startPos_236_ = lean_ctor_get(v_a_233_, 1);
lean_inc(v_startPos_236_);
v_stopPos_237_ = lean_ctor_get(v_a_233_, 2);
lean_inc(v_stopPos_237_);
v___x_238_ = lean_unsigned_to_nat(0u);
v___x_239_ = l_Substring_Raw_nextn(v_a_233_, v_a_234_, v___x_238_);
v_isSharedCheck_247_ = !lean_is_exclusive(v_a_233_);
if (v_isSharedCheck_247_ == 0)
{
lean_object* v_unused_248_; lean_object* v_unused_249_; lean_object* v_unused_250_; 
v_unused_248_ = lean_ctor_get(v_a_233_, 2);
lean_dec(v_unused_248_);
v_unused_249_ = lean_ctor_get(v_a_233_, 1);
lean_dec(v_unused_249_);
v_unused_250_ = lean_ctor_get(v_a_233_, 0);
lean_dec(v_unused_250_);
v___x_241_ = v_a_233_;
v_isShared_242_ = v_isSharedCheck_247_;
goto v_resetjp_240_;
}
else
{
lean_dec(v_a_233_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_247_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_243_; lean_object* v___x_245_; 
v___x_243_ = lean_nat_add(v_startPos_236_, v___x_239_);
lean_dec(v___x_239_);
lean_dec(v_startPos_236_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 1, v___x_243_);
v___x_245_ = v___x_241_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_str_235_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v___x_243_);
lean_ctor_set(v_reuseFailAlloc_246_, 2, v_stopPos_237_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropRight(lean_object* v_x_251_, lean_object* v_x_252_){
_start:
{
lean_object* v_str_253_; lean_object* v_startPos_254_; lean_object* v_stopPos_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_265_; 
v_str_253_ = lean_ctor_get(v_x_251_, 0);
lean_inc_ref(v_str_253_);
v_startPos_254_ = lean_ctor_get(v_x_251_, 1);
lean_inc(v_startPos_254_);
v_stopPos_255_ = lean_ctor_get(v_x_251_, 2);
v___x_256_ = lean_nat_sub(v_stopPos_255_, v_startPos_254_);
v___x_257_ = l_Substring_Raw_prevn(v_x_251_, v_x_252_, v___x_256_);
v_isSharedCheck_265_ = !lean_is_exclusive(v_x_251_);
if (v_isSharedCheck_265_ == 0)
{
lean_object* v_unused_266_; lean_object* v_unused_267_; lean_object* v_unused_268_; 
v_unused_266_ = lean_ctor_get(v_x_251_, 2);
lean_dec(v_unused_266_);
v_unused_267_ = lean_ctor_get(v_x_251_, 1);
lean_dec(v_unused_267_);
v_unused_268_ = lean_ctor_get(v_x_251_, 0);
lean_dec(v_unused_268_);
v___x_259_ = v_x_251_;
v_isShared_260_ = v_isSharedCheck_265_;
goto v_resetjp_258_;
}
else
{
lean_dec(v_x_251_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_265_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_261_ = lean_nat_add(v_startPos_254_, v___x_257_);
lean_dec(v___x_257_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 2, v___x_261_);
v___x_263_ = v___x_259_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_str_253_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v_startPos_254_);
lean_ctor_set(v_reuseFailAlloc_264_, 2, v___x_261_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_take(lean_object* v_x_269_, lean_object* v_x_270_){
_start:
{
lean_object* v_str_271_; lean_object* v_startPos_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_282_; 
v_str_271_ = lean_ctor_get(v_x_269_, 0);
lean_inc_ref(v_str_271_);
v_startPos_272_ = lean_ctor_get(v_x_269_, 1);
lean_inc(v_startPos_272_);
v___x_273_ = lean_unsigned_to_nat(0u);
v___x_274_ = l_Substring_Raw_nextn(v_x_269_, v_x_270_, v___x_273_);
v_isSharedCheck_282_ = !lean_is_exclusive(v_x_269_);
if (v_isSharedCheck_282_ == 0)
{
lean_object* v_unused_283_; lean_object* v_unused_284_; lean_object* v_unused_285_; 
v_unused_283_ = lean_ctor_get(v_x_269_, 2);
lean_dec(v_unused_283_);
v_unused_284_ = lean_ctor_get(v_x_269_, 1);
lean_dec(v_unused_284_);
v_unused_285_ = lean_ctor_get(v_x_269_, 0);
lean_dec(v_unused_285_);
v___x_276_ = v_x_269_;
v_isShared_277_ = v_isSharedCheck_282_;
goto v_resetjp_275_;
}
else
{
lean_dec(v_x_269_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_282_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_278_; lean_object* v___x_280_; 
v___x_278_ = lean_nat_add(v_startPos_272_, v___x_274_);
lean_dec(v___x_274_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 2, v___x_278_);
v___x_280_ = v___x_276_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_str_271_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_startPos_272_);
lean_ctor_set(v_reuseFailAlloc_281_, 2, v___x_278_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRight(lean_object* v_x_286_, lean_object* v_x_287_){
_start:
{
lean_object* v_str_288_; lean_object* v_startPos_289_; lean_object* v_stopPos_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_300_; 
v_str_288_ = lean_ctor_get(v_x_286_, 0);
lean_inc_ref(v_str_288_);
v_startPos_289_ = lean_ctor_get(v_x_286_, 1);
lean_inc(v_startPos_289_);
v_stopPos_290_ = lean_ctor_get(v_x_286_, 2);
lean_inc(v_stopPos_290_);
v___x_291_ = lean_nat_sub(v_stopPos_290_, v_startPos_289_);
v___x_292_ = l_Substring_Raw_prevn(v_x_286_, v_x_287_, v___x_291_);
v_isSharedCheck_300_ = !lean_is_exclusive(v_x_286_);
if (v_isSharedCheck_300_ == 0)
{
lean_object* v_unused_301_; lean_object* v_unused_302_; lean_object* v_unused_303_; 
v_unused_301_ = lean_ctor_get(v_x_286_, 2);
lean_dec(v_unused_301_);
v_unused_302_ = lean_ctor_get(v_x_286_, 1);
lean_dec(v_unused_302_);
v_unused_303_ = lean_ctor_get(v_x_286_, 0);
lean_dec(v_unused_303_);
v___x_294_ = v_x_286_;
v_isShared_295_ = v_isSharedCheck_300_;
goto v_resetjp_293_;
}
else
{
lean_dec(v_x_286_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_300_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_296_; lean_object* v___x_298_; 
v___x_296_ = lean_nat_add(v_startPos_289_, v___x_292_);
lean_dec(v___x_292_);
lean_dec(v_startPos_289_);
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 1, v___x_296_);
v___x_298_ = v___x_294_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_str_288_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v___x_296_);
lean_ctor_set(v_reuseFailAlloc_299_, 2, v_stopPos_290_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_atEnd(lean_object* v_x_304_, lean_object* v_x_305_){
_start:
{
lean_object* v_startPos_306_; lean_object* v_stopPos_307_; lean_object* v___x_308_; uint8_t v_decide_309_; 
v_startPos_306_ = lean_ctor_get(v_x_304_, 1);
v_stopPos_307_ = lean_ctor_get(v_x_304_, 2);
v___x_308_ = lean_nat_add(v_startPos_306_, v_x_305_);
v_decide_309_ = lean_nat_dec_eq(v___x_308_, v_stopPos_307_);
lean_dec(v___x_308_);
return v_decide_309_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_atEnd___boxed(lean_object* v_x_310_, lean_object* v_x_311_){
_start:
{
uint8_t v_res_312_; lean_object* v_r_313_; 
v_res_312_ = l_Substring_Raw_atEnd(v_x_310_, v_x_311_);
lean_dec(v_x_311_);
lean_dec_ref(v_x_310_);
v_r_313_ = lean_box(v_res_312_);
return v_r_313_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_extract(lean_object* v_x_318_, lean_object* v_x_319_, lean_object* v_x_320_){
_start:
{
lean_object* v_str_321_; lean_object* v_startPos_322_; lean_object* v_stopPos_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_341_; 
v_str_321_ = lean_ctor_get(v_x_318_, 0);
v_startPos_322_ = lean_ctor_get(v_x_318_, 1);
v_stopPos_323_ = lean_ctor_get(v_x_318_, 2);
v_isSharedCheck_341_ = !lean_is_exclusive(v_x_318_);
if (v_isSharedCheck_341_ == 0)
{
v___x_325_ = v_x_318_;
v_isShared_326_ = v_isSharedCheck_341_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_stopPos_323_);
lean_inc(v_startPos_322_);
lean_inc(v_str_321_);
lean_dec(v_x_318_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_341_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___y_328_; uint8_t v___x_337_; 
v___x_337_ = lean_nat_dec_le(v_x_320_, v_x_319_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_338_ = lean_nat_add(v_startPos_322_, v_x_319_);
v___x_339_ = lean_nat_dec_le(v_stopPos_323_, v___x_338_);
if (v___x_339_ == 0)
{
v___y_328_ = v___x_338_;
goto v___jp_327_;
}
else
{
lean_dec(v___x_338_);
lean_inc(v_stopPos_323_);
v___y_328_ = v_stopPos_323_;
goto v___jp_327_;
}
}
else
{
lean_object* v___x_340_; 
lean_del_object(v___x_325_);
lean_dec(v_stopPos_323_);
lean_dec(v_startPos_322_);
lean_dec_ref(v_str_321_);
v___x_340_ = ((lean_object*)(l_Substring_Raw_extract___closed__1));
return v___x_340_;
}
v___jp_327_:
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = lean_nat_add(v_startPos_322_, v_x_320_);
lean_dec(v_startPos_322_);
v___x_330_ = lean_nat_dec_le(v_stopPos_323_, v___x_329_);
if (v___x_330_ == 0)
{
lean_object* v___x_332_; 
lean_dec(v_stopPos_323_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 2, v___x_329_);
lean_ctor_set(v___x_325_, 1, v___y_328_);
v___x_332_ = v___x_325_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_str_321_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v___y_328_);
lean_ctor_set(v_reuseFailAlloc_333_, 2, v___x_329_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
else
{
lean_object* v___x_335_; 
lean_dec(v___x_329_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 1, v___y_328_);
v___x_335_ = v___x_325_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_str_321_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v___y_328_);
lean_ctor_set(v_reuseFailAlloc_336_, 2, v_stopPos_323_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_extract___boxed(lean_object* v_x_342_, lean_object* v_x_343_, lean_object* v_x_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Substring_Raw_extract(v_x_342_, v_x_343_, v_x_344_);
lean_dec(v_x_344_);
lean_dec(v_x_343_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* lean_substring_extract(lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_str_349_; lean_object* v_startPos_350_; lean_object* v_stopPos_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_369_; 
v_str_349_ = lean_ctor_get(v_a_346_, 0);
v_startPos_350_ = lean_ctor_get(v_a_346_, 1);
v_stopPos_351_ = lean_ctor_get(v_a_346_, 2);
v_isSharedCheck_369_ = !lean_is_exclusive(v_a_346_);
if (v_isSharedCheck_369_ == 0)
{
v___x_353_ = v_a_346_;
v_isShared_354_ = v_isSharedCheck_369_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_stopPos_351_);
lean_inc(v_startPos_350_);
lean_inc(v_str_349_);
lean_dec(v_a_346_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_369_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___y_356_; uint8_t v___x_365_; 
v___x_365_ = lean_nat_dec_le(v_a_348_, v_a_347_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_366_ = lean_nat_add(v_startPos_350_, v_a_347_);
lean_dec(v_a_347_);
v___x_367_ = lean_nat_dec_le(v_stopPos_351_, v___x_366_);
if (v___x_367_ == 0)
{
v___y_356_ = v___x_366_;
goto v___jp_355_;
}
else
{
lean_dec(v___x_366_);
lean_inc(v_stopPos_351_);
v___y_356_ = v_stopPos_351_;
goto v___jp_355_;
}
}
else
{
lean_object* v___x_368_; 
lean_del_object(v___x_353_);
lean_dec(v_stopPos_351_);
lean_dec(v_startPos_350_);
lean_dec_ref(v_str_349_);
lean_dec(v_a_348_);
lean_dec(v_a_347_);
v___x_368_ = ((lean_object*)(l_Substring_Raw_extract___closed__1));
return v___x_368_;
}
v___jp_355_:
{
lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_357_ = lean_nat_add(v_startPos_350_, v_a_348_);
lean_dec(v_a_348_);
lean_dec(v_startPos_350_);
v___x_358_ = lean_nat_dec_le(v_stopPos_351_, v___x_357_);
if (v___x_358_ == 0)
{
lean_object* v___x_360_; 
lean_dec(v_stopPos_351_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 2, v___x_357_);
lean_ctor_set(v___x_353_, 1, v___y_356_);
v___x_360_ = v___x_353_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_str_349_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v___y_356_);
lean_ctor_set(v_reuseFailAlloc_361_, 2, v___x_357_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
else
{
lean_object* v___x_363_; 
lean_dec(v___x_357_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 1, v___y_356_);
v___x_363_ = v___x_353_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_str_349_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v___y_356_);
lean_ctor_set(v_reuseFailAlloc_364_, 2, v_stopPos_351_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop(lean_object* v_s_370_, lean_object* v_sep_371_, lean_object* v_b_372_, lean_object* v_i_373_, lean_object* v_j_374_, lean_object* v_r_375_){
_start:
{
lean_object* v___y_377_; lean_object* v___y_381_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v_str_390_; lean_object* v_startPos_391_; lean_object* v_stopPos_392_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_403_; lean_object* v___y_414_; lean_object* v___x_419_; uint8_t v___x_420_; 
v_str_390_ = lean_ctor_get(v_s_370_, 0);
v_startPos_391_ = lean_ctor_get(v_s_370_, 1);
v_stopPos_392_ = lean_ctor_get(v_s_370_, 2);
v___x_419_ = lean_nat_sub(v_stopPos_392_, v_startPos_391_);
v___x_420_ = lean_nat_dec_lt(v_i_373_, v___x_419_);
lean_dec(v___x_419_);
if (v___x_420_ == 0)
{
lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_449_; 
lean_inc(v_stopPos_392_);
lean_inc(v_startPos_391_);
lean_inc_ref(v_str_390_);
v_isSharedCheck_449_ = !lean_is_exclusive(v_s_370_);
if (v_isSharedCheck_449_ == 0)
{
lean_object* v_unused_450_; lean_object* v_unused_451_; lean_object* v_unused_452_; 
v_unused_450_ = lean_ctor_get(v_s_370_, 2);
lean_dec(v_unused_450_);
v_unused_451_ = lean_ctor_get(v_s_370_, 1);
lean_dec(v_unused_451_);
v_unused_452_ = lean_ctor_get(v_s_370_, 0);
lean_dec(v_unused_452_);
v___x_422_ = v_s_370_;
v_isShared_423_ = v_isSharedCheck_449_;
goto v_resetjp_421_;
}
else
{
lean_dec(v_s_370_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_449_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
uint8_t v___x_424_; 
v___x_424_ = lean_string_utf8_at_end(v_sep_371_, v_j_374_);
if (v___x_424_ == 0)
{
uint8_t v___x_425_; 
lean_del_object(v___x_422_);
lean_dec(v_j_374_);
v___x_425_ = lean_nat_dec_le(v_i_373_, v_b_372_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_426_ = lean_nat_add(v_startPos_391_, v_b_372_);
lean_dec(v_b_372_);
v___x_427_ = lean_nat_dec_le(v_stopPos_392_, v___x_426_);
if (v___x_427_ == 0)
{
v___y_414_ = v___x_426_;
goto v___jp_413_;
}
else
{
lean_dec(v___x_426_);
lean_inc(v_stopPos_392_);
v___y_414_ = v_stopPos_392_;
goto v___jp_413_;
}
}
else
{
lean_object* v___x_428_; 
lean_dec(v_stopPos_392_);
lean_dec(v_startPos_391_);
lean_dec_ref(v_str_390_);
lean_dec(v_i_373_);
lean_dec(v_b_372_);
v___x_428_ = ((lean_object*)(l_Substring_Raw_extract___closed__1));
v___y_377_ = v___x_428_;
goto v___jp_376_;
}
}
else
{
lean_object* v___x_429_; lean_object* v___y_431_; lean_object* v___x_435_; lean_object* v___y_437_; uint8_t v___x_446_; 
v___x_429_ = ((lean_object*)(l_Substring_Raw_extract___closed__1));
v___x_435_ = lean_nat_sub(v_i_373_, v_j_374_);
lean_dec(v_j_374_);
lean_dec(v_i_373_);
v___x_446_ = lean_nat_dec_le(v___x_435_, v_b_372_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_447_ = lean_nat_add(v_startPos_391_, v_b_372_);
lean_dec(v_b_372_);
v___x_448_ = lean_nat_dec_le(v_stopPos_392_, v___x_447_);
if (v___x_448_ == 0)
{
v___y_437_ = v___x_447_;
goto v___jp_436_;
}
else
{
lean_dec(v___x_447_);
lean_inc(v_stopPos_392_);
v___y_437_ = v_stopPos_392_;
goto v___jp_436_;
}
}
else
{
lean_dec(v___x_435_);
lean_del_object(v___x_422_);
lean_dec(v_stopPos_392_);
lean_dec(v_startPos_391_);
lean_dec_ref(v_str_390_);
lean_dec(v_b_372_);
v___y_431_ = v___x_429_;
goto v___jp_430_;
}
v___jp_430_:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_432_, 0, v___y_431_);
lean_ctor_set(v___x_432_, 1, v_r_375_);
v___x_433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_429_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
v___x_434_ = l_List_reverse___redArg(v___x_433_);
return v___x_434_;
}
v___jp_436_:
{
lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_438_ = lean_nat_add(v_startPos_391_, v___x_435_);
lean_dec(v___x_435_);
lean_dec(v_startPos_391_);
v___x_439_ = lean_nat_dec_le(v_stopPos_392_, v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_441_; 
lean_dec(v_stopPos_392_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 2, v___x_438_);
lean_ctor_set(v___x_422_, 1, v___y_437_);
v___x_441_ = v___x_422_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_str_390_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v___y_437_);
lean_ctor_set(v_reuseFailAlloc_442_, 2, v___x_438_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
v___y_431_ = v___x_441_;
goto v___jp_430_;
}
}
else
{
lean_object* v___x_444_; 
lean_dec(v___x_438_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 1, v___y_437_);
v___x_444_ = v___x_422_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_str_390_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v___y_437_);
lean_ctor_set(v_reuseFailAlloc_445_, 2, v_stopPos_392_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
v___y_431_ = v___x_444_;
goto v___jp_430_;
}
}
}
}
}
}
else
{
lean_object* v___x_453_; uint32_t v___x_454_; uint32_t v___x_455_; uint8_t v___x_456_; 
v___x_453_ = lean_nat_add(v_startPos_391_, v_i_373_);
v___x_454_ = lean_string_utf8_get(v_str_390_, v___x_453_);
v___x_455_ = lean_string_utf8_get(v_sep_371_, v_j_374_);
v___x_456_ = lean_uint32_dec_eq(v___x_454_, v___x_455_);
if (v___x_456_ == 0)
{
uint8_t v_decide_457_; 
lean_dec(v_j_374_);
v_decide_457_ = lean_nat_dec_eq(v___x_453_, v_stopPos_392_);
if (v_decide_457_ == 0)
{
lean_object* v___x_458_; lean_object* v___x_459_; 
lean_dec(v_i_373_);
v___x_458_ = lean_string_utf8_next(v_str_390_, v___x_453_);
lean_dec(v___x_453_);
v___x_459_ = lean_nat_sub(v___x_458_, v_startPos_391_);
lean_dec(v___x_458_);
v___y_381_ = v___x_459_;
goto v___jp_380_;
}
else
{
lean_dec(v___x_453_);
v___y_381_ = v_i_373_;
goto v___jp_380_;
}
}
else
{
uint8_t v_decide_460_; 
v_decide_460_ = lean_nat_dec_eq(v___x_453_, v_stopPos_392_);
if (v_decide_460_ == 0)
{
lean_object* v___x_461_; lean_object* v___x_462_; 
lean_dec(v_i_373_);
v___x_461_ = lean_string_utf8_next(v_str_390_, v___x_453_);
lean_dec(v___x_453_);
v___x_462_ = lean_nat_sub(v___x_461_, v_startPos_391_);
lean_dec(v___x_461_);
v___y_403_ = v___x_462_;
goto v___jp_402_;
}
else
{
lean_dec(v___x_453_);
v___y_403_ = v_i_373_;
goto v___jp_402_;
}
}
}
v___jp_376_:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_378_, 0, v___y_377_);
lean_ctor_set(v___x_378_, 1, v_r_375_);
v___x_379_ = l_List_reverse___redArg(v___x_378_);
return v___x_379_;
}
v___jp_380_:
{
lean_object* v___x_382_; 
v___x_382_ = lean_unsigned_to_nat(0u);
v_i_373_ = v___y_381_;
v_j_374_ = v___x_382_;
goto _start;
}
v___jp_384_:
{
lean_object* v___x_388_; 
v___x_388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_388_, 0, v___y_387_);
lean_ctor_set(v___x_388_, 1, v_r_375_);
lean_inc(v___y_385_);
v_b_372_ = v___y_385_;
v_i_373_ = v___y_385_;
v_j_374_ = v___y_386_;
v_r_375_ = v___x_388_;
goto _start;
}
v___jp_393_:
{
lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_398_ = lean_nat_add(v_startPos_391_, v___y_394_);
lean_dec(v___y_394_);
v___x_399_ = lean_nat_dec_le(v_stopPos_392_, v___x_398_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; 
lean_inc_ref(v_str_390_);
v___x_400_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_400_, 0, v_str_390_);
lean_ctor_set(v___x_400_, 1, v___y_397_);
lean_ctor_set(v___x_400_, 2, v___x_398_);
v___y_385_ = v___y_395_;
v___y_386_ = v___y_396_;
v___y_387_ = v___x_400_;
goto v___jp_384_;
}
else
{
lean_object* v___x_401_; 
lean_dec(v___x_398_);
lean_inc(v_stopPos_392_);
lean_inc_ref(v_str_390_);
v___x_401_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_401_, 0, v_str_390_);
lean_ctor_set(v___x_401_, 1, v___y_397_);
lean_ctor_set(v___x_401_, 2, v_stopPos_392_);
v___y_385_ = v___y_395_;
v___y_386_ = v___y_396_;
v___y_387_ = v___x_401_;
goto v___jp_384_;
}
}
v___jp_402_:
{
lean_object* v_j_404_; uint8_t v___x_405_; 
v_j_404_ = lean_string_utf8_next(v_sep_371_, v_j_374_);
lean_dec(v_j_374_);
v___x_405_ = lean_string_utf8_at_end(v_sep_371_, v_j_404_);
if (v___x_405_ == 0)
{
v_i_373_ = v___y_403_;
v_j_374_ = v_j_404_;
goto _start;
}
else
{
lean_object* v___x_407_; lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_407_ = lean_unsigned_to_nat(0u);
v___x_408_ = lean_nat_sub(v___y_403_, v_j_404_);
lean_dec(v_j_404_);
v___x_409_ = lean_nat_dec_le(v___x_408_, v_b_372_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_410_ = lean_nat_add(v_startPos_391_, v_b_372_);
lean_dec(v_b_372_);
v___x_411_ = lean_nat_dec_le(v_stopPos_392_, v___x_410_);
if (v___x_411_ == 0)
{
v___y_394_ = v___x_408_;
v___y_395_ = v___y_403_;
v___y_396_ = v___x_407_;
v___y_397_ = v___x_410_;
goto v___jp_393_;
}
else
{
lean_dec(v___x_410_);
lean_inc(v_stopPos_392_);
v___y_394_ = v___x_408_;
v___y_395_ = v___y_403_;
v___y_396_ = v___x_407_;
v___y_397_ = v_stopPos_392_;
goto v___jp_393_;
}
}
else
{
lean_object* v___x_412_; 
lean_dec(v___x_408_);
lean_dec(v_b_372_);
v___x_412_ = ((lean_object*)(l_Substring_Raw_extract___closed__1));
v___y_385_ = v___y_403_;
v___y_386_ = v___x_407_;
v___y_387_ = v___x_412_;
goto v___jp_384_;
}
}
}
v___jp_413_:
{
lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_415_ = lean_nat_add(v_startPos_391_, v_i_373_);
lean_dec(v_i_373_);
lean_dec(v_startPos_391_);
v___x_416_ = lean_nat_dec_le(v_stopPos_392_, v___x_415_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; 
lean_dec(v_stopPos_392_);
v___x_417_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_417_, 0, v_str_390_);
lean_ctor_set(v___x_417_, 1, v___y_414_);
lean_ctor_set(v___x_417_, 2, v___x_415_);
v___y_377_ = v___x_417_;
goto v___jp_376_;
}
else
{
lean_object* v___x_418_; 
lean_dec(v___x_415_);
v___x_418_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_418_, 0, v_str_390_);
lean_ctor_set(v___x_418_, 1, v___y_414_);
lean_ctor_set(v___x_418_, 2, v_stopPos_392_);
v___y_377_ = v___x_418_;
goto v___jp_376_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___boxed(lean_object* v_s_463_, lean_object* v_sep_464_, lean_object* v_b_465_, lean_object* v_i_466_, lean_object* v_j_467_, lean_object* v_r_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop(v_s_463_, v_sep_464_, v_b_465_, v_i_466_, v_j_467_, v_r_468_);
lean_dec_ref(v_sep_464_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_splitOn(lean_object* v_s_470_, lean_object* v_sep_471_){
_start:
{
lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_472_ = ((lean_object*)(l_Substring_Raw_extract___closed__0));
v___x_473_ = lean_string_dec_eq(v_sep_471_, v___x_472_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_474_ = lean_unsigned_to_nat(0u);
v___x_475_ = lean_box(0);
v___x_476_ = l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop(v_s_470_, v_sep_471_, v___x_474_, v___x_474_, v___x_474_, v___x_475_);
return v___x_476_;
}
else
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = lean_box(0);
v___x_478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_478_, 0, v_s_470_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
return v___x_478_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_splitOn___boxed(lean_object* v_s_479_, lean_object* v_sep_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Substring_Raw_splitOn(v_s_479_, v_sep_480_);
lean_dec_ref(v_sep_480_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldl___redArg___lam__0(lean_object* v___y_482_, lean_object* v_f_483_, lean_object* v_it_484_, lean_object* v_acc_485_, lean_object* v_hP_486_, lean_object* v_recur_487_){
_start:
{
lean_object* v_str_488_; lean_object* v_startInclusive_489_; lean_object* v_endExclusive_490_; lean_object* v___x_491_; uint8_t v_decide_492_; 
v_str_488_ = lean_ctor_get(v___y_482_, 0);
v_startInclusive_489_ = lean_ctor_get(v___y_482_, 1);
v_endExclusive_490_ = lean_ctor_get(v___y_482_, 2);
v___x_491_ = lean_nat_sub(v_endExclusive_490_, v_startInclusive_489_);
v_decide_492_ = lean_nat_dec_eq(v_it_484_, v___x_491_);
lean_dec(v___x_491_);
if (v_decide_492_ == 0)
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; uint32_t v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_493_ = lean_nat_add(v_startInclusive_489_, v_it_484_);
v___x_494_ = lean_string_utf8_next_fast(v_str_488_, v___x_493_);
v___x_495_ = lean_nat_sub(v___x_494_, v_startInclusive_489_);
v___x_496_ = lean_string_utf8_get_fast(v_str_488_, v___x_493_);
lean_dec(v___x_493_);
v___x_497_ = lean_box_uint32(v___x_496_);
v___x_498_ = lean_apply_2(v_f_483_, v_acc_485_, v___x_497_);
v___x_499_ = lean_apply_4(v_recur_487_, v___x_495_, v___x_498_, lean_box(0), lean_box(0));
return v___x_499_;
}
else
{
lean_dec(v_recur_487_);
lean_dec(v_f_483_);
return v_acc_485_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldl___redArg___lam__0___boxed(lean_object* v___y_500_, lean_object* v_f_501_, lean_object* v_it_502_, lean_object* v_acc_503_, lean_object* v_hP_504_, lean_object* v_recur_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Substring_Raw_foldl___redArg___lam__0(v___y_500_, v_f_501_, v_it_502_, v_acc_503_, v_hP_504_, v_recur_505_);
lean_dec(v_it_502_);
lean_dec_ref(v___y_500_);
return v_res_506_;
}
}
static lean_object* _init_l_Substring_Raw_foldl___redArg___closed__3(void){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_510_ = ((lean_object*)(l_Substring_Raw_foldl___redArg___closed__2));
v___x_511_ = lean_unsigned_to_nat(14u);
v___x_512_ = lean_unsigned_to_nat(22u);
v___x_513_ = ((lean_object*)(l_Substring_Raw_foldl___redArg___closed__1));
v___x_514_ = ((lean_object*)(l_Substring_Raw_foldl___redArg___closed__0));
v___x_515_ = l_mkPanicMessageWithDecl(v___x_514_, v___x_513_, v___x_512_, v___x_511_, v___x_510_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldl___redArg(lean_object* v_f_516_, lean_object* v_init_517_, lean_object* v_s_518_){
_start:
{
lean_object* v___y_520_; lean_object* v_str_524_; lean_object* v_startPos_525_; lean_object* v_stopPos_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_540_; 
v_str_524_ = lean_ctor_get(v_s_518_, 0);
v_startPos_525_ = lean_ctor_get(v_s_518_, 1);
v_stopPos_526_ = lean_ctor_get(v_s_518_, 2);
v_isSharedCheck_540_ = !lean_is_exclusive(v_s_518_);
if (v_isSharedCheck_540_ == 0)
{
v___x_528_ = v_s_518_;
v_isShared_529_ = v_isSharedCheck_540_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_stopPos_526_);
lean_inc(v_startPos_525_);
lean_inc(v_str_524_);
lean_dec(v_s_518_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_540_;
goto v_resetjp_527_;
}
v___jp_519_:
{
lean_object* v___f_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___f_521_ = lean_alloc_closure((void*)(l_Substring_Raw_foldl___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_521_, 0, v___y_520_);
lean_closure_set(v___f_521_, 1, v_f_516_);
v___x_522_ = lean_unsigned_to_nat(0u);
v___x_523_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_521_, v___x_522_, v_init_517_, lean_box(0));
return v___x_523_;
}
v_resetjp_527_:
{
lean_object* v___x_530_; uint8_t v___x_534_; 
v___x_530_ = l_String_instInhabitedSlice;
v___x_534_ = lean_string_is_valid_pos(v_str_524_, v_startPos_525_);
if (v___x_534_ == 0)
{
lean_del_object(v___x_528_);
lean_dec(v_stopPos_526_);
lean_dec(v_startPos_525_);
lean_dec_ref(v_str_524_);
goto v___jp_531_;
}
else
{
uint8_t v___x_535_; 
v___x_535_ = lean_string_is_valid_pos(v_str_524_, v_stopPos_526_);
if (v___x_535_ == 0)
{
lean_del_object(v___x_528_);
lean_dec(v_stopPos_526_);
lean_dec(v_startPos_525_);
lean_dec_ref(v_str_524_);
goto v___jp_531_;
}
else
{
uint8_t v___x_536_; 
v___x_536_ = lean_nat_dec_le(v_startPos_525_, v_stopPos_526_);
if (v___x_536_ == 0)
{
lean_del_object(v___x_528_);
lean_dec(v_stopPos_526_);
lean_dec(v_startPos_525_);
lean_dec_ref(v_str_524_);
goto v___jp_531_;
}
else
{
lean_object* v___x_538_; 
if (v_isShared_529_ == 0)
{
v___x_538_ = v___x_528_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_str_524_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v_startPos_525_);
lean_ctor_set(v_reuseFailAlloc_539_, 2, v_stopPos_526_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
v___y_520_ = v___x_538_;
goto v___jp_519_;
}
}
}
}
v___jp_531_:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_533_ = l_panic___redArg(v___x_530_, v___x_532_);
v___y_520_ = v___x_533_;
goto v___jp_519_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldl(lean_object* v_00_u03b1_541_, lean_object* v_f_542_, lean_object* v_init_543_, lean_object* v_s_544_){
_start:
{
lean_object* v___y_546_; lean_object* v_str_550_; lean_object* v_startPos_551_; lean_object* v_stopPos_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_566_; 
v_str_550_ = lean_ctor_get(v_s_544_, 0);
v_startPos_551_ = lean_ctor_get(v_s_544_, 1);
v_stopPos_552_ = lean_ctor_get(v_s_544_, 2);
v_isSharedCheck_566_ = !lean_is_exclusive(v_s_544_);
if (v_isSharedCheck_566_ == 0)
{
v___x_554_ = v_s_544_;
v_isShared_555_ = v_isSharedCheck_566_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_stopPos_552_);
lean_inc(v_startPos_551_);
lean_inc(v_str_550_);
lean_dec(v_s_544_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_566_;
goto v_resetjp_553_;
}
v___jp_545_:
{
lean_object* v___f_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___f_547_ = lean_alloc_closure((void*)(l_Substring_Raw_foldl___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_547_, 0, v___y_546_);
lean_closure_set(v___f_547_, 1, v_f_542_);
v___x_548_ = lean_unsigned_to_nat(0u);
v___x_549_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_547_, v___x_548_, v_init_543_, lean_box(0));
return v___x_549_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; uint8_t v___x_560_; 
v___x_556_ = l_String_instInhabitedSlice;
v___x_560_ = lean_string_is_valid_pos(v_str_550_, v_startPos_551_);
if (v___x_560_ == 0)
{
lean_del_object(v___x_554_);
lean_dec(v_stopPos_552_);
lean_dec(v_startPos_551_);
lean_dec_ref(v_str_550_);
goto v___jp_557_;
}
else
{
uint8_t v___x_561_; 
v___x_561_ = lean_string_is_valid_pos(v_str_550_, v_stopPos_552_);
if (v___x_561_ == 0)
{
lean_del_object(v___x_554_);
lean_dec(v_stopPos_552_);
lean_dec(v_startPos_551_);
lean_dec_ref(v_str_550_);
goto v___jp_557_;
}
else
{
uint8_t v___x_562_; 
v___x_562_ = lean_nat_dec_le(v_startPos_551_, v_stopPos_552_);
if (v___x_562_ == 0)
{
lean_del_object(v___x_554_);
lean_dec(v_stopPos_552_);
lean_dec(v_startPos_551_);
lean_dec_ref(v_str_550_);
goto v___jp_557_;
}
else
{
lean_object* v___x_564_; 
if (v_isShared_555_ == 0)
{
v___x_564_ = v___x_554_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_str_550_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v_startPos_551_);
lean_ctor_set(v_reuseFailAlloc_565_, 2, v_stopPos_552_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
v___y_546_ = v___x_564_;
goto v___jp_545_;
}
}
}
}
v___jp_557_:
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_559_ = l_panic___redArg(v___x_556_, v___x_558_);
v___y_546_ = v___x_559_;
goto v___jp_545_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr___redArg___lam__0(lean_object* v___y_567_, lean_object* v_f_568_, lean_object* v_it_569_, lean_object* v_acc_570_, lean_object* v_hP_571_, lean_object* v_recur_572_){
_start:
{
lean_object* v___x_573_; uint8_t v_decide_574_; 
v___x_573_ = lean_unsigned_to_nat(0u);
v_decide_574_ = lean_nat_dec_eq(v_it_569_, v___x_573_);
if (v_decide_574_ == 0)
{
lean_object* v_str_575_; lean_object* v_startInclusive_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v_prevPos_579_; lean_object* v___x_580_; uint32_t v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v_str_575_ = lean_ctor_get(v___y_567_, 0);
v_startInclusive_576_ = lean_ctor_get(v___y_567_, 1);
v___x_577_ = lean_unsigned_to_nat(1u);
v___x_578_ = lean_nat_sub(v_it_569_, v___x_577_);
v_prevPos_579_ = l_String_Slice_posLE(v___y_567_, v___x_578_);
v___x_580_ = lean_nat_add(v_startInclusive_576_, v_prevPos_579_);
v___x_581_ = lean_string_utf8_get_fast(v_str_575_, v___x_580_);
lean_dec(v___x_580_);
v___x_582_ = lean_box_uint32(v___x_581_);
v___x_583_ = lean_apply_2(v_f_568_, v___x_582_, v_acc_570_);
v___x_584_ = lean_apply_4(v_recur_572_, v_prevPos_579_, v___x_583_, lean_box(0), lean_box(0));
return v___x_584_;
}
else
{
lean_dec(v_recur_572_);
lean_dec(v_f_568_);
return v_acc_570_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr___redArg___lam__0___boxed(lean_object* v___y_585_, lean_object* v_f_586_, lean_object* v_it_587_, lean_object* v_acc_588_, lean_object* v_hP_589_, lean_object* v_recur_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Substring_Raw_foldr___redArg___lam__0(v___y_585_, v_f_586_, v_it_587_, v_acc_588_, v_hP_589_, v_recur_590_);
lean_dec(v_it_587_);
lean_dec_ref(v___y_585_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr___redArg(lean_object* v_f_592_, lean_object* v_init_593_, lean_object* v_s_594_){
_start:
{
lean_object* v___y_596_; lean_object* v_str_600_; lean_object* v_startPos_601_; lean_object* v_stopPos_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_616_; 
v_str_600_ = lean_ctor_get(v_s_594_, 0);
v_startPos_601_ = lean_ctor_get(v_s_594_, 1);
v_stopPos_602_ = lean_ctor_get(v_s_594_, 2);
v_isSharedCheck_616_ = !lean_is_exclusive(v_s_594_);
if (v_isSharedCheck_616_ == 0)
{
v___x_604_ = v_s_594_;
v_isShared_605_ = v_isSharedCheck_616_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_stopPos_602_);
lean_inc(v_startPos_601_);
lean_inc(v_str_600_);
lean_dec(v_s_594_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_616_;
goto v_resetjp_603_;
}
v___jp_595_:
{
lean_object* v___f_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
lean_inc_ref(v___y_596_);
v___f_597_ = lean_alloc_closure((void*)(l_Substring_Raw_foldr___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_597_, 0, v___y_596_);
lean_closure_set(v___f_597_, 1, v_f_592_);
v___x_598_ = l_String_Slice_revPositions(v___y_596_);
lean_dec_ref(v___y_596_);
v___x_599_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_597_, v___x_598_, v_init_593_, lean_box(0));
return v___x_599_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; uint8_t v___x_610_; 
v___x_606_ = l_String_instInhabitedSlice;
v___x_610_ = lean_string_is_valid_pos(v_str_600_, v_startPos_601_);
if (v___x_610_ == 0)
{
lean_del_object(v___x_604_);
lean_dec(v_stopPos_602_);
lean_dec(v_startPos_601_);
lean_dec_ref(v_str_600_);
goto v___jp_607_;
}
else
{
uint8_t v___x_611_; 
v___x_611_ = lean_string_is_valid_pos(v_str_600_, v_stopPos_602_);
if (v___x_611_ == 0)
{
lean_del_object(v___x_604_);
lean_dec(v_stopPos_602_);
lean_dec(v_startPos_601_);
lean_dec_ref(v_str_600_);
goto v___jp_607_;
}
else
{
uint8_t v___x_612_; 
v___x_612_ = lean_nat_dec_le(v_startPos_601_, v_stopPos_602_);
if (v___x_612_ == 0)
{
lean_del_object(v___x_604_);
lean_dec(v_stopPos_602_);
lean_dec(v_startPos_601_);
lean_dec_ref(v_str_600_);
goto v___jp_607_;
}
else
{
lean_object* v___x_614_; 
if (v_isShared_605_ == 0)
{
v___x_614_ = v___x_604_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_str_600_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_startPos_601_);
lean_ctor_set(v_reuseFailAlloc_615_, 2, v_stopPos_602_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
v___y_596_ = v___x_614_;
goto v___jp_595_;
}
}
}
}
v___jp_607_:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_609_ = l_panic___redArg(v___x_606_, v___x_608_);
v___y_596_ = v___x_609_;
goto v___jp_595_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr(lean_object* v_00_u03b1_617_, lean_object* v_f_618_, lean_object* v_init_619_, lean_object* v_s_620_){
_start:
{
lean_object* v___y_622_; lean_object* v_str_626_; lean_object* v_startPos_627_; lean_object* v_stopPos_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_642_; 
v_str_626_ = lean_ctor_get(v_s_620_, 0);
v_startPos_627_ = lean_ctor_get(v_s_620_, 1);
v_stopPos_628_ = lean_ctor_get(v_s_620_, 2);
v_isSharedCheck_642_ = !lean_is_exclusive(v_s_620_);
if (v_isSharedCheck_642_ == 0)
{
v___x_630_ = v_s_620_;
v_isShared_631_ = v_isSharedCheck_642_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_stopPos_628_);
lean_inc(v_startPos_627_);
lean_inc(v_str_626_);
lean_dec(v_s_620_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_642_;
goto v_resetjp_629_;
}
v___jp_621_:
{
lean_object* v___f_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
lean_inc_ref(v___y_622_);
v___f_623_ = lean_alloc_closure((void*)(l_Substring_Raw_foldr___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_623_, 0, v___y_622_);
lean_closure_set(v___f_623_, 1, v_f_618_);
v___x_624_ = l_String_Slice_revPositions(v___y_622_);
lean_dec_ref(v___y_622_);
v___x_625_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_623_, v___x_624_, v_init_619_, lean_box(0));
return v___x_625_;
}
v_resetjp_629_:
{
lean_object* v___x_632_; uint8_t v___x_636_; 
v___x_632_ = l_String_instInhabitedSlice;
v___x_636_ = lean_string_is_valid_pos(v_str_626_, v_startPos_627_);
if (v___x_636_ == 0)
{
lean_del_object(v___x_630_);
lean_dec(v_stopPos_628_);
lean_dec(v_startPos_627_);
lean_dec_ref(v_str_626_);
goto v___jp_633_;
}
else
{
uint8_t v___x_637_; 
v___x_637_ = lean_string_is_valid_pos(v_str_626_, v_stopPos_628_);
if (v___x_637_ == 0)
{
lean_del_object(v___x_630_);
lean_dec(v_stopPos_628_);
lean_dec(v_startPos_627_);
lean_dec_ref(v_str_626_);
goto v___jp_633_;
}
else
{
uint8_t v___x_638_; 
v___x_638_ = lean_nat_dec_le(v_startPos_627_, v_stopPos_628_);
if (v___x_638_ == 0)
{
lean_del_object(v___x_630_);
lean_dec(v_stopPos_628_);
lean_dec(v_startPos_627_);
lean_dec_ref(v_str_626_);
goto v___jp_633_;
}
else
{
lean_object* v___x_640_; 
if (v_isShared_631_ == 0)
{
v___x_640_ = v___x_630_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_str_626_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v_startPos_627_);
lean_ctor_set(v_reuseFailAlloc_641_, 2, v_stopPos_628_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
v___y_622_ = v___x_640_;
goto v___jp_621_;
}
}
}
}
v___jp_633_:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_635_ = l_panic___redArg(v___x_632_, v___x_634_);
v___y_622_ = v___x_635_;
goto v___jp_621_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_any___lam__0(lean_object* v___x_643_, lean_object* v_s_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(v_s_644_, v___x_643_, v___y_645_, lean_box(0), lean_box(0), v___y_648_, v___y_649_, v___y_650_);
return v___x_651_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_any(lean_object* v_s_652_, lean_object* v_p_653_){
_start:
{
lean_object* v___x_654_; lean_object* v_str_655_; lean_object* v_startPos_656_; lean_object* v_stopPos_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_675_; 
lean_inc_ref(v_p_653_);
v___x_654_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v_p_653_);
v_str_655_ = lean_ctor_get(v_s_652_, 0);
v_startPos_656_ = lean_ctor_get(v_s_652_, 1);
v_stopPos_657_ = lean_ctor_get(v_s_652_, 2);
v_isSharedCheck_675_ = !lean_is_exclusive(v_s_652_);
if (v_isSharedCheck_675_ == 0)
{
v___x_659_ = v_s_652_;
v_isShared_660_ = v_isSharedCheck_675_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_stopPos_657_);
lean_inc(v_startPos_656_);
lean_inc(v_str_655_);
lean_dec(v_s_652_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_675_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; lean_object* v___f_662_; lean_object* v___x_663_; uint8_t v___x_668_; 
v___x_661_ = l_String_instInhabitedSlice;
v___f_662_ = lean_alloc_closure((void*)(l_Substring_Raw_any___lam__0), 8, 1);
lean_closure_set(v___f_662_, 0, v___x_654_);
v___x_663_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_663_, 0, lean_box(0));
lean_closure_set(v___x_663_, 1, v_p_653_);
v___x_668_ = lean_string_is_valid_pos(v_str_655_, v_startPos_656_);
if (v___x_668_ == 0)
{
lean_del_object(v___x_659_);
lean_dec(v_stopPos_657_);
lean_dec(v_startPos_656_);
lean_dec_ref(v_str_655_);
goto v___jp_664_;
}
else
{
uint8_t v___x_669_; 
v___x_669_ = lean_string_is_valid_pos(v_str_655_, v_stopPos_657_);
if (v___x_669_ == 0)
{
lean_del_object(v___x_659_);
lean_dec(v_stopPos_657_);
lean_dec(v_startPos_656_);
lean_dec_ref(v_str_655_);
goto v___jp_664_;
}
else
{
uint8_t v___x_670_; 
v___x_670_ = lean_nat_dec_le(v_startPos_656_, v_stopPos_657_);
if (v___x_670_ == 0)
{
lean_del_object(v___x_659_);
lean_dec(v_stopPos_657_);
lean_dec(v_startPos_656_);
lean_dec_ref(v_str_655_);
goto v___jp_664_;
}
else
{
lean_object* v___x_672_; 
if (v_isShared_660_ == 0)
{
v___x_672_ = v___x_659_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_str_655_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_startPos_656_);
lean_ctor_set(v_reuseFailAlloc_674_, 2, v_stopPos_657_);
v___x_672_ = v_reuseFailAlloc_674_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
uint8_t v___x_673_; 
v___x_673_ = l_String_Slice_contains___redArg(v___f_662_, v___x_672_, v___x_663_);
return v___x_673_;
}
}
}
}
v___jp_664_:
{
lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_665_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_666_ = l_panic___redArg(v___x_661_, v___x_665_);
v___x_667_ = l_String_Slice_contains___redArg(v___f_662_, v___x_666_, v___x_663_);
return v___x_667_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_any___boxed(lean_object* v_s_676_, lean_object* v_p_677_){
_start:
{
uint8_t v_res_678_; lean_object* v_r_679_; 
v_res_678_ = l_Substring_Raw_any(v_s_676_, v_p_677_);
v_r_679_ = lean_box(v_res_678_);
return v_r_679_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_all(lean_object* v_s_680_, lean_object* v_p_681_){
_start:
{
lean_object* v___y_683_; lean_object* v_startInclusive_684_; lean_object* v_endExclusive_685_; lean_object* v_str_691_; lean_object* v_startPos_692_; lean_object* v_stopPos_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_709_; 
v_str_691_ = lean_ctor_get(v_s_680_, 0);
v_startPos_692_ = lean_ctor_get(v_s_680_, 1);
v_stopPos_693_ = lean_ctor_get(v_s_680_, 2);
v_isSharedCheck_709_ = !lean_is_exclusive(v_s_680_);
if (v_isSharedCheck_709_ == 0)
{
v___x_695_ = v_s_680_;
v_isShared_696_ = v_isSharedCheck_709_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_stopPos_693_);
lean_inc(v_startPos_692_);
lean_inc(v_str_691_);
lean_dec(v_s_680_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_709_;
goto v_resetjp_694_;
}
v___jp_682_:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; uint8_t v_decide_690_; 
v___x_686_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v_p_681_);
v___x_687_ = lean_unsigned_to_nat(0u);
v___x_688_ = l_String_Slice_Pos_skipWhile___redArg(v___y_683_, v___x_687_, v___x_686_);
lean_dec_ref(v___y_683_);
v___x_689_ = lean_nat_sub(v_endExclusive_685_, v_startInclusive_684_);
lean_dec(v_startInclusive_684_);
lean_dec(v_endExclusive_685_);
v_decide_690_ = lean_nat_dec_eq(v___x_688_, v___x_689_);
lean_dec(v___x_689_);
lean_dec(v___x_688_);
return v_decide_690_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; uint8_t v___x_703_; 
v___x_697_ = l_String_instInhabitedSlice;
v___x_703_ = lean_string_is_valid_pos(v_str_691_, v_startPos_692_);
if (v___x_703_ == 0)
{
lean_del_object(v___x_695_);
lean_dec(v_stopPos_693_);
lean_dec(v_startPos_692_);
lean_dec_ref(v_str_691_);
goto v___jp_698_;
}
else
{
uint8_t v___x_704_; 
v___x_704_ = lean_string_is_valid_pos(v_str_691_, v_stopPos_693_);
if (v___x_704_ == 0)
{
lean_del_object(v___x_695_);
lean_dec(v_stopPos_693_);
lean_dec(v_startPos_692_);
lean_dec_ref(v_str_691_);
goto v___jp_698_;
}
else
{
uint8_t v___x_705_; 
v___x_705_ = lean_nat_dec_le(v_startPos_692_, v_stopPos_693_);
if (v___x_705_ == 0)
{
lean_del_object(v___x_695_);
lean_dec(v_stopPos_693_);
lean_dec(v_startPos_692_);
lean_dec_ref(v_str_691_);
goto v___jp_698_;
}
else
{
lean_object* v___x_707_; 
lean_inc(v_stopPos_693_);
lean_inc(v_startPos_692_);
if (v_isShared_696_ == 0)
{
v___x_707_ = v___x_695_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_str_691_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v_startPos_692_);
lean_ctor_set(v_reuseFailAlloc_708_, 2, v_stopPos_693_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
v___y_683_ = v___x_707_;
v_startInclusive_684_ = v_startPos_692_;
v_endExclusive_685_ = v_stopPos_693_;
goto v___jp_682_;
}
}
}
}
v___jp_698_:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v_startInclusive_701_; lean_object* v_endExclusive_702_; 
v___x_699_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_700_ = l_panic___redArg(v___x_697_, v___x_699_);
v_startInclusive_701_ = lean_ctor_get(v___x_700_, 1);
lean_inc(v_startInclusive_701_);
v_endExclusive_702_ = lean_ctor_get(v___x_700_, 2);
lean_inc(v_endExclusive_702_);
v___y_683_ = v___x_700_;
v_startInclusive_684_ = v_startInclusive_701_;
v_endExclusive_685_ = v_endExclusive_702_;
goto v___jp_682_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_all___boxed(lean_object* v_s_710_, lean_object* v_p_711_){
_start:
{
uint8_t v_res_712_; lean_object* v_r_713_; 
v_res_712_ = l_Substring_Raw_all(v_s_710_, v_p_711_);
v_r_713_ = lean_box(v_res_712_);
return v_r_713_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(lean_object* v_msg_714_){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_715_ = l_String_instInhabitedSlice;
v___x_716_ = lean_panic_fn_borrowed(v___x_715_, v_msg_714_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0(lean_object* v_p_717_, lean_object* v_s_718_, lean_object* v_pos_719_){
_start:
{
lean_object* v_str_720_; lean_object* v_startInclusive_721_; lean_object* v_endExclusive_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; uint8_t v_decide_726_; 
v_str_720_ = lean_ctor_get(v_s_718_, 0);
v_startInclusive_721_ = lean_ctor_get(v_s_718_, 1);
v_endExclusive_722_ = lean_ctor_get(v_s_718_, 2);
v___x_723_ = lean_nat_add(v_startInclusive_721_, v_pos_719_);
v___x_724_ = lean_unsigned_to_nat(0u);
v___x_725_ = lean_nat_sub(v_endExclusive_722_, v___x_723_);
v_decide_726_ = lean_nat_dec_eq(v___x_724_, v___x_725_);
lean_dec(v___x_725_);
if (v_decide_726_ == 0)
{
uint32_t v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_727_ = lean_string_utf8_get_fast(v_str_720_, v___x_723_);
v___x_728_ = lean_box_uint32(v___x_727_);
lean_inc_ref(v_p_717_);
v___x_729_ = lean_apply_1(v_p_717_, v___x_728_);
v___x_730_ = lean_unbox(v___x_729_);
if (v___x_730_ == 0)
{
lean_dec(v___x_723_);
lean_dec_ref(v_p_717_);
return v_pos_719_;
}
else
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_731_ = lean_string_utf8_next_fast(v_str_720_, v___x_723_);
v___x_732_ = lean_nat_sub(v___x_731_, v___x_723_);
lean_dec(v___x_723_);
v___x_733_ = lean_nat_add(v_pos_719_, v___x_732_);
lean_dec(v___x_732_);
v___x_734_ = lean_unsigned_to_nat(1u);
v___x_735_ = lean_nat_add(v_pos_719_, v___x_734_);
v___x_736_ = lean_nat_dec_le(v___x_735_, v___x_733_);
lean_dec(v___x_735_);
if (v___x_736_ == 0)
{
lean_dec(v___x_733_);
lean_dec_ref(v_p_717_);
return v_pos_719_;
}
else
{
lean_dec(v_pos_719_);
v_pos_719_ = v___x_733_;
goto _start;
}
}
}
else
{
lean_dec(v___x_723_);
lean_dec_ref(v_p_717_);
return v_pos_719_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0___boxed(lean_object* v_p_738_, lean_object* v_s_739_, lean_object* v_pos_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0(v_p_738_, v_s_739_, v_pos_740_);
lean_dec_ref(v_s_739_);
return v_res_741_;
}
}
LEAN_EXPORT uint8_t lean_substring_all(lean_object* v_s_742_, lean_object* v_p_743_){
_start:
{
lean_object* v___y_745_; lean_object* v_startInclusive_746_; lean_object* v_endExclusive_747_; lean_object* v_str_757_; lean_object* v_startPos_758_; lean_object* v_stopPos_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_769_; 
v_str_757_ = lean_ctor_get(v_s_742_, 0);
v_startPos_758_ = lean_ctor_get(v_s_742_, 1);
v_stopPos_759_ = lean_ctor_get(v_s_742_, 2);
v_isSharedCheck_769_ = !lean_is_exclusive(v_s_742_);
if (v_isSharedCheck_769_ == 0)
{
v___x_761_ = v_s_742_;
v_isShared_762_ = v_isSharedCheck_769_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_stopPos_759_);
lean_inc(v_startPos_758_);
lean_inc(v_str_757_);
lean_dec(v_s_742_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_769_;
goto v_resetjp_760_;
}
v___jp_744_:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v_decide_751_; 
v___x_748_ = lean_unsigned_to_nat(0u);
v___x_749_ = l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0(v_p_743_, v___y_745_, v___x_748_);
lean_dec_ref(v___y_745_);
v___x_750_ = lean_nat_sub(v_endExclusive_747_, v_startInclusive_746_);
lean_dec(v_startInclusive_746_);
lean_dec(v_endExclusive_747_);
v_decide_751_ = lean_nat_dec_eq(v___x_749_, v___x_750_);
lean_dec(v___x_750_);
lean_dec(v___x_749_);
return v_decide_751_;
}
v___jp_752_:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v_startInclusive_755_; lean_object* v_endExclusive_756_; 
v___x_753_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_754_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_753_);
v_startInclusive_755_ = lean_ctor_get(v___x_754_, 1);
lean_inc(v_startInclusive_755_);
v_endExclusive_756_ = lean_ctor_get(v___x_754_, 2);
lean_inc(v_endExclusive_756_);
v___y_745_ = v___x_754_;
v_startInclusive_746_ = v_startInclusive_755_;
v_endExclusive_747_ = v_endExclusive_756_;
goto v___jp_744_;
}
v_resetjp_760_:
{
uint8_t v___x_763_; 
v___x_763_ = lean_string_is_valid_pos(v_str_757_, v_startPos_758_);
if (v___x_763_ == 0)
{
lean_del_object(v___x_761_);
lean_dec(v_stopPos_759_);
lean_dec(v_startPos_758_);
lean_dec_ref(v_str_757_);
goto v___jp_752_;
}
else
{
uint8_t v___x_764_; 
v___x_764_ = lean_string_is_valid_pos(v_str_757_, v_stopPos_759_);
if (v___x_764_ == 0)
{
lean_del_object(v___x_761_);
lean_dec(v_stopPos_759_);
lean_dec(v_startPos_758_);
lean_dec_ref(v_str_757_);
goto v___jp_752_;
}
else
{
uint8_t v___x_765_; 
v___x_765_ = lean_nat_dec_le(v_startPos_758_, v_stopPos_759_);
if (v___x_765_ == 0)
{
lean_del_object(v___x_761_);
lean_dec(v_stopPos_759_);
lean_dec(v_startPos_758_);
lean_dec_ref(v_str_757_);
goto v___jp_752_;
}
else
{
lean_object* v___x_767_; 
lean_inc(v_stopPos_759_);
lean_inc(v_startPos_758_);
if (v_isShared_762_ == 0)
{
v___x_767_ = v___x_761_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_str_757_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v_startPos_758_);
lean_ctor_set(v_reuseFailAlloc_768_, 2, v_stopPos_759_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
v___y_745_ = v___x_767_;
v_startInclusive_746_ = v_startPos_758_;
v_endExclusive_747_ = v_stopPos_759_;
goto v___jp_744_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_allImpl___boxed(lean_object* v_s_770_, lean_object* v_p_771_){
_start:
{
uint8_t v_res_772_; lean_object* v_r_773_; 
v_res_772_ = lean_substring_all(v_s_770_, v_p_771_);
v_r_773_ = lean_box(v_res_772_);
return v_r_773_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_contains___lam__0(uint32_t v_c_774_, uint32_t v_a_775_){
_start:
{
uint8_t v___x_776_; 
v___x_776_ = lean_uint32_dec_eq(v_a_775_, v_c_774_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_contains___lam__0___boxed(lean_object* v_c_777_, lean_object* v_a_778_){
_start:
{
uint32_t v_c_boxed_779_; uint32_t v_a_boxed_780_; uint8_t v_res_781_; lean_object* v_r_782_; 
v_c_boxed_779_ = lean_unbox_uint32(v_c_777_);
lean_dec(v_c_777_);
v_a_boxed_780_ = lean_unbox_uint32(v_a_778_);
lean_dec(v_a_778_);
v_res_781_ = l_Substring_Raw_contains___lam__0(v_c_boxed_779_, v_a_boxed_780_);
v_r_782_ = lean_box(v_res_781_);
return v_r_782_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_contains(lean_object* v_s_783_, uint32_t v_c_784_){
_start:
{
lean_object* v___x_785_; lean_object* v___f_786_; lean_object* v___x_787_; lean_object* v_str_788_; lean_object* v_startPos_789_; lean_object* v_stopPos_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_808_; 
v___x_785_ = lean_box_uint32(v_c_784_);
v___f_786_ = lean_alloc_closure((void*)(l_Substring_Raw_contains___lam__0___boxed), 2, 1);
lean_closure_set(v___f_786_, 0, v___x_785_);
lean_inc_ref(v___f_786_);
v___x_787_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___f_786_);
v_str_788_ = lean_ctor_get(v_s_783_, 0);
v_startPos_789_ = lean_ctor_get(v_s_783_, 1);
v_stopPos_790_ = lean_ctor_get(v_s_783_, 2);
v_isSharedCheck_808_ = !lean_is_exclusive(v_s_783_);
if (v_isSharedCheck_808_ == 0)
{
v___x_792_ = v_s_783_;
v_isShared_793_ = v_isSharedCheck_808_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_stopPos_790_);
lean_inc(v_startPos_789_);
lean_inc(v_str_788_);
lean_dec(v_s_783_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_808_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_794_; lean_object* v___f_795_; lean_object* v___x_796_; uint8_t v___x_801_; 
v___x_794_ = l_String_instInhabitedSlice;
v___f_795_ = lean_alloc_closure((void*)(l_Substring_Raw_any___lam__0), 8, 1);
lean_closure_set(v___f_795_, 0, v___x_787_);
v___x_796_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_796_, 0, lean_box(0));
lean_closure_set(v___x_796_, 1, v___f_786_);
v___x_801_ = lean_string_is_valid_pos(v_str_788_, v_startPos_789_);
if (v___x_801_ == 0)
{
lean_del_object(v___x_792_);
lean_dec(v_stopPos_790_);
lean_dec(v_startPos_789_);
lean_dec_ref(v_str_788_);
goto v___jp_797_;
}
else
{
uint8_t v___x_802_; 
v___x_802_ = lean_string_is_valid_pos(v_str_788_, v_stopPos_790_);
if (v___x_802_ == 0)
{
lean_del_object(v___x_792_);
lean_dec(v_stopPos_790_);
lean_dec(v_startPos_789_);
lean_dec_ref(v_str_788_);
goto v___jp_797_;
}
else
{
uint8_t v___x_803_; 
v___x_803_ = lean_nat_dec_le(v_startPos_789_, v_stopPos_790_);
if (v___x_803_ == 0)
{
lean_del_object(v___x_792_);
lean_dec(v_stopPos_790_);
lean_dec(v_startPos_789_);
lean_dec_ref(v_str_788_);
goto v___jp_797_;
}
else
{
lean_object* v___x_805_; 
if (v_isShared_793_ == 0)
{
v___x_805_ = v___x_792_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_str_788_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_startPos_789_);
lean_ctor_set(v_reuseFailAlloc_807_, 2, v_stopPos_790_);
v___x_805_ = v_reuseFailAlloc_807_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
uint8_t v___x_806_; 
v___x_806_ = l_String_Slice_contains___redArg(v___f_795_, v___x_805_, v___x_796_);
return v___x_806_;
}
}
}
}
v___jp_797_:
{
lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v___x_800_; 
v___x_798_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_799_ = l_panic___redArg(v___x_794_, v___x_798_);
v___x_800_ = l_String_Slice_contains___redArg(v___f_795_, v___x_799_, v___x_796_);
return v___x_800_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_contains___boxed(lean_object* v_s_809_, lean_object* v_c_810_){
_start:
{
uint32_t v_c_boxed_811_; uint8_t v_res_812_; lean_object* v_r_813_; 
v_c_boxed_811_ = lean_unbox_uint32(v_c_810_);
lean_dec(v_c_810_);
v_res_812_ = l_Substring_Raw_contains(v_s_809_, v_c_boxed_811_);
v_r_813_ = lean_box(v_res_812_);
return v_r_813_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux(lean_object* v_s_814_, lean_object* v_stopPos_815_, lean_object* v_p_816_, lean_object* v_i_817_){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; uint8_t v___x_820_; 
v___x_818_ = lean_unsigned_to_nat(1u);
v___x_819_ = lean_nat_add(v_i_817_, v___x_818_);
v___x_820_ = lean_nat_dec_le(v___x_819_, v_stopPos_815_);
lean_dec(v___x_819_);
if (v___x_820_ == 0)
{
lean_dec_ref(v_p_816_);
return v_i_817_;
}
else
{
uint32_t v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; uint8_t v___x_824_; 
v___x_821_ = lean_string_utf8_get(v_s_814_, v_i_817_);
v___x_822_ = lean_box_uint32(v___x_821_);
lean_inc_ref(v_p_816_);
v___x_823_ = lean_apply_1(v_p_816_, v___x_822_);
v___x_824_ = lean_unbox(v___x_823_);
if (v___x_824_ == 0)
{
lean_dec_ref(v_p_816_);
return v_i_817_;
}
else
{
lean_object* v___x_825_; 
v___x_825_ = lean_string_utf8_next(v_s_814_, v_i_817_);
lean_dec(v_i_817_);
v_i_817_ = v___x_825_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___boxed(lean_object* v_s_827_, lean_object* v_stopPos_828_, lean_object* v_p_829_, lean_object* v_i_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Substring_Raw_takeWhileAux(v_s_827_, v_stopPos_828_, v_p_829_, v_i_830_);
lean_dec(v_stopPos_828_);
lean_dec_ref(v_s_827_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhile(lean_object* v_x_832_, lean_object* v_x_833_){
_start:
{
lean_object* v_str_834_; lean_object* v_startPos_835_; lean_object* v_stopPos_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_844_; 
v_str_834_ = lean_ctor_get(v_x_832_, 0);
v_startPos_835_ = lean_ctor_get(v_x_832_, 1);
v_stopPos_836_ = lean_ctor_get(v_x_832_, 2);
v_isSharedCheck_844_ = !lean_is_exclusive(v_x_832_);
if (v_isSharedCheck_844_ == 0)
{
v___x_838_ = v_x_832_;
v_isShared_839_ = v_isSharedCheck_844_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_stopPos_836_);
lean_inc(v_startPos_835_);
lean_inc(v_str_834_);
lean_dec(v_x_832_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_844_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v_e_840_; lean_object* v___x_842_; 
lean_inc(v_startPos_835_);
v_e_840_ = l_Substring_Raw_takeWhileAux(v_str_834_, v_stopPos_836_, v_x_833_, v_startPos_835_);
lean_dec(v_stopPos_836_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 2, v_e_840_);
v___x_842_ = v___x_838_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_str_834_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v_startPos_835_);
lean_ctor_set(v_reuseFailAlloc_843_, 2, v_e_840_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(lean_object* v_a_845_, lean_object* v_s_846_, lean_object* v_stopPos_847_, lean_object* v_i_848_){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; uint8_t v___x_851_; 
v___x_849_ = lean_unsigned_to_nat(1u);
v___x_850_ = lean_nat_add(v_i_848_, v___x_849_);
v___x_851_ = lean_nat_dec_le(v___x_850_, v_stopPos_847_);
lean_dec(v___x_850_);
if (v___x_851_ == 0)
{
lean_dec_ref(v_a_845_);
return v_i_848_;
}
else
{
uint32_t v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; uint8_t v___x_855_; 
v___x_852_ = lean_string_utf8_get(v_s_846_, v_i_848_);
v___x_853_ = lean_box_uint32(v___x_852_);
lean_inc_ref(v_a_845_);
v___x_854_ = lean_apply_1(v_a_845_, v___x_853_);
v___x_855_ = lean_unbox(v___x_854_);
if (v___x_855_ == 0)
{
lean_dec_ref(v_a_845_);
return v_i_848_;
}
else
{
lean_object* v___x_856_; 
v___x_856_ = lean_string_utf8_next(v_s_846_, v_i_848_);
lean_dec(v_i_848_);
v_i_848_ = v___x_856_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0___boxed(lean_object* v_a_858_, lean_object* v_s_859_, lean_object* v_stopPos_860_, lean_object* v_i_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(v_a_858_, v_s_859_, v_stopPos_860_, v_i_861_);
lean_dec(v_stopPos_860_);
lean_dec_ref(v_s_859_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* lean_substring_takewhile(lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
lean_object* v_str_865_; lean_object* v_startPos_866_; lean_object* v_stopPos_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_875_; 
v_str_865_ = lean_ctor_get(v_a_863_, 0);
v_startPos_866_ = lean_ctor_get(v_a_863_, 1);
v_stopPos_867_ = lean_ctor_get(v_a_863_, 2);
v_isSharedCheck_875_ = !lean_is_exclusive(v_a_863_);
if (v_isSharedCheck_875_ == 0)
{
v___x_869_ = v_a_863_;
v_isShared_870_ = v_isSharedCheck_875_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_stopPos_867_);
lean_inc(v_startPos_866_);
lean_inc(v_str_865_);
lean_dec(v_a_863_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_875_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v_e_871_; lean_object* v___x_873_; 
lean_inc(v_startPos_866_);
v_e_871_ = l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(v_a_864_, v_str_865_, v_stopPos_867_, v_startPos_866_);
lean_dec(v_stopPos_867_);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 2, v_e_871_);
v___x_873_ = v___x_869_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_str_865_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v_startPos_866_);
lean_ctor_set(v_reuseFailAlloc_874_, 2, v_e_871_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropWhile(lean_object* v_x_876_, lean_object* v_x_877_){
_start:
{
lean_object* v_str_878_; lean_object* v_startPos_879_; lean_object* v_stopPos_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_888_; 
v_str_878_ = lean_ctor_get(v_x_876_, 0);
v_startPos_879_ = lean_ctor_get(v_x_876_, 1);
v_stopPos_880_ = lean_ctor_get(v_x_876_, 2);
v_isSharedCheck_888_ = !lean_is_exclusive(v_x_876_);
if (v_isSharedCheck_888_ == 0)
{
v___x_882_ = v_x_876_;
v_isShared_883_ = v_isSharedCheck_888_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_stopPos_880_);
lean_inc(v_startPos_879_);
lean_inc(v_str_878_);
lean_dec(v_x_876_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_888_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v_b_884_; lean_object* v___x_886_; 
v_b_884_ = l_Substring_Raw_takeWhileAux(v_str_878_, v_stopPos_880_, v_x_877_, v_startPos_879_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 1, v_b_884_);
v___x_886_ = v___x_882_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_str_878_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_b_884_);
lean_ctor_set(v_reuseFailAlloc_887_, 2, v_stopPos_880_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux(lean_object* v_s_889_, lean_object* v_begPos_890_, lean_object* v_p_891_, lean_object* v_i_892_){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_893_ = lean_unsigned_to_nat(1u);
v___x_894_ = lean_nat_add(v_begPos_890_, v___x_893_);
v___x_895_ = lean_nat_dec_le(v___x_894_, v_i_892_);
lean_dec(v___x_894_);
if (v___x_895_ == 0)
{
lean_dec_ref(v_p_891_);
return v_i_892_;
}
else
{
lean_object* v_i_x27_896_; uint32_t v_c_897_; lean_object* v___x_898_; lean_object* v___x_899_; uint8_t v___x_900_; 
v_i_x27_896_ = lean_string_utf8_prev(v_s_889_, v_i_892_);
v_c_897_ = lean_string_utf8_get(v_s_889_, v_i_x27_896_);
v___x_898_ = lean_box_uint32(v_c_897_);
lean_inc_ref(v_p_891_);
v___x_899_ = lean_apply_1(v_p_891_, v___x_898_);
v___x_900_ = lean_unbox(v___x_899_);
if (v___x_900_ == 0)
{
lean_dec(v_i_x27_896_);
lean_dec_ref(v_p_891_);
return v_i_892_;
}
else
{
lean_dec(v_i_892_);
v_i_892_ = v_i_x27_896_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux___boxed(lean_object* v_s_902_, lean_object* v_begPos_903_, lean_object* v_p_904_, lean_object* v_i_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Substring_Raw_takeRightWhileAux(v_s_902_, v_begPos_903_, v_p_904_, v_i_905_);
lean_dec(v_begPos_903_);
lean_dec_ref(v_s_902_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhile(lean_object* v_x_907_, lean_object* v_x_908_){
_start:
{
lean_object* v_str_909_; lean_object* v_startPos_910_; lean_object* v_stopPos_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_919_; 
v_str_909_ = lean_ctor_get(v_x_907_, 0);
v_startPos_910_ = lean_ctor_get(v_x_907_, 1);
v_stopPos_911_ = lean_ctor_get(v_x_907_, 2);
v_isSharedCheck_919_ = !lean_is_exclusive(v_x_907_);
if (v_isSharedCheck_919_ == 0)
{
v___x_913_ = v_x_907_;
v_isShared_914_ = v_isSharedCheck_919_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_stopPos_911_);
lean_inc(v_startPos_910_);
lean_inc(v_str_909_);
lean_dec(v_x_907_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_919_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v_b_915_; lean_object* v___x_917_; 
lean_inc(v_stopPos_911_);
v_b_915_ = l_Substring_Raw_takeRightWhileAux(v_str_909_, v_startPos_910_, v_x_908_, v_stopPos_911_);
lean_dec(v_startPos_910_);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 1, v_b_915_);
v___x_917_ = v___x_913_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_str_909_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_b_915_);
lean_ctor_set(v_reuseFailAlloc_918_, 2, v_stopPos_911_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropRightWhile(lean_object* v_x_920_, lean_object* v_x_921_){
_start:
{
lean_object* v_str_922_; lean_object* v_startPos_923_; lean_object* v_stopPos_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_932_; 
v_str_922_ = lean_ctor_get(v_x_920_, 0);
v_startPos_923_ = lean_ctor_get(v_x_920_, 1);
v_stopPos_924_ = lean_ctor_get(v_x_920_, 2);
v_isSharedCheck_932_ = !lean_is_exclusive(v_x_920_);
if (v_isSharedCheck_932_ == 0)
{
v___x_926_ = v_x_920_;
v_isShared_927_ = v_isSharedCheck_932_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_stopPos_924_);
lean_inc(v_startPos_923_);
lean_inc(v_str_922_);
lean_dec(v_x_920_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_932_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v_e_928_; lean_object* v___x_930_; 
v_e_928_ = l_Substring_Raw_takeRightWhileAux(v_str_922_, v_startPos_923_, v_x_921_, v_stopPos_924_);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 2, v_e_928_);
v___x_930_ = v___x_926_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_str_922_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v_startPos_923_);
lean_ctor_set(v_reuseFailAlloc_931_, 2, v_e_928_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_trimLeft(lean_object* v_s_934_){
_start:
{
lean_object* v_str_935_; lean_object* v_startPos_936_; lean_object* v_stopPos_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_946_; 
v_str_935_ = lean_ctor_get(v_s_934_, 0);
v_startPos_936_ = lean_ctor_get(v_s_934_, 1);
v_stopPos_937_ = lean_ctor_get(v_s_934_, 2);
v_isSharedCheck_946_ = !lean_is_exclusive(v_s_934_);
if (v_isSharedCheck_946_ == 0)
{
v___x_939_ = v_s_934_;
v_isShared_940_ = v_isSharedCheck_946_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_stopPos_937_);
lean_inc(v_startPos_936_);
lean_inc(v_str_935_);
lean_dec(v_s_934_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_946_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; lean_object* v_b_942_; lean_object* v___x_944_; 
v___x_941_ = ((lean_object*)(l_Substring_Raw_trimLeft___closed__0));
v_b_942_ = l_Substring_Raw_takeWhileAux(v_str_935_, v_stopPos_937_, v___x_941_, v_startPos_936_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 1, v_b_942_);
v___x_944_ = v___x_939_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_str_935_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v_b_942_);
lean_ctor_set(v_reuseFailAlloc_945_, 2, v_stopPos_937_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_trimRight(lean_object* v_s_947_){
_start:
{
lean_object* v_str_948_; lean_object* v_startPos_949_; lean_object* v_stopPos_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_959_; 
v_str_948_ = lean_ctor_get(v_s_947_, 0);
v_startPos_949_ = lean_ctor_get(v_s_947_, 1);
v_stopPos_950_ = lean_ctor_get(v_s_947_, 2);
v_isSharedCheck_959_ = !lean_is_exclusive(v_s_947_);
if (v_isSharedCheck_959_ == 0)
{
v___x_952_ = v_s_947_;
v_isShared_953_ = v_isSharedCheck_959_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_stopPos_950_);
lean_inc(v_startPos_949_);
lean_inc(v_str_948_);
lean_dec(v_s_947_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_959_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_954_; lean_object* v_e_955_; lean_object* v___x_957_; 
v___x_954_ = ((lean_object*)(l_Substring_Raw_trimLeft___closed__0));
v_e_955_ = l_Substring_Raw_takeRightWhileAux(v_str_948_, v_startPos_949_, v___x_954_, v_stopPos_950_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 2, v_e_955_);
v___x_957_ = v___x_952_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_str_948_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_startPos_949_);
lean_ctor_set(v_reuseFailAlloc_958_, 2, v_e_955_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_trim(lean_object* v_x_960_){
_start:
{
lean_object* v_str_961_; lean_object* v_startPos_962_; lean_object* v_stopPos_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_973_; 
v_str_961_ = lean_ctor_get(v_x_960_, 0);
v_startPos_962_ = lean_ctor_get(v_x_960_, 1);
v_stopPos_963_ = lean_ctor_get(v_x_960_, 2);
v_isSharedCheck_973_ = !lean_is_exclusive(v_x_960_);
if (v_isSharedCheck_973_ == 0)
{
v___x_965_ = v_x_960_;
v_isShared_966_ = v_isSharedCheck_973_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_stopPos_963_);
lean_inc(v_startPos_962_);
lean_inc(v_str_961_);
lean_dec(v_x_960_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_973_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_967_; lean_object* v_b_968_; lean_object* v_e_969_; lean_object* v___x_971_; 
v___x_967_ = ((lean_object*)(l_Substring_Raw_trimLeft___closed__0));
v_b_968_ = l_Substring_Raw_takeWhileAux(v_str_961_, v_stopPos_963_, v___x_967_, v_startPos_962_);
v_e_969_ = l_Substring_Raw_takeRightWhileAux(v_str_961_, v_b_968_, v___x_967_, v_stopPos_963_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 2, v_e_969_);
lean_ctor_set(v___x_965_, 1, v_b_968_);
v___x_971_ = v___x_965_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_str_961_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v_b_968_);
lean_ctor_set(v_reuseFailAlloc_972_, 2, v_e_969_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___lam__0(lean_object* v___y_974_, uint8_t v___x_975_, uint8_t v___x_976_, lean_object* v_it_977_, lean_object* v_acc_978_, lean_object* v_hP_979_, lean_object* v_recur_980_){
_start:
{
lean_object* v_str_981_; lean_object* v_startInclusive_982_; lean_object* v_endExclusive_983_; lean_object* v___x_984_; uint8_t v_decide_985_; 
v_str_981_ = lean_ctor_get(v___y_974_, 0);
v_startInclusive_982_ = lean_ctor_get(v___y_974_, 1);
v_endExclusive_983_ = lean_ctor_get(v___y_974_, 2);
v___x_984_ = lean_nat_sub(v_endExclusive_983_, v_startInclusive_982_);
v_decide_985_ = lean_nat_dec_eq(v_it_977_, v___x_984_);
lean_dec(v___x_984_);
if (v_decide_985_ == 0)
{
lean_object* v_snd_986_; lean_object* v_snd_987_; lean_object* v_fst_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_1048_; 
v_snd_986_ = lean_ctor_get(v_acc_978_, 1);
lean_inc(v_snd_986_);
v_snd_987_ = lean_ctor_get(v_snd_986_, 1);
lean_inc(v_snd_987_);
v_fst_988_ = lean_ctor_get(v_acc_978_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_acc_978_);
if (v_isSharedCheck_1048_ == 0)
{
lean_object* v_unused_1049_; 
v_unused_1049_ = lean_ctor_get(v_acc_978_, 1);
lean_dec(v_unused_1049_);
v___x_990_ = v_acc_978_;
v_isShared_991_ = v_isSharedCheck_1048_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_fst_988_);
lean_dec(v_acc_978_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_1048_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v_fst_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1046_; 
v_fst_992_ = lean_ctor_get(v_snd_986_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_snd_986_);
if (v_isSharedCheck_1046_ == 0)
{
lean_object* v_unused_1047_; 
v_unused_1047_ = lean_ctor_get(v_snd_986_, 1);
lean_dec(v_unused_1047_);
v___x_994_ = v_snd_986_;
v_isShared_995_ = v_isSharedCheck_1046_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_fst_992_);
lean_dec(v_snd_986_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1046_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v_snd_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1044_; 
v_snd_996_ = lean_ctor_get(v_snd_987_, 1);
v_isSharedCheck_1044_ = !lean_is_exclusive(v_snd_987_);
if (v_isSharedCheck_1044_ == 0)
{
lean_object* v_unused_1045_; 
v_unused_1045_ = lean_ctor_get(v_snd_987_, 0);
lean_dec(v_unused_1045_);
v___x_998_ = v_snd_987_;
v_isShared_999_ = v_isSharedCheck_1044_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_snd_996_);
lean_dec(v_snd_987_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1044_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1000_; uint32_t v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; uint8_t v___y_1005_; uint8_t v___y_1006_; uint8_t v___y_1024_; uint8_t v___y_1025_; uint8_t v___y_1030_; uint8_t v___y_1031_; uint8_t v___y_1036_; uint32_t v___x_1040_; uint8_t v___x_1041_; 
v___x_1000_ = lean_nat_add(v_startInclusive_982_, v_it_977_);
v___x_1001_ = lean_string_utf8_get_fast(v_str_981_, v___x_1000_);
v___x_1002_ = lean_string_utf8_next_fast(v_str_981_, v___x_1000_);
lean_dec(v___x_1000_);
v___x_1003_ = lean_nat_sub(v___x_1002_, v_startInclusive_982_);
v___x_1040_ = 48;
v___x_1041_ = lean_uint32_dec_le(v___x_1040_, v___x_1001_);
if (v___x_1041_ == 0)
{
v___y_1036_ = v___x_1041_;
goto v___jp_1035_;
}
else
{
uint32_t v___x_1042_; uint8_t v___x_1043_; 
v___x_1042_ = 57;
v___x_1043_ = lean_uint32_dec_le(v___x_1001_, v___x_1042_);
v___y_1036_ = v___x_1043_;
goto v___jp_1035_;
}
v___jp_1004_:
{
uint32_t v___x_1007_; uint8_t v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1007_ = 95;
v___x_1008_ = lean_uint32_dec_eq(v___x_1001_, v___x_1007_);
v___x_1009_ = lean_box(v___y_1005_);
v___x_1010_ = lean_box(v___y_1006_);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 1, v___x_1010_);
lean_ctor_set(v___x_998_, 0, v___x_1009_);
v___x_1012_ = v___x_998_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1009_);
lean_ctor_set(v_reuseFailAlloc_1022_, 1, v___x_1010_);
v___x_1012_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1013_ = lean_box(v___x_1008_);
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 1, v___x_1012_);
lean_ctor_set(v___x_994_, 0, v___x_1013_);
v___x_1015_ = v___x_994_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1013_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v___x_1012_);
v___x_1015_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
lean_object* v___x_1016_; lean_object* v___x_1018_; 
v___x_1016_ = lean_box(v___x_975_);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 1, v___x_1015_);
lean_ctor_set(v___x_990_, 0, v___x_1016_);
v___x_1018_ = v___x_990_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1016_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v___x_1015_);
v___x_1018_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_apply_4(v_recur_980_, v___x_1003_, v___x_1018_, lean_box(0), lean_box(0));
return v___x_1019_;
}
}
}
}
v___jp_1023_:
{
uint8_t v___x_1026_; 
v___x_1026_ = lean_unbox(v_fst_992_);
lean_dec(v_fst_992_);
if (v___x_1026_ == 0)
{
v___y_1005_ = v___y_1024_;
v___y_1006_ = v___y_1025_;
goto v___jp_1004_;
}
else
{
uint32_t v___x_1027_; uint8_t v___x_1028_; 
v___x_1027_ = 95;
v___x_1028_ = lean_uint32_dec_eq(v___x_1001_, v___x_1027_);
if (v___x_1028_ == 0)
{
v___y_1005_ = v___y_1024_;
v___y_1006_ = v___y_1025_;
goto v___jp_1004_;
}
else
{
v___y_1005_ = v___y_1024_;
v___y_1006_ = v___x_975_;
goto v___jp_1004_;
}
}
}
v___jp_1029_:
{
uint8_t v___x_1032_; 
v___x_1032_ = lean_unbox(v_fst_988_);
lean_dec(v_fst_988_);
if (v___x_1032_ == 0)
{
v___y_1024_ = v___y_1030_;
v___y_1025_ = v___y_1031_;
goto v___jp_1023_;
}
else
{
uint32_t v___x_1033_; uint8_t v___x_1034_; 
v___x_1033_ = 95;
v___x_1034_ = lean_uint32_dec_eq(v___x_1001_, v___x_1033_);
if (v___x_1034_ == 0)
{
v___y_1024_ = v___y_1030_;
v___y_1025_ = v___y_1031_;
goto v___jp_1023_;
}
else
{
lean_dec(v_fst_992_);
v___y_1005_ = v___y_1030_;
v___y_1006_ = v___x_975_;
goto v___jp_1004_;
}
}
}
v___jp_1035_:
{
uint8_t v___x_1037_; 
v___x_1037_ = lean_unbox(v_snd_996_);
lean_dec(v_snd_996_);
if (v___x_1037_ == 0)
{
lean_dec(v_fst_992_);
lean_dec(v_fst_988_);
v___y_1005_ = v___y_1036_;
v___y_1006_ = v___x_975_;
goto v___jp_1004_;
}
else
{
if (v___y_1036_ == 0)
{
uint32_t v___x_1038_; uint8_t v___x_1039_; 
v___x_1038_ = 95;
v___x_1039_ = lean_uint32_dec_eq(v___x_1001_, v___x_1038_);
if (v___x_1039_ == 0)
{
lean_dec(v_fst_992_);
lean_dec(v_fst_988_);
v___y_1005_ = v___y_1036_;
v___y_1006_ = v___x_975_;
goto v___jp_1004_;
}
else
{
v___y_1030_ = v___y_1036_;
v___y_1031_ = v___x_1039_;
goto v___jp_1029_;
}
}
else
{
v___y_1030_ = v___y_1036_;
v___y_1031_ = v___x_976_;
goto v___jp_1029_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_recur_980_);
return v_acc_978_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___lam__0___boxed(lean_object* v___y_1050_, lean_object* v___x_1051_, lean_object* v___x_1052_, lean_object* v_it_1053_, lean_object* v_acc_1054_, lean_object* v_hP_1055_, lean_object* v_recur_1056_){
_start:
{
uint8_t v___x_790__boxed_1057_; uint8_t v___x_791__boxed_1058_; lean_object* v_res_1059_; 
v___x_790__boxed_1057_ = lean_unbox(v___x_1051_);
v___x_791__boxed_1058_ = lean_unbox(v___x_1052_);
v_res_1059_ = l_Substring_Raw_isNat___lam__0(v___y_1050_, v___x_790__boxed_1057_, v___x_791__boxed_1058_, v_it_1053_, v_acc_1054_, v_hP_1055_, v_recur_1056_);
lean_dec(v_it_1053_);
lean_dec_ref(v___y_1050_);
return v_res_1059_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_isNat(lean_object* v_s_1060_){
_start:
{
lean_object* v_str_1061_; lean_object* v_startPos_1062_; lean_object* v_stopPos_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1101_; 
v_str_1061_ = lean_ctor_get(v_s_1060_, 0);
v_startPos_1062_ = lean_ctor_get(v_s_1060_, 1);
v_stopPos_1063_ = lean_ctor_get(v_s_1060_, 2);
v_isSharedCheck_1101_ = !lean_is_exclusive(v_s_1060_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1065_ = v_s_1060_;
v_isShared_1066_ = v_isSharedCheck_1101_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_stopPos_1063_);
lean_inc(v_startPos_1062_);
lean_inc(v_str_1061_);
lean_dec(v_s_1060_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1101_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; uint8_t v___x_1069_; 
v___x_1067_ = lean_nat_sub(v_stopPos_1063_, v_startPos_1062_);
v___x_1068_ = lean_unsigned_to_nat(0u);
v___x_1069_ = lean_nat_dec_eq(v___x_1067_, v___x_1068_);
lean_dec(v___x_1067_);
if (v___x_1069_ == 0)
{
uint8_t v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___y_1079_; lean_object* v___x_1090_; uint8_t v___x_1094_; 
v___x_1070_ = 1;
v___x_1071_ = lean_box(v___x_1069_);
v___x_1072_ = lean_box(v___x_1070_);
v___x_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1071_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = lean_box(v___x_1069_);
v___x_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
lean_ctor_set(v___x_1075_, 1, v___x_1073_);
v___x_1076_ = lean_box(v___x_1070_);
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
lean_ctor_set(v___x_1077_, 1, v___x_1075_);
v___x_1090_ = l_String_instInhabitedSlice;
v___x_1094_ = lean_string_is_valid_pos(v_str_1061_, v_startPos_1062_);
if (v___x_1094_ == 0)
{
lean_del_object(v___x_1065_);
lean_dec(v_stopPos_1063_);
lean_dec(v_startPos_1062_);
lean_dec_ref(v_str_1061_);
goto v___jp_1091_;
}
else
{
uint8_t v___x_1095_; 
v___x_1095_ = lean_string_is_valid_pos(v_str_1061_, v_stopPos_1063_);
if (v___x_1095_ == 0)
{
lean_del_object(v___x_1065_);
lean_dec(v_stopPos_1063_);
lean_dec(v_startPos_1062_);
lean_dec_ref(v_str_1061_);
goto v___jp_1091_;
}
else
{
uint8_t v___x_1096_; 
v___x_1096_ = lean_nat_dec_le(v_startPos_1062_, v_stopPos_1063_);
if (v___x_1096_ == 0)
{
lean_del_object(v___x_1065_);
lean_dec(v_stopPos_1063_);
lean_dec(v_startPos_1062_);
lean_dec_ref(v_str_1061_);
goto v___jp_1091_;
}
else
{
lean_object* v___x_1098_; 
if (v_isShared_1066_ == 0)
{
v___x_1098_ = v___x_1065_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_str_1061_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v_startPos_1062_);
lean_ctor_set(v_reuseFailAlloc_1099_, 2, v_stopPos_1063_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
v___y_1079_ = v___x_1098_;
goto v___jp_1078_;
}
}
}
}
v___jp_1078_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___f_1082_; lean_object* v___x_1083_; lean_object* v_snd_1084_; lean_object* v_snd_1085_; lean_object* v_snd_1086_; uint8_t v___x_1087_; 
v___x_1080_ = lean_box(v___x_1069_);
v___x_1081_ = lean_box(v___x_1070_);
v___f_1082_ = lean_alloc_closure((void*)(l_Substring_Raw_isNat___lam__0___boxed), 7, 3);
lean_closure_set(v___f_1082_, 0, v___y_1079_);
lean_closure_set(v___f_1082_, 1, v___x_1080_);
lean_closure_set(v___f_1082_, 2, v___x_1081_);
v___x_1083_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1082_, v___x_1068_, v___x_1077_, lean_box(0));
v_snd_1084_ = lean_ctor_get(v___x_1083_, 1);
lean_inc(v_snd_1084_);
lean_dec(v___x_1083_);
v_snd_1085_ = lean_ctor_get(v_snd_1084_, 1);
lean_inc(v_snd_1085_);
lean_dec(v_snd_1084_);
v_snd_1086_ = lean_ctor_get(v_snd_1085_, 1);
v___x_1087_ = lean_unbox(v_snd_1086_);
if (v___x_1087_ == 0)
{
lean_dec(v_snd_1085_);
return v___x_1069_;
}
else
{
lean_object* v_fst_1088_; uint8_t v___x_1089_; 
v_fst_1088_ = lean_ctor_get(v_snd_1085_, 0);
lean_inc(v_fst_1088_);
lean_dec(v_snd_1085_);
v___x_1089_ = lean_unbox(v_fst_1088_);
lean_dec(v_fst_1088_);
return v___x_1089_;
}
}
v___jp_1091_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_1093_ = l_panic___redArg(v___x_1090_, v___x_1092_);
v___y_1079_ = v___x_1093_;
goto v___jp_1078_;
}
}
else
{
uint8_t v___x_1100_; 
lean_del_object(v___x_1065_);
lean_dec(v_stopPos_1063_);
lean_dec(v_startPos_1062_);
lean_dec_ref(v_str_1061_);
v___x_1100_ = 0;
return v___x_1100_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___boxed(lean_object* v_s_1102_){
_start:
{
uint8_t v_res_1103_; lean_object* v_r_1104_; 
v_res_1103_ = l_Substring_Raw_isNat(v_s_1102_);
v_r_1104_ = lean_box(v_res_1103_);
return v_r_1104_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(lean_object* v___y_1105_, lean_object* v_a_1106_, lean_object* v_b_1107_){
_start:
{
lean_object* v_str_1108_; lean_object* v_startInclusive_1109_; lean_object* v_endExclusive_1110_; lean_object* v___x_1111_; uint8_t v_decide_1112_; 
v_str_1108_ = lean_ctor_get(v___y_1105_, 0);
v_startInclusive_1109_ = lean_ctor_get(v___y_1105_, 1);
v_endExclusive_1110_ = lean_ctor_get(v___y_1105_, 2);
v___x_1111_ = lean_nat_sub(v_endExclusive_1110_, v_startInclusive_1109_);
v_decide_1112_ = lean_nat_dec_eq(v_a_1106_, v___x_1111_);
lean_dec(v___x_1111_);
if (v_decide_1112_ == 0)
{
lean_object* v___x_1113_; uint32_t v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; uint32_t v___x_1117_; uint8_t v___x_1118_; 
v___x_1113_ = lean_nat_add(v_startInclusive_1109_, v_a_1106_);
lean_dec(v_a_1106_);
v___x_1114_ = lean_string_utf8_get_fast(v_str_1108_, v___x_1113_);
v___x_1115_ = lean_string_utf8_next_fast(v_str_1108_, v___x_1113_);
lean_dec(v___x_1113_);
v___x_1116_ = lean_nat_sub(v___x_1115_, v_startInclusive_1109_);
v___x_1117_ = 95;
v___x_1118_ = lean_uint32_dec_eq(v___x_1114_, v___x_1117_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1119_ = lean_unsigned_to_nat(10u);
v___x_1120_ = lean_nat_mul(v_b_1107_, v___x_1119_);
lean_dec(v_b_1107_);
v___x_1121_ = lean_uint32_to_nat(v___x_1114_);
v___x_1122_ = lean_unsigned_to_nat(48u);
v___x_1123_ = lean_nat_sub(v___x_1121_, v___x_1122_);
lean_dec(v___x_1121_);
v___x_1124_ = lean_nat_add(v___x_1120_, v___x_1123_);
lean_dec(v___x_1123_);
lean_dec(v___x_1120_);
v_a_1106_ = v___x_1116_;
v_b_1107_ = v___x_1124_;
goto _start;
}
else
{
v_a_1106_ = v___x_1116_;
goto _start;
}
}
else
{
lean_dec(v_a_1106_);
return v_b_1107_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg___boxed(lean_object* v___y_1127_, lean_object* v_a_1128_, lean_object* v_b_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(v___y_1127_, v_a_1128_, v_b_1129_);
lean_dec_ref(v___y_1127_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(lean_object* v___x_1131_, lean_object* v___y_1132_, lean_object* v_a_1133_, lean_object* v_b_1134_){
_start:
{
lean_object* v_str_1135_; lean_object* v_startInclusive_1136_; lean_object* v_endExclusive_1137_; lean_object* v___x_1138_; uint8_t v_decide_1139_; 
v_str_1135_ = lean_ctor_get(v___y_1132_, 0);
v_startInclusive_1136_ = lean_ctor_get(v___y_1132_, 1);
v_endExclusive_1137_ = lean_ctor_get(v___y_1132_, 2);
v___x_1138_ = lean_nat_sub(v_endExclusive_1137_, v_startInclusive_1136_);
v_decide_1139_ = lean_nat_dec_eq(v_a_1133_, v___x_1138_);
lean_dec(v___x_1138_);
if (v_decide_1139_ == 0)
{
lean_object* v_snd_1140_; lean_object* v_snd_1141_; lean_object* v_fst_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1205_; 
v_snd_1140_ = lean_ctor_get(v_b_1134_, 1);
lean_inc(v_snd_1140_);
v_snd_1141_ = lean_ctor_get(v_snd_1140_, 1);
lean_inc(v_snd_1141_);
v_fst_1142_ = lean_ctor_get(v_b_1134_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_b_1134_);
if (v_isSharedCheck_1205_ == 0)
{
lean_object* v_unused_1206_; 
v_unused_1206_ = lean_ctor_get(v_b_1134_, 1);
lean_dec(v_unused_1206_);
v___x_1144_ = v_b_1134_;
v_isShared_1145_ = v_isSharedCheck_1205_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_fst_1142_);
lean_dec(v_b_1134_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1205_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v_fst_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1203_; 
v_fst_1146_ = lean_ctor_get(v_snd_1140_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v_snd_1140_);
if (v_isSharedCheck_1203_ == 0)
{
lean_object* v_unused_1204_; 
v_unused_1204_ = lean_ctor_get(v_snd_1140_, 1);
lean_dec(v_unused_1204_);
v___x_1148_ = v_snd_1140_;
v_isShared_1149_ = v_isSharedCheck_1203_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_fst_1146_);
lean_dec(v_snd_1140_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1203_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v_snd_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1201_; 
v_snd_1150_ = lean_ctor_get(v_snd_1141_, 1);
v_isSharedCheck_1201_ = !lean_is_exclusive(v_snd_1141_);
if (v_isSharedCheck_1201_ == 0)
{
lean_object* v_unused_1202_; 
v_unused_1202_ = lean_ctor_get(v_snd_1141_, 0);
lean_dec(v_unused_1202_);
v___x_1152_ = v_snd_1141_;
v_isShared_1153_ = v_isSharedCheck_1201_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_snd_1150_);
lean_dec(v_snd_1141_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1201_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1154_; uint8_t v___x_1155_; uint8_t v___x_1156_; lean_object* v___x_1157_; uint32_t v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; uint8_t v___y_1162_; uint8_t v___y_1163_; uint8_t v___y_1181_; uint8_t v___y_1182_; uint8_t v___y_1187_; uint8_t v___y_1188_; uint8_t v___y_1193_; uint32_t v___x_1197_; uint8_t v___x_1198_; 
v___x_1154_ = lean_unsigned_to_nat(0u);
v___x_1155_ = lean_nat_dec_eq(v___x_1131_, v___x_1154_);
v___x_1156_ = 1;
v___x_1157_ = lean_nat_add(v_startInclusive_1136_, v_a_1133_);
lean_dec(v_a_1133_);
v___x_1158_ = lean_string_utf8_get_fast(v_str_1135_, v___x_1157_);
v___x_1159_ = lean_string_utf8_next_fast(v_str_1135_, v___x_1157_);
lean_dec(v___x_1157_);
v___x_1160_ = lean_nat_sub(v___x_1159_, v_startInclusive_1136_);
v___x_1197_ = 48;
v___x_1198_ = lean_uint32_dec_le(v___x_1197_, v___x_1158_);
if (v___x_1198_ == 0)
{
v___y_1193_ = v___x_1198_;
goto v___jp_1192_;
}
else
{
uint32_t v___x_1199_; uint8_t v___x_1200_; 
v___x_1199_ = 57;
v___x_1200_ = lean_uint32_dec_le(v___x_1158_, v___x_1199_);
v___y_1193_ = v___x_1200_;
goto v___jp_1192_;
}
v___jp_1161_:
{
uint32_t v___x_1164_; uint8_t v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1164_ = 95;
v___x_1165_ = lean_uint32_dec_eq(v___x_1158_, v___x_1164_);
v___x_1166_ = lean_box(v___y_1162_);
v___x_1167_ = lean_box(v___y_1163_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 1, v___x_1167_);
lean_ctor_set(v___x_1152_, 0, v___x_1166_);
v___x_1169_ = v___x_1152_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
lean_object* v___x_1170_; lean_object* v___x_1172_; 
v___x_1170_ = lean_box(v___x_1165_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 1, v___x_1169_);
lean_ctor_set(v___x_1148_, 0, v___x_1170_);
v___x_1172_ = v___x_1148_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1170_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v___x_1169_);
v___x_1172_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
lean_object* v___x_1173_; lean_object* v___x_1175_; 
v___x_1173_ = lean_box(v___x_1155_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 1, v___x_1172_);
lean_ctor_set(v___x_1144_, 0, v___x_1173_);
v___x_1175_ = v___x_1144_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1173_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v___x_1172_);
v___x_1175_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
v_a_1133_ = v___x_1160_;
v_b_1134_ = v___x_1175_;
goto _start;
}
}
}
}
v___jp_1180_:
{
uint8_t v___x_1183_; 
v___x_1183_ = lean_unbox(v_fst_1146_);
lean_dec(v_fst_1146_);
if (v___x_1183_ == 0)
{
v___y_1162_ = v___y_1181_;
v___y_1163_ = v___y_1182_;
goto v___jp_1161_;
}
else
{
uint32_t v___x_1184_; uint8_t v___x_1185_; 
v___x_1184_ = 95;
v___x_1185_ = lean_uint32_dec_eq(v___x_1158_, v___x_1184_);
if (v___x_1185_ == 0)
{
v___y_1162_ = v___y_1181_;
v___y_1163_ = v___y_1182_;
goto v___jp_1161_;
}
else
{
v___y_1162_ = v___y_1181_;
v___y_1163_ = v___x_1155_;
goto v___jp_1161_;
}
}
}
v___jp_1186_:
{
uint8_t v___x_1189_; 
v___x_1189_ = lean_unbox(v_fst_1142_);
lean_dec(v_fst_1142_);
if (v___x_1189_ == 0)
{
v___y_1181_ = v___y_1187_;
v___y_1182_ = v___y_1188_;
goto v___jp_1180_;
}
else
{
uint32_t v___x_1190_; uint8_t v___x_1191_; 
v___x_1190_ = 95;
v___x_1191_ = lean_uint32_dec_eq(v___x_1158_, v___x_1190_);
if (v___x_1191_ == 0)
{
v___y_1181_ = v___y_1187_;
v___y_1182_ = v___y_1188_;
goto v___jp_1180_;
}
else
{
lean_dec(v_fst_1146_);
v___y_1162_ = v___y_1187_;
v___y_1163_ = v___x_1155_;
goto v___jp_1161_;
}
}
}
v___jp_1192_:
{
uint8_t v___x_1194_; 
v___x_1194_ = lean_unbox(v_snd_1150_);
lean_dec(v_snd_1150_);
if (v___x_1194_ == 0)
{
lean_dec(v_fst_1146_);
lean_dec(v_fst_1142_);
v___y_1162_ = v___y_1193_;
v___y_1163_ = v___x_1155_;
goto v___jp_1161_;
}
else
{
if (v___y_1193_ == 0)
{
uint32_t v___x_1195_; uint8_t v___x_1196_; 
v___x_1195_ = 95;
v___x_1196_ = lean_uint32_dec_eq(v___x_1158_, v___x_1195_);
if (v___x_1196_ == 0)
{
lean_dec(v_fst_1146_);
lean_dec(v_fst_1142_);
v___y_1162_ = v___y_1193_;
v___y_1163_ = v___x_1155_;
goto v___jp_1161_;
}
else
{
v___y_1187_ = v___y_1193_;
v___y_1188_ = v___x_1196_;
goto v___jp_1186_;
}
}
else
{
v___y_1187_ = v___y_1193_;
v___y_1188_ = v___x_1156_;
goto v___jp_1186_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1133_);
return v_b_1134_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg___boxed(lean_object* v___x_1207_, lean_object* v___y_1208_, lean_object* v_a_1209_, lean_object* v_b_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(v___x_1207_, v___y_1208_, v_a_1209_, v_b_1210_);
lean_dec_ref(v___y_1208_);
lean_dec(v___x_1207_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toNat_x3f(lean_object* v_s_1212_){
_start:
{
lean_object* v_str_1213_; lean_object* v_startPos_1214_; lean_object* v_stopPos_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1262_; 
v_str_1213_ = lean_ctor_get(v_s_1212_, 0);
v_startPos_1214_ = lean_ctor_get(v_s_1212_, 1);
v_stopPos_1215_ = lean_ctor_get(v_s_1212_, 2);
v_isSharedCheck_1262_ = !lean_is_exclusive(v_s_1212_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1217_ = v_s_1212_;
v_isShared_1218_ = v_isSharedCheck_1262_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_stopPos_1215_);
lean_inc(v_startPos_1214_);
lean_inc(v_str_1213_);
lean_dec(v_s_1212_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1262_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___y_1222_; uint8_t v___x_1228_; 
v___x_1219_ = lean_nat_sub(v_stopPos_1215_, v_startPos_1214_);
v___x_1220_ = lean_unsigned_to_nat(0u);
v___x_1228_ = lean_nat_dec_eq(v___x_1219_, v___x_1220_);
if (v___x_1228_ == 0)
{
uint8_t v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___y_1238_; uint8_t v___x_1257_; 
v___x_1229_ = 1;
v___x_1230_ = lean_box(v___x_1228_);
v___x_1231_ = lean_box(v___x_1229_);
v___x_1232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1230_);
lean_ctor_set(v___x_1232_, 1, v___x_1231_);
v___x_1233_ = lean_box(v___x_1228_);
v___x_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
lean_ctor_set(v___x_1234_, 1, v___x_1232_);
v___x_1235_ = lean_box(v___x_1229_);
v___x_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1235_);
lean_ctor_set(v___x_1236_, 1, v___x_1234_);
v___x_1257_ = lean_string_is_valid_pos(v_str_1213_, v_startPos_1214_);
if (v___x_1257_ == 0)
{
goto v___jp_1254_;
}
else
{
uint8_t v___x_1258_; 
v___x_1258_ = lean_string_is_valid_pos(v_str_1213_, v_stopPos_1215_);
if (v___x_1258_ == 0)
{
goto v___jp_1254_;
}
else
{
uint8_t v___x_1259_; 
v___x_1259_ = lean_nat_dec_le(v_startPos_1214_, v_stopPos_1215_);
if (v___x_1259_ == 0)
{
goto v___jp_1254_;
}
else
{
lean_object* v___x_1260_; 
lean_inc(v_stopPos_1215_);
lean_inc(v_startPos_1214_);
lean_inc_ref(v_str_1213_);
v___x_1260_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1260_, 0, v_str_1213_);
lean_ctor_set(v___x_1260_, 1, v_startPos_1214_);
lean_ctor_set(v___x_1260_, 2, v_stopPos_1215_);
v___y_1238_ = v___x_1260_;
goto v___jp_1237_;
}
}
}
v___jp_1237_:
{
lean_object* v___x_1239_; lean_object* v_snd_1240_; lean_object* v_snd_1241_; lean_object* v_snd_1242_; uint8_t v___x_1243_; 
v___x_1239_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(v___x_1219_, v___y_1238_, v___x_1220_, v___x_1236_);
lean_dec_ref(v___y_1238_);
lean_dec(v___x_1219_);
v_snd_1240_ = lean_ctor_get(v___x_1239_, 1);
lean_inc(v_snd_1240_);
lean_dec_ref(v___x_1239_);
v_snd_1241_ = lean_ctor_get(v_snd_1240_, 1);
lean_inc(v_snd_1241_);
lean_dec(v_snd_1240_);
v_snd_1242_ = lean_ctor_get(v_snd_1241_, 1);
v___x_1243_ = lean_unbox(v_snd_1242_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; 
lean_dec(v_snd_1241_);
lean_del_object(v___x_1217_);
lean_dec(v_stopPos_1215_);
lean_dec(v_startPos_1214_);
lean_dec_ref(v_str_1213_);
v___x_1244_ = lean_box(0);
return v___x_1244_;
}
else
{
lean_object* v_fst_1245_; uint8_t v___x_1246_; 
v_fst_1245_ = lean_ctor_get(v_snd_1241_, 0);
lean_inc(v_fst_1245_);
lean_dec(v_snd_1241_);
v___x_1246_ = lean_unbox(v_fst_1245_);
lean_dec(v_fst_1245_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; 
lean_del_object(v___x_1217_);
lean_dec(v_stopPos_1215_);
lean_dec(v_startPos_1214_);
lean_dec_ref(v_str_1213_);
v___x_1247_ = lean_box(0);
return v___x_1247_;
}
else
{
uint8_t v___x_1248_; 
v___x_1248_ = lean_string_is_valid_pos(v_str_1213_, v_startPos_1214_);
if (v___x_1248_ == 0)
{
lean_del_object(v___x_1217_);
lean_dec(v_stopPos_1215_);
lean_dec(v_startPos_1214_);
lean_dec_ref(v_str_1213_);
goto v___jp_1225_;
}
else
{
uint8_t v___x_1249_; 
v___x_1249_ = lean_string_is_valid_pos(v_str_1213_, v_stopPos_1215_);
if (v___x_1249_ == 0)
{
lean_del_object(v___x_1217_);
lean_dec(v_stopPos_1215_);
lean_dec(v_startPos_1214_);
lean_dec_ref(v_str_1213_);
goto v___jp_1225_;
}
else
{
uint8_t v___x_1250_; 
v___x_1250_ = lean_nat_dec_le(v_startPos_1214_, v_stopPos_1215_);
if (v___x_1250_ == 0)
{
lean_del_object(v___x_1217_);
lean_dec(v_stopPos_1215_);
lean_dec(v_startPos_1214_);
lean_dec_ref(v_str_1213_);
goto v___jp_1225_;
}
else
{
lean_object* v___x_1252_; 
if (v_isShared_1218_ == 0)
{
v___x_1252_ = v___x_1217_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_str_1213_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v_startPos_1214_);
lean_ctor_set(v_reuseFailAlloc_1253_, 2, v_stopPos_1215_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
v___y_1222_ = v___x_1252_;
goto v___jp_1221_;
}
}
}
}
}
}
}
v___jp_1254_:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_1256_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_1255_);
v___y_1238_ = v___x_1256_;
goto v___jp_1237_;
}
}
else
{
lean_object* v___x_1261_; 
lean_dec(v___x_1219_);
lean_del_object(v___x_1217_);
lean_dec(v_stopPos_1215_);
lean_dec(v_startPos_1214_);
lean_dec_ref(v_str_1213_);
v___x_1261_ = lean_box(0);
return v___x_1261_;
}
v___jp_1221_:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(v___y_1222_, v___x_1220_, v___x_1220_);
lean_dec_ref(v___y_1222_);
v___x_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
return v___x_1224_;
}
v___jp_1225_:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_1227_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_1226_);
v___y_1222_ = v___x_1227_;
goto v___jp_1221_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0(lean_object* v___x_1263_, lean_object* v___y_1264_, lean_object* v_inst_1265_, lean_object* v_R_1266_, lean_object* v_a_1267_, lean_object* v_b_1268_, lean_object* v_c_1269_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(v___x_1263_, v___y_1264_, v_a_1267_, v_b_1268_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___boxed(lean_object* v___x_1271_, lean_object* v___y_1272_, lean_object* v_inst_1273_, lean_object* v_R_1274_, lean_object* v_a_1275_, lean_object* v_b_1276_, lean_object* v_c_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0(v___x_1271_, v___y_1272_, v_inst_1273_, v_R_1274_, v_a_1275_, v_b_1276_, v_c_1277_);
lean_dec_ref(v___y_1272_);
lean_dec(v___x_1271_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1(lean_object* v___y_1279_, lean_object* v_inst_1280_, lean_object* v_R_1281_, lean_object* v_a_1282_, lean_object* v_b_1283_, lean_object* v_c_1284_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(v___y_1279_, v_a_1282_, v_b_1283_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___boxed(lean_object* v___y_1286_, lean_object* v_inst_1287_, lean_object* v_R_1288_, lean_object* v_a_1289_, lean_object* v_b_1290_, lean_object* v_c_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1(v___y_1286_, v_inst_1287_, v_R_1288_, v_a_1289_, v_b_1290_, v_c_1291_);
lean_dec_ref(v___y_1286_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_repair(lean_object* v_x_1293_){
_start:
{
lean_object* v_str_1294_; lean_object* v_startPos_1295_; lean_object* v_stopPos_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1312_; 
v_str_1294_ = lean_ctor_get(v_x_1293_, 0);
v_startPos_1295_ = lean_ctor_get(v_x_1293_, 1);
v_stopPos_1296_ = lean_ctor_get(v_x_1293_, 2);
v_isSharedCheck_1312_ = !lean_is_exclusive(v_x_1293_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1298_ = v_x_1293_;
v_isShared_1299_ = v_isSharedCheck_1312_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_stopPos_1296_);
lean_inc(v_startPos_1295_);
lean_inc(v_str_1294_);
lean_dec(v_x_1293_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1312_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___y_1301_; uint8_t v___x_1310_; 
v___x_1310_ = lean_string_is_valid_pos(v_str_1294_, v_startPos_1295_);
if (v___x_1310_ == 0)
{
lean_object* v___x_1311_; 
lean_dec(v_startPos_1295_);
v___x_1311_ = lean_string_utf8_byte_size(v_str_1294_);
v___y_1301_ = v___x_1311_;
goto v___jp_1300_;
}
else
{
v___y_1301_ = v_startPos_1295_;
goto v___jp_1300_;
}
v___jp_1300_:
{
uint8_t v___x_1302_; 
v___x_1302_ = lean_string_is_valid_pos(v_str_1294_, v_stopPos_1296_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; lean_object* v___x_1305_; 
lean_dec(v_stopPos_1296_);
v___x_1303_ = lean_string_utf8_byte_size(v_str_1294_);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 2, v___x_1303_);
lean_ctor_set(v___x_1298_, 1, v___y_1301_);
v___x_1305_ = v___x_1298_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_str_1294_);
lean_ctor_set(v_reuseFailAlloc_1306_, 1, v___y_1301_);
lean_ctor_set(v_reuseFailAlloc_1306_, 2, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
else
{
lean_object* v___x_1308_; 
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 1, v___y_1301_);
v___x_1308_ = v___x_1298_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_str_1294_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v___y_1301_);
lean_ctor_set(v_reuseFailAlloc_1309_, 2, v_stopPos_1296_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_beq(lean_object* v_ss1_1313_, lean_object* v_ss2_1314_){
_start:
{
lean_object* v_ss1_1315_; lean_object* v_str_1316_; lean_object* v_startPos_1317_; lean_object* v_stopPos_1318_; lean_object* v_ss2_1319_; lean_object* v_str_1320_; lean_object* v_startPos_1321_; lean_object* v_stopPos_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; uint8_t v___x_1325_; 
v_ss1_1315_ = l_Substring_Raw_repair(v_ss1_1313_);
v_str_1316_ = lean_ctor_get(v_ss1_1315_, 0);
lean_inc_ref(v_str_1316_);
v_startPos_1317_ = lean_ctor_get(v_ss1_1315_, 1);
lean_inc(v_startPos_1317_);
v_stopPos_1318_ = lean_ctor_get(v_ss1_1315_, 2);
lean_inc(v_stopPos_1318_);
lean_dec_ref(v_ss1_1315_);
v_ss2_1319_ = l_Substring_Raw_repair(v_ss2_1314_);
v_str_1320_ = lean_ctor_get(v_ss2_1319_, 0);
lean_inc_ref(v_str_1320_);
v_startPos_1321_ = lean_ctor_get(v_ss2_1319_, 1);
lean_inc(v_startPos_1321_);
v_stopPos_1322_ = lean_ctor_get(v_ss2_1319_, 2);
lean_inc(v_stopPos_1322_);
lean_dec_ref(v_ss2_1319_);
v___x_1323_ = lean_nat_sub(v_stopPos_1318_, v_startPos_1317_);
lean_dec(v_stopPos_1318_);
v___x_1324_ = lean_nat_sub(v_stopPos_1322_, v_startPos_1321_);
lean_dec(v_stopPos_1322_);
v___x_1325_ = lean_nat_dec_eq(v___x_1323_, v___x_1324_);
lean_dec(v___x_1324_);
if (v___x_1325_ == 0)
{
lean_dec(v___x_1323_);
lean_dec(v_startPos_1321_);
lean_dec_ref(v_str_1320_);
lean_dec(v_startPos_1317_);
lean_dec_ref(v_str_1316_);
return v___x_1325_;
}
else
{
uint8_t v___x_1326_; 
v___x_1326_ = l_String_Pos_Raw_substrEq(v_str_1316_, v_startPos_1317_, v_str_1320_, v_startPos_1321_, v___x_1323_);
lean_dec(v___x_1323_);
lean_dec_ref(v_str_1320_);
lean_dec_ref(v_str_1316_);
return v___x_1326_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_beq___boxed(lean_object* v_ss1_1327_, lean_object* v_ss2_1328_){
_start:
{
uint8_t v_res_1329_; lean_object* v_r_1330_; 
v_res_1329_ = l_Substring_Raw_beq(v_ss1_1327_, v_ss2_1328_);
v_r_1330_ = lean_box(v_res_1329_);
return v_r_1330_;
}
}
LEAN_EXPORT uint8_t lean_substring_beq(lean_object* v_ss1_1331_, lean_object* v_ss2_1332_){
_start:
{
uint8_t v___x_1333_; 
v___x_1333_ = l_Substring_Raw_beq(v_ss1_1331_, v_ss2_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_beqImpl___boxed(lean_object* v_ss1_1334_, lean_object* v_ss2_1335_){
_start:
{
uint8_t v_res_1336_; lean_object* v_r_1337_; 
v_res_1336_ = lean_substring_beq(v_ss1_1334_, v_ss2_1335_);
v_r_1337_ = lean_box(v_res_1336_);
return v_r_1337_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_sameAs(lean_object* v_ss1_1340_, lean_object* v_ss2_1341_){
_start:
{
lean_object* v_startPos_1342_; lean_object* v_startPos_1343_; uint8_t v_decide_1344_; 
v_startPos_1342_ = lean_ctor_get(v_ss1_1340_, 1);
v_startPos_1343_ = lean_ctor_get(v_ss2_1341_, 1);
v_decide_1344_ = lean_nat_dec_eq(v_startPos_1342_, v_startPos_1343_);
if (v_decide_1344_ == 0)
{
lean_dec_ref(v_ss2_1341_);
lean_dec_ref(v_ss1_1340_);
return v_decide_1344_;
}
else
{
uint8_t v___x_1345_; 
v___x_1345_ = l_Substring_Raw_beq(v_ss1_1340_, v_ss2_1341_);
return v___x_1345_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_sameAs___boxed(lean_object* v_ss1_1346_, lean_object* v_ss2_1347_){
_start:
{
uint8_t v_res_1348_; lean_object* v_r_1349_; 
v_res_1348_ = l_Substring_Raw_sameAs(v_ss1_1346_, v_ss2_1347_);
v_r_1349_ = lean_box(v_res_1348_);
return v_r_1349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(lean_object* v_s_1350_, lean_object* v_t_1351_, lean_object* v_spos_1352_, lean_object* v_tpos_1353_){
_start:
{
lean_object* v_str_1354_; lean_object* v_stopPos_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; 
v_str_1354_ = lean_ctor_get(v_s_1350_, 0);
v_stopPos_1355_ = lean_ctor_get(v_s_1350_, 2);
v___x_1356_ = lean_unsigned_to_nat(1u);
v___x_1357_ = lean_nat_add(v_spos_1352_, v___x_1356_);
v___x_1358_ = lean_nat_dec_le(v___x_1357_, v_stopPos_1355_);
lean_dec(v___x_1357_);
if (v___x_1358_ == 0)
{
lean_dec(v_tpos_1353_);
return v_spos_1352_;
}
else
{
lean_object* v_str_1359_; lean_object* v_stopPos_1360_; lean_object* v___x_1361_; uint8_t v___x_1362_; 
v_str_1359_ = lean_ctor_get(v_t_1351_, 0);
v_stopPos_1360_ = lean_ctor_get(v_t_1351_, 2);
v___x_1361_ = lean_nat_add(v_tpos_1353_, v___x_1356_);
v___x_1362_ = lean_nat_dec_le(v___x_1361_, v_stopPos_1360_);
lean_dec(v___x_1361_);
if (v___x_1362_ == 0)
{
lean_dec(v_tpos_1353_);
return v_spos_1352_;
}
else
{
uint32_t v___x_1363_; uint32_t v___x_1364_; uint8_t v___x_1365_; 
v___x_1363_ = lean_string_utf8_get(v_str_1354_, v_spos_1352_);
v___x_1364_ = lean_string_utf8_get(v_str_1359_, v_tpos_1353_);
v___x_1365_ = lean_uint32_dec_eq(v___x_1363_, v___x_1364_);
if (v___x_1365_ == 0)
{
lean_dec(v_tpos_1353_);
return v_spos_1352_;
}
else
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = lean_string_utf8_next(v_str_1354_, v_spos_1352_);
lean_dec(v_spos_1352_);
v___x_1367_ = lean_string_utf8_next(v_str_1359_, v_tpos_1353_);
lean_dec(v_tpos_1353_);
v_spos_1352_ = v___x_1366_;
v_tpos_1353_ = v___x_1367_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop___boxed(lean_object* v_s_1369_, lean_object* v_t_1370_, lean_object* v_spos_1371_, lean_object* v_tpos_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(v_s_1369_, v_t_1370_, v_spos_1371_, v_tpos_1372_);
lean_dec_ref(v_t_1370_);
lean_dec_ref(v_s_1369_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_commonPrefix(lean_object* v_s_1374_, lean_object* v_t_1375_){
_start:
{
lean_object* v_str_1376_; lean_object* v_startPos_1377_; lean_object* v_startPos_1378_; lean_object* v___x_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
v_str_1376_ = lean_ctor_get(v_s_1374_, 0);
lean_inc_ref(v_str_1376_);
v_startPos_1377_ = lean_ctor_get(v_s_1374_, 1);
lean_inc_n(v_startPos_1377_, 2);
v_startPos_1378_ = lean_ctor_get(v_t_1375_, 1);
lean_inc(v_startPos_1378_);
v___x_1379_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(v_s_1374_, v_t_1375_, v_startPos_1377_, v_startPos_1378_);
lean_dec_ref(v_s_1374_);
v_isSharedCheck_1386_ = !lean_is_exclusive(v_t_1375_);
if (v_isSharedCheck_1386_ == 0)
{
lean_object* v_unused_1387_; lean_object* v_unused_1388_; lean_object* v_unused_1389_; 
v_unused_1387_ = lean_ctor_get(v_t_1375_, 2);
lean_dec(v_unused_1387_);
v_unused_1388_ = lean_ctor_get(v_t_1375_, 1);
lean_dec(v_unused_1388_);
v_unused_1389_ = lean_ctor_get(v_t_1375_, 0);
lean_dec(v_unused_1389_);
v___x_1381_ = v_t_1375_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_dec(v_t_1375_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 2, v___x_1379_);
lean_ctor_set(v___x_1381_, 1, v_startPos_1377_);
lean_ctor_set(v___x_1381_, 0, v_str_1376_);
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_str_1376_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v_startPos_1377_);
lean_ctor_set(v_reuseFailAlloc_1385_, 2, v___x_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(lean_object* v_s_1390_, lean_object* v_t_1391_, lean_object* v_spos_1392_, lean_object* v_tpos_1393_){
_start:
{
lean_object* v_str_1394_; lean_object* v_startPos_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; uint8_t v___x_1398_; 
v_str_1394_ = lean_ctor_get(v_s_1390_, 0);
v_startPos_1395_ = lean_ctor_get(v_s_1390_, 1);
v___x_1396_ = lean_unsigned_to_nat(1u);
v___x_1397_ = lean_nat_add(v_startPos_1395_, v___x_1396_);
v___x_1398_ = lean_nat_dec_le(v___x_1397_, v_spos_1392_);
lean_dec(v___x_1397_);
if (v___x_1398_ == 0)
{
lean_dec(v_tpos_1393_);
return v_spos_1392_;
}
else
{
lean_object* v_str_1399_; lean_object* v_startPos_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; 
v_str_1399_ = lean_ctor_get(v_t_1391_, 0);
v_startPos_1400_ = lean_ctor_get(v_t_1391_, 1);
v___x_1401_ = lean_nat_add(v_startPos_1400_, v___x_1396_);
v___x_1402_ = lean_nat_dec_le(v___x_1401_, v_tpos_1393_);
lean_dec(v___x_1401_);
if (v___x_1402_ == 0)
{
lean_dec(v_tpos_1393_);
return v_spos_1392_;
}
else
{
lean_object* v_spos_x27_1403_; lean_object* v_tpos_x27_1404_; uint32_t v___x_1405_; uint32_t v___x_1406_; uint8_t v___x_1407_; 
v_spos_x27_1403_ = lean_string_utf8_prev(v_str_1394_, v_spos_1392_);
v_tpos_x27_1404_ = lean_string_utf8_prev(v_str_1399_, v_tpos_1393_);
lean_dec(v_tpos_1393_);
v___x_1405_ = lean_string_utf8_get(v_str_1394_, v_spos_x27_1403_);
v___x_1406_ = lean_string_utf8_get(v_str_1399_, v_tpos_x27_1404_);
v___x_1407_ = lean_uint32_dec_eq(v___x_1405_, v___x_1406_);
if (v___x_1407_ == 0)
{
lean_dec(v_tpos_x27_1404_);
lean_dec(v_spos_x27_1403_);
return v_spos_1392_;
}
else
{
lean_dec(v_spos_1392_);
v_spos_1392_ = v_spos_x27_1403_;
v_tpos_1393_ = v_tpos_x27_1404_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop___boxed(lean_object* v_s_1409_, lean_object* v_t_1410_, lean_object* v_spos_1411_, lean_object* v_tpos_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(v_s_1409_, v_t_1410_, v_spos_1411_, v_tpos_1412_);
lean_dec_ref(v_t_1410_);
lean_dec_ref(v_s_1409_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_commonSuffix(lean_object* v_s_1414_, lean_object* v_t_1415_){
_start:
{
lean_object* v_str_1416_; lean_object* v_stopPos_1417_; lean_object* v_stopPos_1418_; lean_object* v___x_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
v_str_1416_ = lean_ctor_get(v_s_1414_, 0);
lean_inc_ref(v_str_1416_);
v_stopPos_1417_ = lean_ctor_get(v_s_1414_, 2);
lean_inc_n(v_stopPos_1417_, 2);
v_stopPos_1418_ = lean_ctor_get(v_t_1415_, 2);
lean_inc(v_stopPos_1418_);
v___x_1419_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(v_s_1414_, v_t_1415_, v_stopPos_1417_, v_stopPos_1418_);
lean_dec_ref(v_s_1414_);
v_isSharedCheck_1426_ = !lean_is_exclusive(v_t_1415_);
if (v_isSharedCheck_1426_ == 0)
{
lean_object* v_unused_1427_; lean_object* v_unused_1428_; lean_object* v_unused_1429_; 
v_unused_1427_ = lean_ctor_get(v_t_1415_, 2);
lean_dec(v_unused_1427_);
v_unused_1428_ = lean_ctor_get(v_t_1415_, 1);
lean_dec(v_unused_1428_);
v_unused_1429_ = lean_ctor_get(v_t_1415_, 0);
lean_dec(v_unused_1429_);
v___x_1421_ = v_t_1415_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_dec(v_t_1415_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 2, v_stopPos_1417_);
lean_ctor_set(v___x_1421_, 1, v___x_1419_);
lean_ctor_set(v___x_1421_, 0, v_str_1416_);
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_str_1416_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v___x_1419_);
lean_ctor_set(v_reuseFailAlloc_1425_, 2, v_stopPos_1417_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropPrefix_x3f(lean_object* v_s_1430_, lean_object* v_pre_1431_){
_start:
{
lean_object* v_t_1432_; lean_object* v_startPos_1433_; lean_object* v_stopPos_1434_; lean_object* v_startPos_1435_; lean_object* v_stopPos_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; uint8_t v___x_1439_; 
lean_inc_ref(v_pre_1431_);
lean_inc_ref(v_s_1430_);
v_t_1432_ = l_Substring_Raw_commonPrefix(v_s_1430_, v_pre_1431_);
v_startPos_1433_ = lean_ctor_get(v_t_1432_, 1);
lean_inc(v_startPos_1433_);
v_stopPos_1434_ = lean_ctor_get(v_t_1432_, 2);
lean_inc(v_stopPos_1434_);
lean_dec_ref(v_t_1432_);
v_startPos_1435_ = lean_ctor_get(v_pre_1431_, 1);
lean_inc(v_startPos_1435_);
v_stopPos_1436_ = lean_ctor_get(v_pre_1431_, 2);
lean_inc(v_stopPos_1436_);
lean_dec_ref(v_pre_1431_);
v___x_1437_ = lean_nat_sub(v_stopPos_1434_, v_startPos_1433_);
lean_dec(v_startPos_1433_);
v___x_1438_ = lean_nat_sub(v_stopPos_1436_, v_startPos_1435_);
lean_dec(v_startPos_1435_);
lean_dec(v_stopPos_1436_);
v___x_1439_ = lean_nat_dec_eq(v___x_1437_, v___x_1438_);
lean_dec(v___x_1438_);
lean_dec(v___x_1437_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1440_; 
lean_dec(v_stopPos_1434_);
lean_dec_ref(v_s_1430_);
v___x_1440_ = lean_box(0);
return v___x_1440_;
}
else
{
lean_object* v_str_1441_; lean_object* v_stopPos_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1450_; 
v_str_1441_ = lean_ctor_get(v_s_1430_, 0);
v_stopPos_1442_ = lean_ctor_get(v_s_1430_, 2);
v_isSharedCheck_1450_ = !lean_is_exclusive(v_s_1430_);
if (v_isSharedCheck_1450_ == 0)
{
lean_object* v_unused_1451_; 
v_unused_1451_ = lean_ctor_get(v_s_1430_, 1);
lean_dec(v_unused_1451_);
v___x_1444_ = v_s_1430_;
v_isShared_1445_ = v_isSharedCheck_1450_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_stopPos_1442_);
lean_inc(v_str_1441_);
lean_dec(v_s_1430_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1450_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 1, v_stopPos_1434_);
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_str_1441_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v_stopPos_1434_);
lean_ctor_set(v_reuseFailAlloc_1449_, 2, v_stopPos_1442_);
v___x_1447_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
lean_object* v___x_1448_; 
v___x_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1447_);
return v___x_1448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropSuffix_x3f(lean_object* v_s_1452_, lean_object* v_suff_1453_){
_start:
{
lean_object* v_t_1454_; lean_object* v_startPos_1455_; lean_object* v_stopPos_1456_; lean_object* v_startPos_1457_; lean_object* v_stopPos_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; uint8_t v___x_1461_; 
lean_inc_ref(v_suff_1453_);
lean_inc_ref(v_s_1452_);
v_t_1454_ = l_Substring_Raw_commonSuffix(v_s_1452_, v_suff_1453_);
v_startPos_1455_ = lean_ctor_get(v_t_1454_, 1);
lean_inc(v_startPos_1455_);
v_stopPos_1456_ = lean_ctor_get(v_t_1454_, 2);
lean_inc(v_stopPos_1456_);
lean_dec_ref(v_t_1454_);
v_startPos_1457_ = lean_ctor_get(v_suff_1453_, 1);
lean_inc(v_startPos_1457_);
v_stopPos_1458_ = lean_ctor_get(v_suff_1453_, 2);
lean_inc(v_stopPos_1458_);
lean_dec_ref(v_suff_1453_);
v___x_1459_ = lean_nat_sub(v_stopPos_1456_, v_startPos_1455_);
lean_dec(v_stopPos_1456_);
v___x_1460_ = lean_nat_sub(v_stopPos_1458_, v_startPos_1457_);
lean_dec(v_startPos_1457_);
lean_dec(v_stopPos_1458_);
v___x_1461_ = lean_nat_dec_eq(v___x_1459_, v___x_1460_);
lean_dec(v___x_1460_);
lean_dec(v___x_1459_);
if (v___x_1461_ == 0)
{
lean_object* v___x_1462_; 
lean_dec(v_startPos_1455_);
lean_dec_ref(v_s_1452_);
v___x_1462_ = lean_box(0);
return v___x_1462_;
}
else
{
lean_object* v_str_1463_; lean_object* v_startPos_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1472_; 
v_str_1463_ = lean_ctor_get(v_s_1452_, 0);
v_startPos_1464_ = lean_ctor_get(v_s_1452_, 1);
v_isSharedCheck_1472_ = !lean_is_exclusive(v_s_1452_);
if (v_isSharedCheck_1472_ == 0)
{
lean_object* v_unused_1473_; 
v_unused_1473_ = lean_ctor_get(v_s_1452_, 2);
lean_dec(v_unused_1473_);
v___x_1466_ = v_s_1452_;
v_isShared_1467_ = v_isSharedCheck_1472_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_startPos_1464_);
lean_inc(v_str_1463_);
lean_dec(v_s_1452_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1472_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 2, v_startPos_1455_);
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_str_1463_);
lean_ctor_set(v_reuseFailAlloc_1471_, 1, v_startPos_1464_);
lean_ctor_set(v_reuseFailAlloc_1471_, 2, v_startPos_1455_);
v___x_1469_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
lean_object* v___x_1470_; 
v___x_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1469_);
return v___x_1470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_bsize(lean_object* v_a_1474_){
_start:
{
lean_object* v_startPos_1475_; lean_object* v_stopPos_1476_; lean_object* v___x_1477_; 
v_startPos_1475_ = lean_ctor_get(v_a_1474_, 1);
v_stopPos_1476_ = lean_ctor_get(v_a_1474_, 2);
v___x_1477_ = lean_nat_sub(v_stopPos_1476_, v_startPos_1475_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Substring_bsize___boxed(lean_object* v_a_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Substring_bsize(v_a_1478_);
lean_dec_ref(v_a_1478_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Substring_toString(lean_object* v_a_1480_){
_start:
{
lean_object* v_str_1481_; lean_object* v_startPos_1482_; lean_object* v_stopPos_1483_; lean_object* v___x_1484_; 
v_str_1481_ = lean_ctor_get(v_a_1480_, 0);
v_startPos_1482_ = lean_ctor_get(v_a_1480_, 1);
v_stopPos_1483_ = lean_ctor_get(v_a_1480_, 2);
v___x_1484_ = lean_string_utf8_extract(v_str_1481_, v_startPos_1482_, v_stopPos_1483_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Substring_toString___boxed(lean_object* v_a_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Substring_toString(v_a_1485_);
lean_dec_ref(v_a_1485_);
return v_res_1486_;
}
}
LEAN_EXPORT uint8_t l_Substring_isEmpty(lean_object* v_ss_1487_){
_start:
{
lean_object* v_startPos_1488_; lean_object* v_stopPos_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; uint8_t v___x_1492_; 
v_startPos_1488_ = lean_ctor_get(v_ss_1487_, 1);
v_stopPos_1489_ = lean_ctor_get(v_ss_1487_, 2);
v___x_1490_ = lean_nat_sub(v_stopPos_1489_, v_startPos_1488_);
v___x_1491_ = lean_unsigned_to_nat(0u);
v___x_1492_ = lean_nat_dec_eq(v___x_1490_, v___x_1491_);
lean_dec(v___x_1490_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Substring_isEmpty___boxed(lean_object* v_ss_1493_){
_start:
{
uint8_t v_res_1494_; lean_object* v_r_1495_; 
v_res_1494_ = l_Substring_isEmpty(v_ss_1493_);
lean_dec_ref(v_ss_1493_);
v_r_1495_ = lean_box(v_res_1494_);
return v_r_1495_;
}
}
LEAN_EXPORT lean_object* l_Substring_next(lean_object* v_a_1496_, lean_object* v_a_1497_){
_start:
{
lean_object* v_str_1498_; lean_object* v_startPos_1499_; lean_object* v_stopPos_1500_; lean_object* v_absP_1501_; uint8_t v_decide_1502_; 
v_str_1498_ = lean_ctor_get(v_a_1496_, 0);
v_startPos_1499_ = lean_ctor_get(v_a_1496_, 1);
v_stopPos_1500_ = lean_ctor_get(v_a_1496_, 2);
v_absP_1501_ = lean_nat_add(v_startPos_1499_, v_a_1497_);
v_decide_1502_ = lean_nat_dec_eq(v_absP_1501_, v_stopPos_1500_);
if (v_decide_1502_ == 0)
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = lean_string_utf8_next(v_str_1498_, v_absP_1501_);
lean_dec(v_absP_1501_);
v___x_1504_ = lean_nat_sub(v___x_1503_, v_startPos_1499_);
lean_dec(v___x_1503_);
return v___x_1504_;
}
else
{
lean_dec(v_absP_1501_);
lean_inc(v_a_1497_);
return v_a_1497_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_next___boxed(lean_object* v_a_1505_, lean_object* v_a_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_Substring_next(v_a_1505_, v_a_1506_);
lean_dec(v_a_1506_);
lean_dec_ref(v_a_1505_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Substring_prev(lean_object* v_a_1508_, lean_object* v_a_1509_){
_start:
{
lean_object* v_str_1510_; lean_object* v_startPos_1511_; lean_object* v_absP_1512_; uint8_t v_decide_1513_; 
v_str_1510_ = lean_ctor_get(v_a_1508_, 0);
v_startPos_1511_ = lean_ctor_get(v_a_1508_, 1);
v_absP_1512_ = lean_nat_add(v_startPos_1511_, v_a_1509_);
v_decide_1513_ = lean_nat_dec_eq(v_absP_1512_, v_startPos_1511_);
if (v_decide_1513_ == 0)
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1514_ = lean_string_utf8_prev(v_str_1510_, v_absP_1512_);
lean_dec(v_absP_1512_);
v___x_1515_ = lean_nat_sub(v___x_1514_, v_startPos_1511_);
lean_dec(v___x_1514_);
return v___x_1515_;
}
else
{
lean_dec(v_absP_1512_);
lean_inc(v_a_1509_);
return v_a_1509_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_prev___boxed(lean_object* v_a_1516_, lean_object* v_a_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Substring_prev(v_a_1516_, v_a_1517_);
lean_dec(v_a_1517_);
lean_dec_ref(v_a_1516_);
return v_res_1518_;
}
}
LEAN_EXPORT uint8_t l_Substring_atEnd(lean_object* v_a_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v_startPos_1521_; lean_object* v_stopPos_1522_; lean_object* v___x_1523_; uint8_t v_decide_1524_; 
v_startPos_1521_ = lean_ctor_get(v_a_1519_, 1);
v_stopPos_1522_ = lean_ctor_get(v_a_1519_, 2);
v___x_1523_ = lean_nat_add(v_startPos_1521_, v_a_1520_);
v_decide_1524_ = lean_nat_dec_eq(v___x_1523_, v_stopPos_1522_);
lean_dec(v___x_1523_);
return v_decide_1524_;
}
}
LEAN_EXPORT lean_object* l_Substring_atEnd___boxed(lean_object* v_a_1525_, lean_object* v_a_1526_){
_start:
{
uint8_t v_res_1527_; lean_object* v_r_1528_; 
v_res_1527_ = l_Substring_atEnd(v_a_1525_, v_a_1526_);
lean_dec(v_a_1526_);
lean_dec_ref(v_a_1525_);
v_r_1528_ = lean_box(v_res_1527_);
return v_r_1528_;
}
}
LEAN_EXPORT uint8_t l_Substring_beq(lean_object* v_ss1_1529_, lean_object* v_ss2_1530_){
_start:
{
uint8_t v___x_1531_; 
v___x_1531_ = l_Substring_Raw_beq(v_ss1_1529_, v_ss2_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Substring_beq___boxed(lean_object* v_ss1_1532_, lean_object* v_ss2_1533_){
_start:
{
uint8_t v_res_1534_; lean_object* v_r_1535_; 
v_res_1534_ = l_Substring_beq(v_ss1_1532_, v_ss2_1533_);
v_r_1535_ = lean_box(v_res_1534_);
return v_r_1535_;
}
}
lean_object* runtime_initialize_Init_Data_String_Slice_Pattern(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Iterate(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_BasicAux(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Substring(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_String_Slice_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Iterate(builtin);
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
lean_object* initialize_Init_Data_String_Slice_Pattern(uint8_t builtin);
lean_object* initialize_Init_Data_String_Iterate(uint8_t builtin);
lean_object* initialize_Init_Data_Option_BasicAux(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Substring(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Slice_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Iterate(builtin);
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

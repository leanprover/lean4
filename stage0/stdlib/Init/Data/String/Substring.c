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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_get_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_get_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_get_match__1_splitter___redArg(lean_object* v_x_92_, lean_object* v_x_93_, lean_object* v_h__1_94_){
_start:
{
lean_object* v_str_95_; lean_object* v_startPos_96_; lean_object* v_stopPos_97_; lean_object* v___x_98_; 
v_str_95_ = lean_ctor_get(v_x_92_, 0);
lean_inc_ref(v_str_95_);
v_startPos_96_ = lean_ctor_get(v_x_92_, 1);
lean_inc(v_startPos_96_);
v_stopPos_97_ = lean_ctor_get(v_x_92_, 2);
lean_inc(v_stopPos_97_);
lean_dec_ref(v_x_92_);
v___x_98_ = lean_apply_4(v_h__1_94_, v_str_95_, v_startPos_96_, v_stopPos_97_, v_x_93_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_get_match__1_splitter(lean_object* v_motive_99_, lean_object* v_x_100_, lean_object* v_x_101_, lean_object* v_h__1_102_){
_start:
{
lean_object* v_str_103_; lean_object* v_startPos_104_; lean_object* v_stopPos_105_; lean_object* v___x_106_; 
v_str_103_ = lean_ctor_get(v_x_100_, 0);
lean_inc_ref(v_str_103_);
v_startPos_104_ = lean_ctor_get(v_x_100_, 1);
lean_inc(v_startPos_104_);
v_stopPos_105_ = lean_ctor_get(v_x_100_, 2);
lean_inc(v_stopPos_105_);
lean_dec_ref(v_x_100_);
v___x_106_ = lean_apply_4(v_h__1_102_, v_str_103_, v_startPos_104_, v_stopPos_105_, v_x_101_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_prev(lean_object* v_x_107_, lean_object* v_x_108_){
_start:
{
lean_object* v_str_109_; lean_object* v_startPos_110_; lean_object* v_absP_111_; uint8_t v_decide_112_; 
v_str_109_ = lean_ctor_get(v_x_107_, 0);
v_startPos_110_ = lean_ctor_get(v_x_107_, 1);
v_absP_111_ = lean_nat_add(v_startPos_110_, v_x_108_);
v_decide_112_ = lean_nat_dec_eq(v_absP_111_, v_startPos_110_);
if (v_decide_112_ == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = lean_string_utf8_prev(v_str_109_, v_absP_111_);
lean_dec(v_absP_111_);
v___x_114_ = lean_nat_sub(v___x_113_, v_startPos_110_);
lean_dec(v___x_113_);
return v___x_114_;
}
else
{
lean_dec(v_absP_111_);
lean_inc(v_x_108_);
return v_x_108_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_prev___boxed(lean_object* v_x_115_, lean_object* v_x_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Substring_Raw_prev(v_x_115_, v_x_116_);
lean_dec(v_x_116_);
lean_dec_ref(v_x_115_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* lean_substring_prev(lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v_str_120_; lean_object* v_startPos_121_; lean_object* v_absP_122_; uint8_t v_decide_123_; 
v_str_120_ = lean_ctor_get(v_a_118_, 0);
lean_inc_ref(v_str_120_);
v_startPos_121_ = lean_ctor_get(v_a_118_, 1);
lean_inc(v_startPos_121_);
lean_dec_ref(v_a_118_);
v_absP_122_ = lean_nat_add(v_startPos_121_, v_a_119_);
v_decide_123_ = lean_nat_dec_eq(v_absP_122_, v_startPos_121_);
if (v_decide_123_ == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; 
lean_dec(v_a_119_);
v___x_124_ = lean_string_utf8_prev(v_str_120_, v_absP_122_);
lean_dec(v_absP_122_);
lean_dec_ref(v_str_120_);
v___x_125_ = lean_nat_sub(v___x_124_, v_startPos_121_);
lean_dec(v_startPos_121_);
lean_dec(v___x_124_);
return v___x_125_;
}
else
{
lean_dec(v_absP_122_);
lean_dec(v_startPos_121_);
lean_dec_ref(v_str_120_);
return v_a_119_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_nextn(lean_object* v_x_126_, lean_object* v_x_127_, lean_object* v_x_128_){
_start:
{
lean_object* v_zero_129_; uint8_t v_isZero_130_; 
v_zero_129_ = lean_unsigned_to_nat(0u);
v_isZero_130_ = lean_nat_dec_eq(v_x_127_, v_zero_129_);
if (v_isZero_130_ == 1)
{
lean_dec(v_x_127_);
return v_x_128_;
}
else
{
lean_object* v_str_131_; lean_object* v_startPos_132_; lean_object* v_stopPos_133_; lean_object* v_one_134_; lean_object* v_n_135_; lean_object* v_absP_136_; uint8_t v_decide_137_; 
v_str_131_ = lean_ctor_get(v_x_126_, 0);
v_startPos_132_ = lean_ctor_get(v_x_126_, 1);
v_stopPos_133_ = lean_ctor_get(v_x_126_, 2);
v_one_134_ = lean_unsigned_to_nat(1u);
v_n_135_ = lean_nat_sub(v_x_127_, v_one_134_);
lean_dec(v_x_127_);
v_absP_136_ = lean_nat_add(v_startPos_132_, v_x_128_);
v_decide_137_ = lean_nat_dec_eq(v_absP_136_, v_stopPos_133_);
if (v_decide_137_ == 0)
{
lean_object* v___x_138_; lean_object* v___x_139_; 
lean_dec(v_x_128_);
v___x_138_ = lean_string_utf8_next(v_str_131_, v_absP_136_);
lean_dec(v_absP_136_);
v___x_139_ = lean_nat_sub(v___x_138_, v_startPos_132_);
lean_dec(v___x_138_);
v_x_127_ = v_n_135_;
v_x_128_ = v___x_139_;
goto _start;
}
else
{
lean_dec(v_absP_136_);
v_x_127_ = v_n_135_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_nextn___boxed(lean_object* v_x_142_, lean_object* v_x_143_, lean_object* v_x_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Substring_Raw_nextn(v_x_142_, v_x_143_, v_x_144_);
lean_dec_ref(v_x_142_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_prevn(lean_object* v_x_146_, lean_object* v_x_147_, lean_object* v_x_148_){
_start:
{
lean_object* v_zero_149_; uint8_t v_isZero_150_; 
v_zero_149_ = lean_unsigned_to_nat(0u);
v_isZero_150_ = lean_nat_dec_eq(v_x_147_, v_zero_149_);
if (v_isZero_150_ == 1)
{
lean_dec(v_x_147_);
return v_x_148_;
}
else
{
lean_object* v_str_151_; lean_object* v_startPos_152_; lean_object* v_one_153_; lean_object* v_n_154_; lean_object* v_absP_155_; uint8_t v_decide_156_; 
v_str_151_ = lean_ctor_get(v_x_146_, 0);
v_startPos_152_ = lean_ctor_get(v_x_146_, 1);
v_one_153_ = lean_unsigned_to_nat(1u);
v_n_154_ = lean_nat_sub(v_x_147_, v_one_153_);
lean_dec(v_x_147_);
v_absP_155_ = lean_nat_add(v_startPos_152_, v_x_148_);
v_decide_156_ = lean_nat_dec_eq(v_absP_155_, v_startPos_152_);
if (v_decide_156_ == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; 
lean_dec(v_x_148_);
v___x_157_ = lean_string_utf8_prev(v_str_151_, v_absP_155_);
lean_dec(v_absP_155_);
v___x_158_ = lean_nat_sub(v___x_157_, v_startPos_152_);
lean_dec(v___x_157_);
v_x_147_ = v_n_154_;
v_x_148_ = v___x_158_;
goto _start;
}
else
{
lean_dec(v_absP_155_);
v_x_147_ = v_n_154_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_prevn___boxed(lean_object* v_x_161_, lean_object* v_x_162_, lean_object* v_x_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Substring_Raw_prevn(v_x_161_, v_x_162_, v_x_163_);
lean_dec_ref(v_x_161_);
return v_res_164_;
}
}
LEAN_EXPORT uint32_t l_Substring_Raw_front(lean_object* v_s_165_){
_start:
{
lean_object* v_str_166_; lean_object* v_startPos_167_; uint32_t v___x_168_; 
v_str_166_ = lean_ctor_get(v_s_165_, 0);
v_startPos_167_ = lean_ctor_get(v_s_165_, 1);
v___x_168_ = lean_string_utf8_get(v_str_166_, v_startPos_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_front___boxed(lean_object* v_s_169_){
_start:
{
uint32_t v_res_170_; lean_object* v_r_171_; 
v_res_170_ = l_Substring_Raw_front(v_s_169_);
lean_dec_ref(v_s_169_);
v_r_171_ = lean_box_uint32(v_res_170_);
return v_r_171_;
}
}
LEAN_EXPORT uint32_t lean_substring_front(lean_object* v_s_172_){
_start:
{
lean_object* v_str_173_; lean_object* v_startPos_174_; uint32_t v___x_175_; 
v_str_173_ = lean_ctor_get(v_s_172_, 0);
lean_inc_ref(v_str_173_);
v_startPos_174_ = lean_ctor_get(v_s_172_, 1);
lean_inc(v_startPos_174_);
lean_dec_ref(v_s_172_);
v___x_175_ = lean_string_utf8_get(v_str_173_, v_startPos_174_);
lean_dec(v_startPos_174_);
lean_dec_ref(v_str_173_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_frontImpl___boxed(lean_object* v_s_176_){
_start:
{
uint32_t v_res_177_; lean_object* v_r_178_; 
v_res_177_ = lean_substring_front(v_s_176_);
v_r_178_ = lean_box_uint32(v_res_177_);
return v_r_178_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_posOf___lam__0(lean_object* v_stopPos_179_, lean_object* v_startPos_180_, lean_object* v_str_181_, uint32_t v_c_182_, lean_object* v___x_183_, lean_object* v_it_184_, lean_object* v_acc_185_, lean_object* v_hP_186_, lean_object* v_recur_187_){
_start:
{
lean_object* v___x_188_; uint8_t v_decide_189_; 
v___x_188_ = lean_nat_sub(v_stopPos_179_, v_startPos_180_);
v_decide_189_ = lean_nat_dec_eq(v_it_184_, v___x_188_);
lean_dec(v___x_188_);
if (v_decide_189_ == 0)
{
lean_object* v___x_190_; uint32_t v___x_191_; uint8_t v___x_192_; 
v___x_190_ = lean_nat_add(v_startPos_180_, v_it_184_);
v___x_191_ = lean_string_utf8_get_fast(v_str_181_, v___x_190_);
v___x_192_ = lean_uint32_dec_eq(v___x_191_, v_c_182_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
lean_dec(v_it_184_);
v___x_193_ = lean_string_utf8_next_fast(v_str_181_, v___x_190_);
lean_dec(v___x_190_);
v___x_194_ = lean_nat_sub(v___x_193_, v_startPos_180_);
v___x_195_ = lean_apply_4(v_recur_187_, v___x_194_, v___x_183_, lean_box(0), lean_box(0));
return v___x_195_;
}
else
{
lean_object* v___x_196_; 
lean_dec(v___x_190_);
lean_dec_ref(v_recur_187_);
lean_dec(v___x_183_);
v___x_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_196_, 0, v_it_184_);
return v___x_196_;
}
}
else
{
lean_dec_ref(v_recur_187_);
lean_dec(v_it_184_);
lean_dec(v___x_183_);
lean_inc(v_acc_185_);
return v_acc_185_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_posOf___lam__0___boxed(lean_object* v_stopPos_197_, lean_object* v_startPos_198_, lean_object* v_str_199_, lean_object* v_c_200_, lean_object* v___x_201_, lean_object* v_it_202_, lean_object* v_acc_203_, lean_object* v_hP_204_, lean_object* v_recur_205_){
_start:
{
uint32_t v_c_boxed_206_; lean_object* v_res_207_; 
v_c_boxed_206_ = lean_unbox_uint32(v_c_200_);
lean_dec(v_c_200_);
v_res_207_ = l_Substring_Raw_posOf___lam__0(v_stopPos_197_, v_startPos_198_, v_str_199_, v_c_boxed_206_, v___x_201_, v_it_202_, v_acc_203_, v_hP_204_, v_recur_205_);
lean_dec(v_acc_203_);
lean_dec_ref(v_str_199_);
lean_dec(v_startPos_198_);
lean_dec(v_stopPos_197_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_posOf(lean_object* v_s_208_, uint32_t v_c_209_){
_start:
{
lean_object* v_str_210_; lean_object* v_startPos_211_; lean_object* v_stopPos_212_; uint8_t v___x_213_; 
v_str_210_ = lean_ctor_get(v_s_208_, 0);
lean_inc_ref(v_str_210_);
v_startPos_211_ = lean_ctor_get(v_s_208_, 1);
lean_inc(v_startPos_211_);
v_stopPos_212_ = lean_ctor_get(v_s_208_, 2);
lean_inc(v_stopPos_212_);
lean_dec_ref(v_s_208_);
v___x_213_ = lean_string_is_valid_pos(v_str_210_, v_startPos_211_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; 
lean_dec_ref(v_str_210_);
v___x_214_ = lean_nat_sub(v_stopPos_212_, v_startPos_211_);
lean_dec(v_startPos_211_);
lean_dec(v_stopPos_212_);
return v___x_214_;
}
else
{
uint8_t v___x_215_; 
v___x_215_ = lean_string_is_valid_pos(v_str_210_, v_stopPos_212_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; 
lean_dec_ref(v_str_210_);
v___x_216_ = lean_nat_sub(v_stopPos_212_, v_startPos_211_);
lean_dec(v_startPos_211_);
lean_dec(v_stopPos_212_);
return v___x_216_;
}
else
{
uint8_t v___x_217_; 
v___x_217_ = lean_nat_dec_le(v_startPos_211_, v_stopPos_212_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; 
lean_dec_ref(v_str_210_);
v___x_218_ = lean_nat_sub(v_stopPos_212_, v_startPos_211_);
lean_dec(v_startPos_211_);
lean_dec(v_stopPos_212_);
return v___x_218_;
}
else
{
lean_object* v_searcher_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___f_222_; lean_object* v___x_223_; 
v_searcher_219_ = lean_unsigned_to_nat(0u);
v___x_220_ = lean_box(0);
v___x_221_ = lean_box_uint32(v_c_209_);
lean_inc(v_startPos_211_);
lean_inc(v_stopPos_212_);
v___f_222_ = lean_alloc_closure((void*)(l_Substring_Raw_posOf___lam__0___boxed), 9, 5);
lean_closure_set(v___f_222_, 0, v_stopPos_212_);
lean_closure_set(v___f_222_, 1, v_startPos_211_);
lean_closure_set(v___f_222_, 2, v_str_210_);
lean_closure_set(v___f_222_, 3, v___x_221_);
lean_closure_set(v___f_222_, 4, v___x_220_);
v___x_223_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_222_, v_searcher_219_, v___x_220_, lean_box(0));
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v___x_224_; 
v___x_224_ = lean_nat_sub(v_stopPos_212_, v_startPos_211_);
lean_dec(v_startPos_211_);
lean_dec(v_stopPos_212_);
return v___x_224_;
}
else
{
lean_object* v_val_225_; 
lean_dec(v_stopPos_212_);
lean_dec(v_startPos_211_);
v_val_225_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_val_225_);
lean_dec_ref_known(v___x_223_, 1);
return v_val_225_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_posOf___boxed(lean_object* v_s_226_, lean_object* v_c_227_){
_start:
{
uint32_t v_c_boxed_228_; lean_object* v_res_229_; 
v_c_boxed_228_ = lean_unbox_uint32(v_c_227_);
lean_dec(v_c_227_);
v_res_229_ = l_Substring_Raw_posOf(v_s_226_, v_c_boxed_228_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_drop(lean_object* v_x_230_, lean_object* v_x_231_){
_start:
{
lean_object* v_str_232_; lean_object* v_startPos_233_; lean_object* v_stopPos_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_244_; 
v_str_232_ = lean_ctor_get(v_x_230_, 0);
lean_inc_ref(v_str_232_);
v_startPos_233_ = lean_ctor_get(v_x_230_, 1);
lean_inc(v_startPos_233_);
v_stopPos_234_ = lean_ctor_get(v_x_230_, 2);
lean_inc(v_stopPos_234_);
v___x_235_ = lean_unsigned_to_nat(0u);
v___x_236_ = l_Substring_Raw_nextn(v_x_230_, v_x_231_, v___x_235_);
v_isSharedCheck_244_ = !lean_is_exclusive(v_x_230_);
if (v_isSharedCheck_244_ == 0)
{
lean_object* v_unused_245_; lean_object* v_unused_246_; lean_object* v_unused_247_; 
v_unused_245_ = lean_ctor_get(v_x_230_, 2);
lean_dec(v_unused_245_);
v_unused_246_ = lean_ctor_get(v_x_230_, 1);
lean_dec(v_unused_246_);
v_unused_247_ = lean_ctor_get(v_x_230_, 0);
lean_dec(v_unused_247_);
v___x_238_ = v_x_230_;
v_isShared_239_ = v_isSharedCheck_244_;
goto v_resetjp_237_;
}
else
{
lean_dec(v_x_230_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_244_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_240_ = lean_nat_add(v_startPos_233_, v___x_236_);
lean_dec(v___x_236_);
lean_dec(v_startPos_233_);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 1, v___x_240_);
v___x_242_ = v___x_238_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_str_232_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v___x_240_);
lean_ctor_set(v_reuseFailAlloc_243_, 2, v_stopPos_234_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
LEAN_EXPORT lean_object* lean_substring_drop(lean_object* v_a_248_, lean_object* v_a_249_){
_start:
{
lean_object* v_str_250_; lean_object* v_startPos_251_; lean_object* v_stopPos_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_262_; 
v_str_250_ = lean_ctor_get(v_a_248_, 0);
lean_inc_ref(v_str_250_);
v_startPos_251_ = lean_ctor_get(v_a_248_, 1);
lean_inc(v_startPos_251_);
v_stopPos_252_ = lean_ctor_get(v_a_248_, 2);
lean_inc(v_stopPos_252_);
v___x_253_ = lean_unsigned_to_nat(0u);
v___x_254_ = l_Substring_Raw_nextn(v_a_248_, v_a_249_, v___x_253_);
v_isSharedCheck_262_ = !lean_is_exclusive(v_a_248_);
if (v_isSharedCheck_262_ == 0)
{
lean_object* v_unused_263_; lean_object* v_unused_264_; lean_object* v_unused_265_; 
v_unused_263_ = lean_ctor_get(v_a_248_, 2);
lean_dec(v_unused_263_);
v_unused_264_ = lean_ctor_get(v_a_248_, 1);
lean_dec(v_unused_264_);
v_unused_265_ = lean_ctor_get(v_a_248_, 0);
lean_dec(v_unused_265_);
v___x_256_ = v_a_248_;
v_isShared_257_ = v_isSharedCheck_262_;
goto v_resetjp_255_;
}
else
{
lean_dec(v_a_248_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_262_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_258_; lean_object* v___x_260_; 
v___x_258_ = lean_nat_add(v_startPos_251_, v___x_254_);
lean_dec(v___x_254_);
lean_dec(v_startPos_251_);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 1, v___x_258_);
v___x_260_ = v___x_256_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_str_250_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v___x_258_);
lean_ctor_set(v_reuseFailAlloc_261_, 2, v_stopPos_252_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropRight(lean_object* v_x_266_, lean_object* v_x_267_){
_start:
{
lean_object* v_str_268_; lean_object* v_startPos_269_; lean_object* v_stopPos_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_280_; 
v_str_268_ = lean_ctor_get(v_x_266_, 0);
lean_inc_ref(v_str_268_);
v_startPos_269_ = lean_ctor_get(v_x_266_, 1);
lean_inc(v_startPos_269_);
v_stopPos_270_ = lean_ctor_get(v_x_266_, 2);
v___x_271_ = lean_nat_sub(v_stopPos_270_, v_startPos_269_);
v___x_272_ = l_Substring_Raw_prevn(v_x_266_, v_x_267_, v___x_271_);
v_isSharedCheck_280_ = !lean_is_exclusive(v_x_266_);
if (v_isSharedCheck_280_ == 0)
{
lean_object* v_unused_281_; lean_object* v_unused_282_; lean_object* v_unused_283_; 
v_unused_281_ = lean_ctor_get(v_x_266_, 2);
lean_dec(v_unused_281_);
v_unused_282_ = lean_ctor_get(v_x_266_, 1);
lean_dec(v_unused_282_);
v_unused_283_ = lean_ctor_get(v_x_266_, 0);
lean_dec(v_unused_283_);
v___x_274_ = v_x_266_;
v_isShared_275_ = v_isSharedCheck_280_;
goto v_resetjp_273_;
}
else
{
lean_dec(v_x_266_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_280_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_276_; lean_object* v___x_278_; 
v___x_276_ = lean_nat_add(v_startPos_269_, v___x_272_);
lean_dec(v___x_272_);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 2, v___x_276_);
v___x_278_ = v___x_274_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_str_268_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_startPos_269_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v___x_276_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_take(lean_object* v_x_284_, lean_object* v_x_285_){
_start:
{
lean_object* v_str_286_; lean_object* v_startPos_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_297_; 
v_str_286_ = lean_ctor_get(v_x_284_, 0);
lean_inc_ref(v_str_286_);
v_startPos_287_ = lean_ctor_get(v_x_284_, 1);
lean_inc(v_startPos_287_);
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = l_Substring_Raw_nextn(v_x_284_, v_x_285_, v___x_288_);
v_isSharedCheck_297_ = !lean_is_exclusive(v_x_284_);
if (v_isSharedCheck_297_ == 0)
{
lean_object* v_unused_298_; lean_object* v_unused_299_; lean_object* v_unused_300_; 
v_unused_298_ = lean_ctor_get(v_x_284_, 2);
lean_dec(v_unused_298_);
v_unused_299_ = lean_ctor_get(v_x_284_, 1);
lean_dec(v_unused_299_);
v_unused_300_ = lean_ctor_get(v_x_284_, 0);
lean_dec(v_unused_300_);
v___x_291_ = v_x_284_;
v_isShared_292_ = v_isSharedCheck_297_;
goto v_resetjp_290_;
}
else
{
lean_dec(v_x_284_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_297_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_293_ = lean_nat_add(v_startPos_287_, v___x_289_);
lean_dec(v___x_289_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 2, v___x_293_);
v___x_295_ = v___x_291_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_str_286_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v_startPos_287_);
lean_ctor_set(v_reuseFailAlloc_296_, 2, v___x_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRight(lean_object* v_x_301_, lean_object* v_x_302_){
_start:
{
lean_object* v_str_303_; lean_object* v_startPos_304_; lean_object* v_stopPos_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_315_; 
v_str_303_ = lean_ctor_get(v_x_301_, 0);
lean_inc_ref(v_str_303_);
v_startPos_304_ = lean_ctor_get(v_x_301_, 1);
lean_inc(v_startPos_304_);
v_stopPos_305_ = lean_ctor_get(v_x_301_, 2);
lean_inc(v_stopPos_305_);
v___x_306_ = lean_nat_sub(v_stopPos_305_, v_startPos_304_);
v___x_307_ = l_Substring_Raw_prevn(v_x_301_, v_x_302_, v___x_306_);
v_isSharedCheck_315_ = !lean_is_exclusive(v_x_301_);
if (v_isSharedCheck_315_ == 0)
{
lean_object* v_unused_316_; lean_object* v_unused_317_; lean_object* v_unused_318_; 
v_unused_316_ = lean_ctor_get(v_x_301_, 2);
lean_dec(v_unused_316_);
v_unused_317_ = lean_ctor_get(v_x_301_, 1);
lean_dec(v_unused_317_);
v_unused_318_ = lean_ctor_get(v_x_301_, 0);
lean_dec(v_unused_318_);
v___x_309_ = v_x_301_;
v_isShared_310_ = v_isSharedCheck_315_;
goto v_resetjp_308_;
}
else
{
lean_dec(v_x_301_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_315_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_311_; lean_object* v___x_313_; 
v___x_311_ = lean_nat_add(v_startPos_304_, v___x_307_);
lean_dec(v___x_307_);
lean_dec(v_startPos_304_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 1, v___x_311_);
v___x_313_ = v___x_309_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_str_303_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v___x_311_);
lean_ctor_set(v_reuseFailAlloc_314_, 2, v_stopPos_305_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_atEnd(lean_object* v_x_319_, lean_object* v_x_320_){
_start:
{
lean_object* v_startPos_321_; lean_object* v_stopPos_322_; lean_object* v___x_323_; uint8_t v_decide_324_; 
v_startPos_321_ = lean_ctor_get(v_x_319_, 1);
v_stopPos_322_ = lean_ctor_get(v_x_319_, 2);
v___x_323_ = lean_nat_add(v_startPos_321_, v_x_320_);
v_decide_324_ = lean_nat_dec_eq(v___x_323_, v_stopPos_322_);
lean_dec(v___x_323_);
return v_decide_324_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_atEnd___boxed(lean_object* v_x_325_, lean_object* v_x_326_){
_start:
{
uint8_t v_res_327_; lean_object* v_r_328_; 
v_res_327_ = l_Substring_Raw_atEnd(v_x_325_, v_x_326_);
lean_dec(v_x_326_);
lean_dec_ref(v_x_325_);
v_r_328_ = lean_box(v_res_327_);
return v_r_328_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_extract(lean_object* v_x_333_, lean_object* v_x_334_, lean_object* v_x_335_){
_start:
{
lean_object* v_str_336_; lean_object* v_startPos_337_; lean_object* v_stopPos_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_356_; 
v_str_336_ = lean_ctor_get(v_x_333_, 0);
v_startPos_337_ = lean_ctor_get(v_x_333_, 1);
v_stopPos_338_ = lean_ctor_get(v_x_333_, 2);
v_isSharedCheck_356_ = !lean_is_exclusive(v_x_333_);
if (v_isSharedCheck_356_ == 0)
{
v___x_340_ = v_x_333_;
v_isShared_341_ = v_isSharedCheck_356_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_stopPos_338_);
lean_inc(v_startPos_337_);
lean_inc(v_str_336_);
lean_dec(v_x_333_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_356_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___y_343_; uint8_t v___x_352_; 
v___x_352_ = lean_nat_dec_le(v_x_335_, v_x_334_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_353_ = lean_nat_add(v_startPos_337_, v_x_334_);
v___x_354_ = lean_nat_dec_le(v_stopPos_338_, v___x_353_);
if (v___x_354_ == 0)
{
v___y_343_ = v___x_353_;
goto v___jp_342_;
}
else
{
lean_dec(v___x_353_);
lean_inc(v_stopPos_338_);
v___y_343_ = v_stopPos_338_;
goto v___jp_342_;
}
}
else
{
lean_object* v___x_355_; 
lean_del_object(v___x_340_);
lean_dec(v_stopPos_338_);
lean_dec(v_startPos_337_);
lean_dec_ref(v_str_336_);
v___x_355_ = ((lean_object*)(l_Substring_Raw_extract___closed__1));
return v___x_355_;
}
v___jp_342_:
{
lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_344_ = lean_nat_add(v_startPos_337_, v_x_335_);
lean_dec(v_startPos_337_);
v___x_345_ = lean_nat_dec_le(v_stopPos_338_, v___x_344_);
if (v___x_345_ == 0)
{
lean_object* v___x_347_; 
lean_dec(v_stopPos_338_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 2, v___x_344_);
lean_ctor_set(v___x_340_, 1, v___y_343_);
v___x_347_ = v___x_340_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_str_336_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v___y_343_);
lean_ctor_set(v_reuseFailAlloc_348_, 2, v___x_344_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
else
{
lean_object* v___x_350_; 
lean_dec(v___x_344_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 1, v___y_343_);
v___x_350_ = v___x_340_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_str_336_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v___y_343_);
lean_ctor_set(v_reuseFailAlloc_351_, 2, v_stopPos_338_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_extract___boxed(lean_object* v_x_357_, lean_object* v_x_358_, lean_object* v_x_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Substring_Raw_extract(v_x_357_, v_x_358_, v_x_359_);
lean_dec(v_x_359_);
lean_dec(v_x_358_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* lean_substring_extract(lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_){
_start:
{
lean_object* v_str_364_; lean_object* v_startPos_365_; lean_object* v_stopPos_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_384_; 
v_str_364_ = lean_ctor_get(v_a_361_, 0);
v_startPos_365_ = lean_ctor_get(v_a_361_, 1);
v_stopPos_366_ = lean_ctor_get(v_a_361_, 2);
v_isSharedCheck_384_ = !lean_is_exclusive(v_a_361_);
if (v_isSharedCheck_384_ == 0)
{
v___x_368_ = v_a_361_;
v_isShared_369_ = v_isSharedCheck_384_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_stopPos_366_);
lean_inc(v_startPos_365_);
lean_inc(v_str_364_);
lean_dec(v_a_361_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_384_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___y_371_; uint8_t v___x_380_; 
v___x_380_ = lean_nat_dec_le(v_a_363_, v_a_362_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_381_ = lean_nat_add(v_startPos_365_, v_a_362_);
lean_dec(v_a_362_);
v___x_382_ = lean_nat_dec_le(v_stopPos_366_, v___x_381_);
if (v___x_382_ == 0)
{
v___y_371_ = v___x_381_;
goto v___jp_370_;
}
else
{
lean_dec(v___x_381_);
lean_inc(v_stopPos_366_);
v___y_371_ = v_stopPos_366_;
goto v___jp_370_;
}
}
else
{
lean_object* v___x_383_; 
lean_del_object(v___x_368_);
lean_dec(v_stopPos_366_);
lean_dec(v_startPos_365_);
lean_dec_ref(v_str_364_);
lean_dec(v_a_363_);
lean_dec(v_a_362_);
v___x_383_ = ((lean_object*)(l_Substring_Raw_extract___closed__1));
return v___x_383_;
}
v___jp_370_:
{
lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_372_ = lean_nat_add(v_startPos_365_, v_a_363_);
lean_dec(v_a_363_);
lean_dec(v_startPos_365_);
v___x_373_ = lean_nat_dec_le(v_stopPos_366_, v___x_372_);
if (v___x_373_ == 0)
{
lean_object* v___x_375_; 
lean_dec(v_stopPos_366_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 2, v___x_372_);
lean_ctor_set(v___x_368_, 1, v___y_371_);
v___x_375_ = v___x_368_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_str_364_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v___y_371_);
lean_ctor_set(v_reuseFailAlloc_376_, 2, v___x_372_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
else
{
lean_object* v___x_378_; 
lean_dec(v___x_372_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 1, v___y_371_);
v___x_378_ = v___x_368_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_str_364_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v___y_371_);
lean_ctor_set(v_reuseFailAlloc_379_, 2, v_stopPos_366_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop(lean_object* v_s_385_, lean_object* v_sep_386_, lean_object* v_b_387_, lean_object* v_i_388_, lean_object* v_j_389_, lean_object* v_r_390_){
_start:
{
lean_object* v___y_392_; lean_object* v___y_396_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v_str_405_; lean_object* v_startPos_406_; lean_object* v_stopPos_407_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v___y_418_; lean_object* v___y_429_; lean_object* v___x_434_; uint8_t v___x_435_; 
v_str_405_ = lean_ctor_get(v_s_385_, 0);
v_startPos_406_ = lean_ctor_get(v_s_385_, 1);
v_stopPos_407_ = lean_ctor_get(v_s_385_, 2);
v___x_434_ = lean_nat_sub(v_stopPos_407_, v_startPos_406_);
v___x_435_ = lean_nat_dec_lt(v_i_388_, v___x_434_);
lean_dec(v___x_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_464_; 
lean_inc(v_stopPos_407_);
lean_inc(v_startPos_406_);
lean_inc_ref(v_str_405_);
v_isSharedCheck_464_ = !lean_is_exclusive(v_s_385_);
if (v_isSharedCheck_464_ == 0)
{
lean_object* v_unused_465_; lean_object* v_unused_466_; lean_object* v_unused_467_; 
v_unused_465_ = lean_ctor_get(v_s_385_, 2);
lean_dec(v_unused_465_);
v_unused_466_ = lean_ctor_get(v_s_385_, 1);
lean_dec(v_unused_466_);
v_unused_467_ = lean_ctor_get(v_s_385_, 0);
lean_dec(v_unused_467_);
v___x_437_ = v_s_385_;
v_isShared_438_ = v_isSharedCheck_464_;
goto v_resetjp_436_;
}
else
{
lean_dec(v_s_385_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_464_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
uint8_t v___x_439_; 
v___x_439_ = lean_string_utf8_at_end(v_sep_386_, v_j_389_);
if (v___x_439_ == 0)
{
uint8_t v___x_440_; 
lean_del_object(v___x_437_);
lean_dec(v_j_389_);
v___x_440_ = lean_nat_dec_le(v_i_388_, v_b_387_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_441_ = lean_nat_add(v_startPos_406_, v_b_387_);
lean_dec(v_b_387_);
v___x_442_ = lean_nat_dec_le(v_stopPos_407_, v___x_441_);
if (v___x_442_ == 0)
{
v___y_429_ = v___x_441_;
goto v___jp_428_;
}
else
{
lean_dec(v___x_441_);
lean_inc(v_stopPos_407_);
v___y_429_ = v_stopPos_407_;
goto v___jp_428_;
}
}
else
{
lean_object* v___x_443_; 
lean_dec(v_stopPos_407_);
lean_dec(v_startPos_406_);
lean_dec_ref(v_str_405_);
lean_dec(v_i_388_);
lean_dec(v_b_387_);
v___x_443_ = ((lean_object*)(l_Substring_Raw_extract___closed__1));
v___y_392_ = v___x_443_;
goto v___jp_391_;
}
}
else
{
lean_object* v___x_444_; lean_object* v___y_446_; lean_object* v___x_450_; lean_object* v___y_452_; uint8_t v___x_461_; 
v___x_444_ = ((lean_object*)(l_Substring_Raw_extract___closed__1));
v___x_450_ = lean_nat_sub(v_i_388_, v_j_389_);
lean_dec(v_j_389_);
lean_dec(v_i_388_);
v___x_461_ = lean_nat_dec_le(v___x_450_, v_b_387_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_462_ = lean_nat_add(v_startPos_406_, v_b_387_);
lean_dec(v_b_387_);
v___x_463_ = lean_nat_dec_le(v_stopPos_407_, v___x_462_);
if (v___x_463_ == 0)
{
v___y_452_ = v___x_462_;
goto v___jp_451_;
}
else
{
lean_dec(v___x_462_);
lean_inc(v_stopPos_407_);
v___y_452_ = v_stopPos_407_;
goto v___jp_451_;
}
}
else
{
lean_dec(v___x_450_);
lean_del_object(v___x_437_);
lean_dec(v_stopPos_407_);
lean_dec(v_startPos_406_);
lean_dec_ref(v_str_405_);
lean_dec(v_b_387_);
v___y_446_ = v___x_444_;
goto v___jp_445_;
}
v___jp_445_:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_447_, 0, v___y_446_);
lean_ctor_set(v___x_447_, 1, v_r_390_);
v___x_448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_444_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
v___x_449_ = l_List_reverse___redArg(v___x_448_);
return v___x_449_;
}
v___jp_451_:
{
lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_453_ = lean_nat_add(v_startPos_406_, v___x_450_);
lean_dec(v___x_450_);
lean_dec(v_startPos_406_);
v___x_454_ = lean_nat_dec_le(v_stopPos_407_, v___x_453_);
if (v___x_454_ == 0)
{
lean_object* v___x_456_; 
lean_dec(v_stopPos_407_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 2, v___x_453_);
lean_ctor_set(v___x_437_, 1, v___y_452_);
v___x_456_ = v___x_437_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_str_405_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v___y_452_);
lean_ctor_set(v_reuseFailAlloc_457_, 2, v___x_453_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
v___y_446_ = v___x_456_;
goto v___jp_445_;
}
}
else
{
lean_object* v___x_459_; 
lean_dec(v___x_453_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 1, v___y_452_);
v___x_459_ = v___x_437_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_str_405_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v___y_452_);
lean_ctor_set(v_reuseFailAlloc_460_, 2, v_stopPos_407_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
v___y_446_ = v___x_459_;
goto v___jp_445_;
}
}
}
}
}
}
else
{
lean_object* v___x_468_; uint32_t v___x_469_; uint32_t v___x_470_; uint8_t v___x_471_; 
v___x_468_ = lean_nat_add(v_startPos_406_, v_i_388_);
v___x_469_ = lean_string_utf8_get(v_str_405_, v___x_468_);
v___x_470_ = lean_string_utf8_get(v_sep_386_, v_j_389_);
v___x_471_ = lean_uint32_dec_eq(v___x_469_, v___x_470_);
if (v___x_471_ == 0)
{
uint8_t v_decide_472_; 
lean_dec(v_j_389_);
v_decide_472_ = lean_nat_dec_eq(v___x_468_, v_stopPos_407_);
if (v_decide_472_ == 0)
{
lean_object* v___x_473_; lean_object* v___x_474_; 
lean_dec(v_i_388_);
v___x_473_ = lean_string_utf8_next(v_str_405_, v___x_468_);
lean_dec(v___x_468_);
v___x_474_ = lean_nat_sub(v___x_473_, v_startPos_406_);
lean_dec(v___x_473_);
v___y_396_ = v___x_474_;
goto v___jp_395_;
}
else
{
lean_dec(v___x_468_);
v___y_396_ = v_i_388_;
goto v___jp_395_;
}
}
else
{
uint8_t v_decide_475_; 
v_decide_475_ = lean_nat_dec_eq(v___x_468_, v_stopPos_407_);
if (v_decide_475_ == 0)
{
lean_object* v___x_476_; lean_object* v___x_477_; 
lean_dec(v_i_388_);
v___x_476_ = lean_string_utf8_next(v_str_405_, v___x_468_);
lean_dec(v___x_468_);
v___x_477_ = lean_nat_sub(v___x_476_, v_startPos_406_);
lean_dec(v___x_476_);
v___y_418_ = v___x_477_;
goto v___jp_417_;
}
else
{
lean_dec(v___x_468_);
v___y_418_ = v_i_388_;
goto v___jp_417_;
}
}
}
v___jp_391_:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_393_, 0, v___y_392_);
lean_ctor_set(v___x_393_, 1, v_r_390_);
v___x_394_ = l_List_reverse___redArg(v___x_393_);
return v___x_394_;
}
v___jp_395_:
{
lean_object* v___x_397_; 
v___x_397_ = lean_unsigned_to_nat(0u);
v_i_388_ = v___y_396_;
v_j_389_ = v___x_397_;
goto _start;
}
v___jp_399_:
{
lean_object* v___x_403_; 
v___x_403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_403_, 0, v___y_402_);
lean_ctor_set(v___x_403_, 1, v_r_390_);
lean_inc(v___y_400_);
v_b_387_ = v___y_400_;
v_i_388_ = v___y_400_;
v_j_389_ = v___y_401_;
v_r_390_ = v___x_403_;
goto _start;
}
v___jp_408_:
{
lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_413_ = lean_nat_add(v_startPos_406_, v___y_411_);
lean_dec(v___y_411_);
v___x_414_ = lean_nat_dec_le(v_stopPos_407_, v___x_413_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; 
lean_inc_ref(v_str_405_);
v___x_415_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_415_, 0, v_str_405_);
lean_ctor_set(v___x_415_, 1, v___y_412_);
lean_ctor_set(v___x_415_, 2, v___x_413_);
v___y_400_ = v___y_409_;
v___y_401_ = v___y_410_;
v___y_402_ = v___x_415_;
goto v___jp_399_;
}
else
{
lean_object* v___x_416_; 
lean_dec(v___x_413_);
lean_inc(v_stopPos_407_);
lean_inc_ref(v_str_405_);
v___x_416_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_416_, 0, v_str_405_);
lean_ctor_set(v___x_416_, 1, v___y_412_);
lean_ctor_set(v___x_416_, 2, v_stopPos_407_);
v___y_400_ = v___y_409_;
v___y_401_ = v___y_410_;
v___y_402_ = v___x_416_;
goto v___jp_399_;
}
}
v___jp_417_:
{
lean_object* v_j_419_; uint8_t v___x_420_; 
v_j_419_ = lean_string_utf8_next(v_sep_386_, v_j_389_);
lean_dec(v_j_389_);
v___x_420_ = lean_string_utf8_at_end(v_sep_386_, v_j_419_);
if (v___x_420_ == 0)
{
v_i_388_ = v___y_418_;
v_j_389_ = v_j_419_;
goto _start;
}
else
{
lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_422_ = lean_unsigned_to_nat(0u);
v___x_423_ = lean_nat_sub(v___y_418_, v_j_419_);
lean_dec(v_j_419_);
v___x_424_ = lean_nat_dec_le(v___x_423_, v_b_387_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_425_ = lean_nat_add(v_startPos_406_, v_b_387_);
lean_dec(v_b_387_);
v___x_426_ = lean_nat_dec_le(v_stopPos_407_, v___x_425_);
if (v___x_426_ == 0)
{
v___y_409_ = v___y_418_;
v___y_410_ = v___x_422_;
v___y_411_ = v___x_423_;
v___y_412_ = v___x_425_;
goto v___jp_408_;
}
else
{
lean_dec(v___x_425_);
lean_inc(v_stopPos_407_);
v___y_409_ = v___y_418_;
v___y_410_ = v___x_422_;
v___y_411_ = v___x_423_;
v___y_412_ = v_stopPos_407_;
goto v___jp_408_;
}
}
else
{
lean_object* v___x_427_; 
lean_dec(v___x_423_);
lean_dec(v_b_387_);
v___x_427_ = ((lean_object*)(l_Substring_Raw_extract___closed__1));
v___y_400_ = v___y_418_;
v___y_401_ = v___x_422_;
v___y_402_ = v___x_427_;
goto v___jp_399_;
}
}
}
v___jp_428_:
{
lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_430_ = lean_nat_add(v_startPos_406_, v_i_388_);
lean_dec(v_i_388_);
lean_dec(v_startPos_406_);
v___x_431_ = lean_nat_dec_le(v_stopPos_407_, v___x_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; 
lean_dec(v_stopPos_407_);
v___x_432_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_432_, 0, v_str_405_);
lean_ctor_set(v___x_432_, 1, v___y_429_);
lean_ctor_set(v___x_432_, 2, v___x_430_);
v___y_392_ = v___x_432_;
goto v___jp_391_;
}
else
{
lean_object* v___x_433_; 
lean_dec(v___x_430_);
v___x_433_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_433_, 0, v_str_405_);
lean_ctor_set(v___x_433_, 1, v___y_429_);
lean_ctor_set(v___x_433_, 2, v_stopPos_407_);
v___y_392_ = v___x_433_;
goto v___jp_391_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___boxed(lean_object* v_s_478_, lean_object* v_sep_479_, lean_object* v_b_480_, lean_object* v_i_481_, lean_object* v_j_482_, lean_object* v_r_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop(v_s_478_, v_sep_479_, v_b_480_, v_i_481_, v_j_482_, v_r_483_);
lean_dec_ref(v_sep_479_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_splitOn(lean_object* v_s_485_, lean_object* v_sep_486_){
_start:
{
lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_487_ = ((lean_object*)(l_Substring_Raw_extract___closed__0));
v___x_488_ = lean_string_dec_eq(v_sep_486_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_489_ = lean_unsigned_to_nat(0u);
v___x_490_ = lean_box(0);
v___x_491_ = l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop(v_s_485_, v_sep_486_, v___x_489_, v___x_489_, v___x_489_, v___x_490_);
return v___x_491_;
}
else
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_box(0);
v___x_493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_493_, 0, v_s_485_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
return v___x_493_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_splitOn___boxed(lean_object* v_s_494_, lean_object* v_sep_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Substring_Raw_splitOn(v_s_494_, v_sep_495_);
lean_dec_ref(v_sep_495_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldl___redArg___lam__0(lean_object* v___y_497_, lean_object* v_f_498_, lean_object* v_it_499_, lean_object* v_acc_500_, lean_object* v_hP_501_, lean_object* v_recur_502_){
_start:
{
lean_object* v_str_503_; lean_object* v_startInclusive_504_; lean_object* v_endExclusive_505_; lean_object* v___x_506_; uint8_t v_decide_507_; 
v_str_503_ = lean_ctor_get(v___y_497_, 0);
v_startInclusive_504_ = lean_ctor_get(v___y_497_, 1);
v_endExclusive_505_ = lean_ctor_get(v___y_497_, 2);
v___x_506_ = lean_nat_sub(v_endExclusive_505_, v_startInclusive_504_);
v_decide_507_ = lean_nat_dec_eq(v_it_499_, v___x_506_);
lean_dec(v___x_506_);
if (v_decide_507_ == 0)
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; uint32_t v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_508_ = lean_nat_add(v_startInclusive_504_, v_it_499_);
v___x_509_ = lean_string_utf8_next_fast(v_str_503_, v___x_508_);
v___x_510_ = lean_nat_sub(v___x_509_, v_startInclusive_504_);
v___x_511_ = lean_string_utf8_get_fast(v_str_503_, v___x_508_);
lean_dec(v___x_508_);
v___x_512_ = lean_box_uint32(v___x_511_);
v___x_513_ = lean_apply_2(v_f_498_, v_acc_500_, v___x_512_);
v___x_514_ = lean_apply_4(v_recur_502_, v___x_510_, v___x_513_, lean_box(0), lean_box(0));
return v___x_514_;
}
else
{
lean_dec(v_recur_502_);
lean_dec(v_f_498_);
return v_acc_500_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldl___redArg___lam__0___boxed(lean_object* v___y_515_, lean_object* v_f_516_, lean_object* v_it_517_, lean_object* v_acc_518_, lean_object* v_hP_519_, lean_object* v_recur_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Substring_Raw_foldl___redArg___lam__0(v___y_515_, v_f_516_, v_it_517_, v_acc_518_, v_hP_519_, v_recur_520_);
lean_dec(v_it_517_);
lean_dec_ref(v___y_515_);
return v_res_521_;
}
}
static lean_object* _init_l_Substring_Raw_foldl___redArg___closed__3(void){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_525_ = ((lean_object*)(l_Substring_Raw_foldl___redArg___closed__2));
v___x_526_ = lean_unsigned_to_nat(14u);
v___x_527_ = lean_unsigned_to_nat(22u);
v___x_528_ = ((lean_object*)(l_Substring_Raw_foldl___redArg___closed__1));
v___x_529_ = ((lean_object*)(l_Substring_Raw_foldl___redArg___closed__0));
v___x_530_ = l_mkPanicMessageWithDecl(v___x_529_, v___x_528_, v___x_527_, v___x_526_, v___x_525_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldl___redArg(lean_object* v_f_531_, lean_object* v_init_532_, lean_object* v_s_533_){
_start:
{
lean_object* v___y_535_; lean_object* v_str_539_; lean_object* v_startPos_540_; lean_object* v_stopPos_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_555_; 
v_str_539_ = lean_ctor_get(v_s_533_, 0);
v_startPos_540_ = lean_ctor_get(v_s_533_, 1);
v_stopPos_541_ = lean_ctor_get(v_s_533_, 2);
v_isSharedCheck_555_ = !lean_is_exclusive(v_s_533_);
if (v_isSharedCheck_555_ == 0)
{
v___x_543_ = v_s_533_;
v_isShared_544_ = v_isSharedCheck_555_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_stopPos_541_);
lean_inc(v_startPos_540_);
lean_inc(v_str_539_);
lean_dec(v_s_533_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_555_;
goto v_resetjp_542_;
}
v___jp_534_:
{
lean_object* v___f_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___f_536_ = lean_alloc_closure((void*)(l_Substring_Raw_foldl___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_536_, 0, v___y_535_);
lean_closure_set(v___f_536_, 1, v_f_531_);
v___x_537_ = lean_unsigned_to_nat(0u);
v___x_538_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_536_, v___x_537_, v_init_532_, lean_box(0));
return v___x_538_;
}
v_resetjp_542_:
{
lean_object* v___x_545_; uint8_t v___x_549_; 
v___x_545_ = l_String_instInhabitedSlice;
v___x_549_ = lean_string_is_valid_pos(v_str_539_, v_startPos_540_);
if (v___x_549_ == 0)
{
lean_del_object(v___x_543_);
lean_dec(v_stopPos_541_);
lean_dec(v_startPos_540_);
lean_dec_ref(v_str_539_);
goto v___jp_546_;
}
else
{
uint8_t v___x_550_; 
v___x_550_ = lean_string_is_valid_pos(v_str_539_, v_stopPos_541_);
if (v___x_550_ == 0)
{
lean_del_object(v___x_543_);
lean_dec(v_stopPos_541_);
lean_dec(v_startPos_540_);
lean_dec_ref(v_str_539_);
goto v___jp_546_;
}
else
{
uint8_t v___x_551_; 
v___x_551_ = lean_nat_dec_le(v_startPos_540_, v_stopPos_541_);
if (v___x_551_ == 0)
{
lean_del_object(v___x_543_);
lean_dec(v_stopPos_541_);
lean_dec(v_startPos_540_);
lean_dec_ref(v_str_539_);
goto v___jp_546_;
}
else
{
lean_object* v___x_553_; 
if (v_isShared_544_ == 0)
{
v___x_553_ = v___x_543_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_str_539_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_startPos_540_);
lean_ctor_set(v_reuseFailAlloc_554_, 2, v_stopPos_541_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
v___y_535_ = v___x_553_;
goto v___jp_534_;
}
}
}
}
v___jp_546_:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_548_ = l_panic___redArg(v___x_545_, v___x_547_);
v___y_535_ = v___x_548_;
goto v___jp_534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldl(lean_object* v_00_u03b1_556_, lean_object* v_f_557_, lean_object* v_init_558_, lean_object* v_s_559_){
_start:
{
lean_object* v___y_561_; lean_object* v_str_565_; lean_object* v_startPos_566_; lean_object* v_stopPos_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_581_; 
v_str_565_ = lean_ctor_get(v_s_559_, 0);
v_startPos_566_ = lean_ctor_get(v_s_559_, 1);
v_stopPos_567_ = lean_ctor_get(v_s_559_, 2);
v_isSharedCheck_581_ = !lean_is_exclusive(v_s_559_);
if (v_isSharedCheck_581_ == 0)
{
v___x_569_ = v_s_559_;
v_isShared_570_ = v_isSharedCheck_581_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_stopPos_567_);
lean_inc(v_startPos_566_);
lean_inc(v_str_565_);
lean_dec(v_s_559_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_581_;
goto v_resetjp_568_;
}
v___jp_560_:
{
lean_object* v___f_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___f_562_ = lean_alloc_closure((void*)(l_Substring_Raw_foldl___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_562_, 0, v___y_561_);
lean_closure_set(v___f_562_, 1, v_f_557_);
v___x_563_ = lean_unsigned_to_nat(0u);
v___x_564_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_562_, v___x_563_, v_init_558_, lean_box(0));
return v___x_564_;
}
v_resetjp_568_:
{
lean_object* v___x_571_; uint8_t v___x_575_; 
v___x_571_ = l_String_instInhabitedSlice;
v___x_575_ = lean_string_is_valid_pos(v_str_565_, v_startPos_566_);
if (v___x_575_ == 0)
{
lean_del_object(v___x_569_);
lean_dec(v_stopPos_567_);
lean_dec(v_startPos_566_);
lean_dec_ref(v_str_565_);
goto v___jp_572_;
}
else
{
uint8_t v___x_576_; 
v___x_576_ = lean_string_is_valid_pos(v_str_565_, v_stopPos_567_);
if (v___x_576_ == 0)
{
lean_del_object(v___x_569_);
lean_dec(v_stopPos_567_);
lean_dec(v_startPos_566_);
lean_dec_ref(v_str_565_);
goto v___jp_572_;
}
else
{
uint8_t v___x_577_; 
v___x_577_ = lean_nat_dec_le(v_startPos_566_, v_stopPos_567_);
if (v___x_577_ == 0)
{
lean_del_object(v___x_569_);
lean_dec(v_stopPos_567_);
lean_dec(v_startPos_566_);
lean_dec_ref(v_str_565_);
goto v___jp_572_;
}
else
{
lean_object* v___x_579_; 
if (v_isShared_570_ == 0)
{
v___x_579_ = v___x_569_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_str_565_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v_startPos_566_);
lean_ctor_set(v_reuseFailAlloc_580_, 2, v_stopPos_567_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
v___y_561_ = v___x_579_;
goto v___jp_560_;
}
}
}
}
v___jp_572_:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_574_ = l_panic___redArg(v___x_571_, v___x_573_);
v___y_561_ = v___x_574_;
goto v___jp_560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr___redArg___lam__0(lean_object* v___y_582_, lean_object* v_f_583_, lean_object* v_it_584_, lean_object* v_acc_585_, lean_object* v_hP_586_, lean_object* v_recur_587_){
_start:
{
lean_object* v___x_588_; uint8_t v_decide_589_; 
v___x_588_ = lean_unsigned_to_nat(0u);
v_decide_589_ = lean_nat_dec_eq(v_it_584_, v___x_588_);
if (v_decide_589_ == 0)
{
lean_object* v_str_590_; lean_object* v_startInclusive_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v_prevPos_594_; lean_object* v___x_595_; uint32_t v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v_str_590_ = lean_ctor_get(v___y_582_, 0);
v_startInclusive_591_ = lean_ctor_get(v___y_582_, 1);
v___x_592_ = lean_unsigned_to_nat(1u);
v___x_593_ = lean_nat_sub(v_it_584_, v___x_592_);
v_prevPos_594_ = l_String_Slice_posLE(v___y_582_, v___x_593_);
v___x_595_ = lean_nat_add(v_startInclusive_591_, v_prevPos_594_);
v___x_596_ = lean_string_utf8_get_fast(v_str_590_, v___x_595_);
lean_dec(v___x_595_);
v___x_597_ = lean_box_uint32(v___x_596_);
v___x_598_ = lean_apply_2(v_f_583_, v___x_597_, v_acc_585_);
v___x_599_ = lean_apply_4(v_recur_587_, v_prevPos_594_, v___x_598_, lean_box(0), lean_box(0));
return v___x_599_;
}
else
{
lean_dec(v_recur_587_);
lean_dec(v_f_583_);
return v_acc_585_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr___redArg___lam__0___boxed(lean_object* v___y_600_, lean_object* v_f_601_, lean_object* v_it_602_, lean_object* v_acc_603_, lean_object* v_hP_604_, lean_object* v_recur_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Substring_Raw_foldr___redArg___lam__0(v___y_600_, v_f_601_, v_it_602_, v_acc_603_, v_hP_604_, v_recur_605_);
lean_dec(v_it_602_);
lean_dec_ref(v___y_600_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr___redArg(lean_object* v_f_607_, lean_object* v_init_608_, lean_object* v_s_609_){
_start:
{
lean_object* v___y_611_; lean_object* v_str_615_; lean_object* v_startPos_616_; lean_object* v_stopPos_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_631_; 
v_str_615_ = lean_ctor_get(v_s_609_, 0);
v_startPos_616_ = lean_ctor_get(v_s_609_, 1);
v_stopPos_617_ = lean_ctor_get(v_s_609_, 2);
v_isSharedCheck_631_ = !lean_is_exclusive(v_s_609_);
if (v_isSharedCheck_631_ == 0)
{
v___x_619_ = v_s_609_;
v_isShared_620_ = v_isSharedCheck_631_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_stopPos_617_);
lean_inc(v_startPos_616_);
lean_inc(v_str_615_);
lean_dec(v_s_609_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_631_;
goto v_resetjp_618_;
}
v___jp_610_:
{
lean_object* v___f_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
lean_inc_ref(v___y_611_);
v___f_612_ = lean_alloc_closure((void*)(l_Substring_Raw_foldr___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_612_, 0, v___y_611_);
lean_closure_set(v___f_612_, 1, v_f_607_);
v___x_613_ = l_String_Slice_revPositions(v___y_611_);
lean_dec_ref(v___y_611_);
v___x_614_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_612_, v___x_613_, v_init_608_, lean_box(0));
return v___x_614_;
}
v_resetjp_618_:
{
lean_object* v___x_621_; uint8_t v___x_625_; 
v___x_621_ = l_String_instInhabitedSlice;
v___x_625_ = lean_string_is_valid_pos(v_str_615_, v_startPos_616_);
if (v___x_625_ == 0)
{
lean_del_object(v___x_619_);
lean_dec(v_stopPos_617_);
lean_dec(v_startPos_616_);
lean_dec_ref(v_str_615_);
goto v___jp_622_;
}
else
{
uint8_t v___x_626_; 
v___x_626_ = lean_string_is_valid_pos(v_str_615_, v_stopPos_617_);
if (v___x_626_ == 0)
{
lean_del_object(v___x_619_);
lean_dec(v_stopPos_617_);
lean_dec(v_startPos_616_);
lean_dec_ref(v_str_615_);
goto v___jp_622_;
}
else
{
uint8_t v___x_627_; 
v___x_627_ = lean_nat_dec_le(v_startPos_616_, v_stopPos_617_);
if (v___x_627_ == 0)
{
lean_del_object(v___x_619_);
lean_dec(v_stopPos_617_);
lean_dec(v_startPos_616_);
lean_dec_ref(v_str_615_);
goto v___jp_622_;
}
else
{
lean_object* v___x_629_; 
if (v_isShared_620_ == 0)
{
v___x_629_ = v___x_619_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_str_615_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_startPos_616_);
lean_ctor_set(v_reuseFailAlloc_630_, 2, v_stopPos_617_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
v___y_611_ = v___x_629_;
goto v___jp_610_;
}
}
}
}
v___jp_622_:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_624_ = l_panic___redArg(v___x_621_, v___x_623_);
v___y_611_ = v___x_624_;
goto v___jp_610_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr(lean_object* v_00_u03b1_632_, lean_object* v_f_633_, lean_object* v_init_634_, lean_object* v_s_635_){
_start:
{
lean_object* v___y_637_; lean_object* v_str_641_; lean_object* v_startPos_642_; lean_object* v_stopPos_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_657_; 
v_str_641_ = lean_ctor_get(v_s_635_, 0);
v_startPos_642_ = lean_ctor_get(v_s_635_, 1);
v_stopPos_643_ = lean_ctor_get(v_s_635_, 2);
v_isSharedCheck_657_ = !lean_is_exclusive(v_s_635_);
if (v_isSharedCheck_657_ == 0)
{
v___x_645_ = v_s_635_;
v_isShared_646_ = v_isSharedCheck_657_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_stopPos_643_);
lean_inc(v_startPos_642_);
lean_inc(v_str_641_);
lean_dec(v_s_635_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_657_;
goto v_resetjp_644_;
}
v___jp_636_:
{
lean_object* v___f_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
lean_inc_ref(v___y_637_);
v___f_638_ = lean_alloc_closure((void*)(l_Substring_Raw_foldr___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_638_, 0, v___y_637_);
lean_closure_set(v___f_638_, 1, v_f_633_);
v___x_639_ = l_String_Slice_revPositions(v___y_637_);
lean_dec_ref(v___y_637_);
v___x_640_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_638_, v___x_639_, v_init_634_, lean_box(0));
return v___x_640_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; uint8_t v___x_651_; 
v___x_647_ = l_String_instInhabitedSlice;
v___x_651_ = lean_string_is_valid_pos(v_str_641_, v_startPos_642_);
if (v___x_651_ == 0)
{
lean_del_object(v___x_645_);
lean_dec(v_stopPos_643_);
lean_dec(v_startPos_642_);
lean_dec_ref(v_str_641_);
goto v___jp_648_;
}
else
{
uint8_t v___x_652_; 
v___x_652_ = lean_string_is_valid_pos(v_str_641_, v_stopPos_643_);
if (v___x_652_ == 0)
{
lean_del_object(v___x_645_);
lean_dec(v_stopPos_643_);
lean_dec(v_startPos_642_);
lean_dec_ref(v_str_641_);
goto v___jp_648_;
}
else
{
uint8_t v___x_653_; 
v___x_653_ = lean_nat_dec_le(v_startPos_642_, v_stopPos_643_);
if (v___x_653_ == 0)
{
lean_del_object(v___x_645_);
lean_dec(v_stopPos_643_);
lean_dec(v_startPos_642_);
lean_dec_ref(v_str_641_);
goto v___jp_648_;
}
else
{
lean_object* v___x_655_; 
if (v_isShared_646_ == 0)
{
v___x_655_ = v___x_645_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_str_641_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v_startPos_642_);
lean_ctor_set(v_reuseFailAlloc_656_, 2, v_stopPos_643_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
v___y_637_ = v___x_655_;
goto v___jp_636_;
}
}
}
}
v___jp_648_:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_650_ = l_panic___redArg(v___x_647_, v___x_649_);
v___y_637_ = v___x_650_;
goto v___jp_636_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_any___lam__0(lean_object* v___x_658_, lean_object* v_s_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(v_s_659_, v___x_658_, v___y_660_, lean_box(0), lean_box(0), v___y_663_, v___y_664_, v___y_665_);
return v___x_666_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_any(lean_object* v_s_667_, lean_object* v_p_668_){
_start:
{
lean_object* v___x_669_; lean_object* v_str_670_; lean_object* v_startPos_671_; lean_object* v_stopPos_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_690_; 
lean_inc_ref(v_p_668_);
v___x_669_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v_p_668_);
v_str_670_ = lean_ctor_get(v_s_667_, 0);
v_startPos_671_ = lean_ctor_get(v_s_667_, 1);
v_stopPos_672_ = lean_ctor_get(v_s_667_, 2);
v_isSharedCheck_690_ = !lean_is_exclusive(v_s_667_);
if (v_isSharedCheck_690_ == 0)
{
v___x_674_ = v_s_667_;
v_isShared_675_ = v_isSharedCheck_690_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_stopPos_672_);
lean_inc(v_startPos_671_);
lean_inc(v_str_670_);
lean_dec(v_s_667_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_690_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_676_; lean_object* v___f_677_; lean_object* v___x_678_; uint8_t v___x_683_; 
v___x_676_ = l_String_instInhabitedSlice;
v___f_677_ = lean_alloc_closure((void*)(l_Substring_Raw_any___lam__0), 8, 1);
lean_closure_set(v___f_677_, 0, v___x_669_);
v___x_678_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_678_, 0, lean_box(0));
lean_closure_set(v___x_678_, 1, v_p_668_);
v___x_683_ = lean_string_is_valid_pos(v_str_670_, v_startPos_671_);
if (v___x_683_ == 0)
{
lean_del_object(v___x_674_);
lean_dec(v_stopPos_672_);
lean_dec(v_startPos_671_);
lean_dec_ref(v_str_670_);
goto v___jp_679_;
}
else
{
uint8_t v___x_684_; 
v___x_684_ = lean_string_is_valid_pos(v_str_670_, v_stopPos_672_);
if (v___x_684_ == 0)
{
lean_del_object(v___x_674_);
lean_dec(v_stopPos_672_);
lean_dec(v_startPos_671_);
lean_dec_ref(v_str_670_);
goto v___jp_679_;
}
else
{
uint8_t v___x_685_; 
v___x_685_ = lean_nat_dec_le(v_startPos_671_, v_stopPos_672_);
if (v___x_685_ == 0)
{
lean_del_object(v___x_674_);
lean_dec(v_stopPos_672_);
lean_dec(v_startPos_671_);
lean_dec_ref(v_str_670_);
goto v___jp_679_;
}
else
{
lean_object* v___x_687_; 
if (v_isShared_675_ == 0)
{
v___x_687_ = v___x_674_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_str_670_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_startPos_671_);
lean_ctor_set(v_reuseFailAlloc_689_, 2, v_stopPos_672_);
v___x_687_ = v_reuseFailAlloc_689_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
uint8_t v___x_688_; 
v___x_688_ = l_String_Slice_contains___redArg(v___f_677_, v___x_687_, v___x_678_);
return v___x_688_;
}
}
}
}
v___jp_679_:
{
lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_680_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_681_ = l_panic___redArg(v___x_676_, v___x_680_);
v___x_682_ = l_String_Slice_contains___redArg(v___f_677_, v___x_681_, v___x_678_);
return v___x_682_;
}
}
}
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
LEAN_EXPORT uint8_t l_Substring_Raw_all(lean_object* v_s_695_, lean_object* v_p_696_){
_start:
{
lean_object* v___y_698_; lean_object* v_startInclusive_699_; lean_object* v_endExclusive_700_; lean_object* v_str_706_; lean_object* v_startPos_707_; lean_object* v_stopPos_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_724_; 
v_str_706_ = lean_ctor_get(v_s_695_, 0);
v_startPos_707_ = lean_ctor_get(v_s_695_, 1);
v_stopPos_708_ = lean_ctor_get(v_s_695_, 2);
v_isSharedCheck_724_ = !lean_is_exclusive(v_s_695_);
if (v_isSharedCheck_724_ == 0)
{
v___x_710_ = v_s_695_;
v_isShared_711_ = v_isSharedCheck_724_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_stopPos_708_);
lean_inc(v_startPos_707_);
lean_inc(v_str_706_);
lean_dec(v_s_695_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_724_;
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
lean_object* v___x_712_; uint8_t v___x_718_; 
v___x_712_ = l_String_instInhabitedSlice;
v___x_718_ = lean_string_is_valid_pos(v_str_706_, v_startPos_707_);
if (v___x_718_ == 0)
{
lean_del_object(v___x_710_);
lean_dec(v_stopPos_708_);
lean_dec(v_startPos_707_);
lean_dec_ref(v_str_706_);
goto v___jp_713_;
}
else
{
uint8_t v___x_719_; 
v___x_719_ = lean_string_is_valid_pos(v_str_706_, v_stopPos_708_);
if (v___x_719_ == 0)
{
lean_del_object(v___x_710_);
lean_dec(v_stopPos_708_);
lean_dec(v_startPos_707_);
lean_dec_ref(v_str_706_);
goto v___jp_713_;
}
else
{
uint8_t v___x_720_; 
v___x_720_ = lean_nat_dec_le(v_startPos_707_, v_stopPos_708_);
if (v___x_720_ == 0)
{
lean_del_object(v___x_710_);
lean_dec(v_stopPos_708_);
lean_dec(v_startPos_707_);
lean_dec_ref(v_str_706_);
goto v___jp_713_;
}
else
{
lean_object* v___x_722_; 
lean_inc(v_stopPos_708_);
lean_inc(v_startPos_707_);
if (v_isShared_711_ == 0)
{
v___x_722_ = v___x_710_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_str_706_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_startPos_707_);
lean_ctor_set(v_reuseFailAlloc_723_, 2, v_stopPos_708_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
v___y_698_ = v___x_722_;
v_startInclusive_699_ = v_startPos_707_;
v_endExclusive_700_ = v_stopPos_708_;
goto v___jp_697_;
}
}
}
}
v___jp_713_:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v_startInclusive_716_; lean_object* v_endExclusive_717_; 
v___x_714_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_715_ = l_panic___redArg(v___x_712_, v___x_714_);
v_startInclusive_716_ = lean_ctor_get(v___x_715_, 1);
lean_inc(v_startInclusive_716_);
v_endExclusive_717_ = lean_ctor_get(v___x_715_, 2);
lean_inc(v_endExclusive_717_);
v___y_698_ = v___x_715_;
v_startInclusive_699_ = v_startInclusive_716_;
v_endExclusive_700_ = v_endExclusive_717_;
goto v___jp_697_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_all___boxed(lean_object* v_s_725_, lean_object* v_p_726_){
_start:
{
uint8_t v_res_727_; lean_object* v_r_728_; 
v_res_727_ = l_Substring_Raw_all(v_s_725_, v_p_726_);
v_r_728_ = lean_box(v_res_727_);
return v_r_728_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(lean_object* v_msg_729_){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = l_String_instInhabitedSlice;
v___x_731_ = lean_panic_fn_borrowed(v___x_730_, v_msg_729_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0(lean_object* v_p_732_, lean_object* v_s_733_, lean_object* v_pos_734_){
_start:
{
lean_object* v_str_735_; lean_object* v_startInclusive_736_; lean_object* v_endExclusive_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; uint8_t v_decide_741_; 
v_str_735_ = lean_ctor_get(v_s_733_, 0);
v_startInclusive_736_ = lean_ctor_get(v_s_733_, 1);
v_endExclusive_737_ = lean_ctor_get(v_s_733_, 2);
v___x_738_ = lean_nat_add(v_startInclusive_736_, v_pos_734_);
v___x_739_ = lean_unsigned_to_nat(0u);
v___x_740_ = lean_nat_sub(v_endExclusive_737_, v___x_738_);
v_decide_741_ = lean_nat_dec_eq(v___x_739_, v___x_740_);
lean_dec(v___x_740_);
if (v_decide_741_ == 0)
{
uint32_t v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_742_ = lean_string_utf8_get_fast(v_str_735_, v___x_738_);
v___x_743_ = lean_box_uint32(v___x_742_);
lean_inc_ref(v_p_732_);
v___x_744_ = lean_apply_1(v_p_732_, v___x_743_);
v___x_745_ = lean_unbox(v___x_744_);
if (v___x_745_ == 0)
{
lean_dec(v___x_738_);
lean_dec_ref(v_p_732_);
return v_pos_734_;
}
else
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_746_ = lean_string_utf8_next_fast(v_str_735_, v___x_738_);
v___x_747_ = lean_nat_sub(v___x_746_, v___x_738_);
lean_dec(v___x_738_);
v___x_748_ = lean_nat_add(v_pos_734_, v___x_747_);
lean_dec(v___x_747_);
v___x_749_ = lean_unsigned_to_nat(1u);
v___x_750_ = lean_nat_add(v_pos_734_, v___x_749_);
v___x_751_ = lean_nat_dec_le(v___x_750_, v___x_748_);
lean_dec(v___x_750_);
if (v___x_751_ == 0)
{
lean_dec(v___x_748_);
lean_dec_ref(v_p_732_);
return v_pos_734_;
}
else
{
lean_dec(v_pos_734_);
v_pos_734_ = v___x_748_;
goto _start;
}
}
}
else
{
lean_dec(v___x_738_);
lean_dec_ref(v_p_732_);
return v_pos_734_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0___boxed(lean_object* v_p_753_, lean_object* v_s_754_, lean_object* v_pos_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0(v_p_753_, v_s_754_, v_pos_755_);
lean_dec_ref(v_s_754_);
return v_res_756_;
}
}
LEAN_EXPORT uint8_t lean_substring_all(lean_object* v_s_757_, lean_object* v_p_758_){
_start:
{
lean_object* v___y_760_; lean_object* v_startInclusive_761_; lean_object* v_endExclusive_762_; lean_object* v_str_772_; lean_object* v_startPos_773_; lean_object* v_stopPos_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_784_; 
v_str_772_ = lean_ctor_get(v_s_757_, 0);
v_startPos_773_ = lean_ctor_get(v_s_757_, 1);
v_stopPos_774_ = lean_ctor_get(v_s_757_, 2);
v_isSharedCheck_784_ = !lean_is_exclusive(v_s_757_);
if (v_isSharedCheck_784_ == 0)
{
v___x_776_ = v_s_757_;
v_isShared_777_ = v_isSharedCheck_784_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_stopPos_774_);
lean_inc(v_startPos_773_);
lean_inc(v_str_772_);
lean_dec(v_s_757_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_784_;
goto v_resetjp_775_;
}
v___jp_759_:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v_decide_766_; 
v___x_763_ = lean_unsigned_to_nat(0u);
v___x_764_ = l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0(v_p_758_, v___y_760_, v___x_763_);
lean_dec_ref(v___y_760_);
v___x_765_ = lean_nat_sub(v_endExclusive_762_, v_startInclusive_761_);
lean_dec(v_startInclusive_761_);
lean_dec(v_endExclusive_762_);
v_decide_766_ = lean_nat_dec_eq(v___x_764_, v___x_765_);
lean_dec(v___x_765_);
lean_dec(v___x_764_);
return v_decide_766_;
}
v___jp_767_:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v_startInclusive_770_; lean_object* v_endExclusive_771_; 
v___x_768_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_769_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_768_);
v_startInclusive_770_ = lean_ctor_get(v___x_769_, 1);
lean_inc(v_startInclusive_770_);
v_endExclusive_771_ = lean_ctor_get(v___x_769_, 2);
lean_inc(v_endExclusive_771_);
v___y_760_ = v___x_769_;
v_startInclusive_761_ = v_startInclusive_770_;
v_endExclusive_762_ = v_endExclusive_771_;
goto v___jp_759_;
}
v_resetjp_775_:
{
uint8_t v___x_778_; 
v___x_778_ = lean_string_is_valid_pos(v_str_772_, v_startPos_773_);
if (v___x_778_ == 0)
{
lean_del_object(v___x_776_);
lean_dec(v_stopPos_774_);
lean_dec(v_startPos_773_);
lean_dec_ref(v_str_772_);
goto v___jp_767_;
}
else
{
uint8_t v___x_779_; 
v___x_779_ = lean_string_is_valid_pos(v_str_772_, v_stopPos_774_);
if (v___x_779_ == 0)
{
lean_del_object(v___x_776_);
lean_dec(v_stopPos_774_);
lean_dec(v_startPos_773_);
lean_dec_ref(v_str_772_);
goto v___jp_767_;
}
else
{
uint8_t v___x_780_; 
v___x_780_ = lean_nat_dec_le(v_startPos_773_, v_stopPos_774_);
if (v___x_780_ == 0)
{
lean_del_object(v___x_776_);
lean_dec(v_stopPos_774_);
lean_dec(v_startPos_773_);
lean_dec_ref(v_str_772_);
goto v___jp_767_;
}
else
{
lean_object* v___x_782_; 
lean_inc(v_stopPos_774_);
lean_inc(v_startPos_773_);
if (v_isShared_777_ == 0)
{
v___x_782_ = v___x_776_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_str_772_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_startPos_773_);
lean_ctor_set(v_reuseFailAlloc_783_, 2, v_stopPos_774_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
v___y_760_ = v___x_782_;
v_startInclusive_761_ = v_startPos_773_;
v_endExclusive_762_ = v_stopPos_774_;
goto v___jp_759_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_allImpl___boxed(lean_object* v_s_785_, lean_object* v_p_786_){
_start:
{
uint8_t v_res_787_; lean_object* v_r_788_; 
v_res_787_ = lean_substring_all(v_s_785_, v_p_786_);
v_r_788_ = lean_box(v_res_787_);
return v_r_788_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_contains___lam__0(uint32_t v_c_789_, uint32_t v_a_790_){
_start:
{
uint8_t v___x_791_; 
v___x_791_ = lean_uint32_dec_eq(v_a_790_, v_c_789_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_contains___lam__0___boxed(lean_object* v_c_792_, lean_object* v_a_793_){
_start:
{
uint32_t v_c_boxed_794_; uint32_t v_a_boxed_795_; uint8_t v_res_796_; lean_object* v_r_797_; 
v_c_boxed_794_ = lean_unbox_uint32(v_c_792_);
lean_dec(v_c_792_);
v_a_boxed_795_ = lean_unbox_uint32(v_a_793_);
lean_dec(v_a_793_);
v_res_796_ = l_Substring_Raw_contains___lam__0(v_c_boxed_794_, v_a_boxed_795_);
v_r_797_ = lean_box(v_res_796_);
return v_r_797_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_contains(lean_object* v_s_798_, uint32_t v_c_799_){
_start:
{
lean_object* v___x_800_; lean_object* v___f_801_; lean_object* v___x_802_; lean_object* v_str_803_; lean_object* v_startPos_804_; lean_object* v_stopPos_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_823_; 
v___x_800_ = lean_box_uint32(v_c_799_);
v___f_801_ = lean_alloc_closure((void*)(l_Substring_Raw_contains___lam__0___boxed), 2, 1);
lean_closure_set(v___f_801_, 0, v___x_800_);
lean_inc_ref(v___f_801_);
v___x_802_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___f_801_);
v_str_803_ = lean_ctor_get(v_s_798_, 0);
v_startPos_804_ = lean_ctor_get(v_s_798_, 1);
v_stopPos_805_ = lean_ctor_get(v_s_798_, 2);
v_isSharedCheck_823_ = !lean_is_exclusive(v_s_798_);
if (v_isSharedCheck_823_ == 0)
{
v___x_807_ = v_s_798_;
v_isShared_808_ = v_isSharedCheck_823_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_stopPos_805_);
lean_inc(v_startPos_804_);
lean_inc(v_str_803_);
lean_dec(v_s_798_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_823_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_809_; lean_object* v___f_810_; lean_object* v___x_811_; uint8_t v___x_816_; 
v___x_809_ = l_String_instInhabitedSlice;
v___f_810_ = lean_alloc_closure((void*)(l_Substring_Raw_any___lam__0), 8, 1);
lean_closure_set(v___f_810_, 0, v___x_802_);
v___x_811_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_811_, 0, lean_box(0));
lean_closure_set(v___x_811_, 1, v___f_801_);
v___x_816_ = lean_string_is_valid_pos(v_str_803_, v_startPos_804_);
if (v___x_816_ == 0)
{
lean_del_object(v___x_807_);
lean_dec(v_stopPos_805_);
lean_dec(v_startPos_804_);
lean_dec_ref(v_str_803_);
goto v___jp_812_;
}
else
{
uint8_t v___x_817_; 
v___x_817_ = lean_string_is_valid_pos(v_str_803_, v_stopPos_805_);
if (v___x_817_ == 0)
{
lean_del_object(v___x_807_);
lean_dec(v_stopPos_805_);
lean_dec(v_startPos_804_);
lean_dec_ref(v_str_803_);
goto v___jp_812_;
}
else
{
uint8_t v___x_818_; 
v___x_818_ = lean_nat_dec_le(v_startPos_804_, v_stopPos_805_);
if (v___x_818_ == 0)
{
lean_del_object(v___x_807_);
lean_dec(v_stopPos_805_);
lean_dec(v_startPos_804_);
lean_dec_ref(v_str_803_);
goto v___jp_812_;
}
else
{
lean_object* v___x_820_; 
if (v_isShared_808_ == 0)
{
v___x_820_ = v___x_807_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_str_803_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v_startPos_804_);
lean_ctor_set(v_reuseFailAlloc_822_, 2, v_stopPos_805_);
v___x_820_ = v_reuseFailAlloc_822_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
uint8_t v___x_821_; 
v___x_821_ = l_String_Slice_contains___redArg(v___f_810_, v___x_820_, v___x_811_);
return v___x_821_;
}
}
}
}
v___jp_812_:
{
lean_object* v___x_813_; lean_object* v___x_814_; uint8_t v___x_815_; 
v___x_813_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_814_ = l_panic___redArg(v___x_809_, v___x_813_);
v___x_815_ = l_String_Slice_contains___redArg(v___f_810_, v___x_814_, v___x_811_);
return v___x_815_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_contains___boxed(lean_object* v_s_824_, lean_object* v_c_825_){
_start:
{
uint32_t v_c_boxed_826_; uint8_t v_res_827_; lean_object* v_r_828_; 
v_c_boxed_826_ = lean_unbox_uint32(v_c_825_);
lean_dec(v_c_825_);
v_res_827_ = l_Substring_Raw_contains(v_s_824_, v_c_boxed_826_);
v_r_828_ = lean_box(v_res_827_);
return v_r_828_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux(lean_object* v_s_829_, lean_object* v_stopPos_830_, lean_object* v_p_831_, lean_object* v_i_832_){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_833_ = lean_unsigned_to_nat(1u);
v___x_834_ = lean_nat_add(v_i_832_, v___x_833_);
v___x_835_ = lean_nat_dec_le(v___x_834_, v_stopPos_830_);
lean_dec(v___x_834_);
if (v___x_835_ == 0)
{
lean_dec_ref(v_p_831_);
return v_i_832_;
}
else
{
uint32_t v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_836_ = lean_string_utf8_get(v_s_829_, v_i_832_);
v___x_837_ = lean_box_uint32(v___x_836_);
lean_inc_ref(v_p_831_);
v___x_838_ = lean_apply_1(v_p_831_, v___x_837_);
v___x_839_ = lean_unbox(v___x_838_);
if (v___x_839_ == 0)
{
lean_dec_ref(v_p_831_);
return v_i_832_;
}
else
{
lean_object* v___x_840_; 
v___x_840_ = lean_string_utf8_next(v_s_829_, v_i_832_);
lean_dec(v_i_832_);
v_i_832_ = v___x_840_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___boxed(lean_object* v_s_842_, lean_object* v_stopPos_843_, lean_object* v_p_844_, lean_object* v_i_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Substring_Raw_takeWhileAux(v_s_842_, v_stopPos_843_, v_p_844_, v_i_845_);
lean_dec(v_stopPos_843_);
lean_dec_ref(v_s_842_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhile(lean_object* v_x_847_, lean_object* v_x_848_){
_start:
{
lean_object* v_str_849_; lean_object* v_startPos_850_; lean_object* v_stopPos_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_859_; 
v_str_849_ = lean_ctor_get(v_x_847_, 0);
v_startPos_850_ = lean_ctor_get(v_x_847_, 1);
v_stopPos_851_ = lean_ctor_get(v_x_847_, 2);
v_isSharedCheck_859_ = !lean_is_exclusive(v_x_847_);
if (v_isSharedCheck_859_ == 0)
{
v___x_853_ = v_x_847_;
v_isShared_854_ = v_isSharedCheck_859_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_stopPos_851_);
lean_inc(v_startPos_850_);
lean_inc(v_str_849_);
lean_dec(v_x_847_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_859_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v_e_855_; lean_object* v___x_857_; 
lean_inc(v_startPos_850_);
v_e_855_ = l_Substring_Raw_takeWhileAux(v_str_849_, v_stopPos_851_, v_x_848_, v_startPos_850_);
lean_dec(v_stopPos_851_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 2, v_e_855_);
v___x_857_ = v___x_853_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_str_849_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v_startPos_850_);
lean_ctor_set(v_reuseFailAlloc_858_, 2, v_e_855_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(lean_object* v_a_860_, lean_object* v_s_861_, lean_object* v_stopPos_862_, lean_object* v_i_863_){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_864_ = lean_unsigned_to_nat(1u);
v___x_865_ = lean_nat_add(v_i_863_, v___x_864_);
v___x_866_ = lean_nat_dec_le(v___x_865_, v_stopPos_862_);
lean_dec(v___x_865_);
if (v___x_866_ == 0)
{
lean_dec_ref(v_a_860_);
return v_i_863_;
}
else
{
uint32_t v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; uint8_t v___x_870_; 
v___x_867_ = lean_string_utf8_get(v_s_861_, v_i_863_);
v___x_868_ = lean_box_uint32(v___x_867_);
lean_inc_ref(v_a_860_);
v___x_869_ = lean_apply_1(v_a_860_, v___x_868_);
v___x_870_ = lean_unbox(v___x_869_);
if (v___x_870_ == 0)
{
lean_dec_ref(v_a_860_);
return v_i_863_;
}
else
{
lean_object* v___x_871_; 
v___x_871_ = lean_string_utf8_next(v_s_861_, v_i_863_);
lean_dec(v_i_863_);
v_i_863_ = v___x_871_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0___boxed(lean_object* v_a_873_, lean_object* v_s_874_, lean_object* v_stopPos_875_, lean_object* v_i_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(v_a_873_, v_s_874_, v_stopPos_875_, v_i_876_);
lean_dec(v_stopPos_875_);
lean_dec_ref(v_s_874_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* lean_substring_takewhile(lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
lean_object* v_str_880_; lean_object* v_startPos_881_; lean_object* v_stopPos_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_890_; 
v_str_880_ = lean_ctor_get(v_a_878_, 0);
v_startPos_881_ = lean_ctor_get(v_a_878_, 1);
v_stopPos_882_ = lean_ctor_get(v_a_878_, 2);
v_isSharedCheck_890_ = !lean_is_exclusive(v_a_878_);
if (v_isSharedCheck_890_ == 0)
{
v___x_884_ = v_a_878_;
v_isShared_885_ = v_isSharedCheck_890_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_stopPos_882_);
lean_inc(v_startPos_881_);
lean_inc(v_str_880_);
lean_dec(v_a_878_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_890_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v_e_886_; lean_object* v___x_888_; 
lean_inc(v_startPos_881_);
v_e_886_ = l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(v_a_879_, v_str_880_, v_stopPos_882_, v_startPos_881_);
lean_dec(v_stopPos_882_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 2, v_e_886_);
v___x_888_ = v___x_884_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_str_880_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_startPos_881_);
lean_ctor_set(v_reuseFailAlloc_889_, 2, v_e_886_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropWhile(lean_object* v_x_891_, lean_object* v_x_892_){
_start:
{
lean_object* v_str_893_; lean_object* v_startPos_894_; lean_object* v_stopPos_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_903_; 
v_str_893_ = lean_ctor_get(v_x_891_, 0);
v_startPos_894_ = lean_ctor_get(v_x_891_, 1);
v_stopPos_895_ = lean_ctor_get(v_x_891_, 2);
v_isSharedCheck_903_ = !lean_is_exclusive(v_x_891_);
if (v_isSharedCheck_903_ == 0)
{
v___x_897_ = v_x_891_;
v_isShared_898_ = v_isSharedCheck_903_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_stopPos_895_);
lean_inc(v_startPos_894_);
lean_inc(v_str_893_);
lean_dec(v_x_891_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_903_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v_b_899_; lean_object* v___x_901_; 
v_b_899_ = l_Substring_Raw_takeWhileAux(v_str_893_, v_stopPos_895_, v_x_892_, v_startPos_894_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 1, v_b_899_);
v___x_901_ = v___x_897_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_str_893_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_b_899_);
lean_ctor_set(v_reuseFailAlloc_902_, 2, v_stopPos_895_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux(lean_object* v_s_904_, lean_object* v_begPos_905_, lean_object* v_p_906_, lean_object* v_i_907_){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; uint8_t v___x_910_; 
v___x_908_ = lean_unsigned_to_nat(1u);
v___x_909_ = lean_nat_add(v_begPos_905_, v___x_908_);
v___x_910_ = lean_nat_dec_le(v___x_909_, v_i_907_);
lean_dec(v___x_909_);
if (v___x_910_ == 0)
{
lean_dec_ref(v_p_906_);
return v_i_907_;
}
else
{
lean_object* v_i_x27_911_; uint32_t v_c_912_; lean_object* v___x_913_; lean_object* v___x_914_; uint8_t v___x_915_; 
v_i_x27_911_ = lean_string_utf8_prev(v_s_904_, v_i_907_);
v_c_912_ = lean_string_utf8_get(v_s_904_, v_i_x27_911_);
v___x_913_ = lean_box_uint32(v_c_912_);
lean_inc_ref(v_p_906_);
v___x_914_ = lean_apply_1(v_p_906_, v___x_913_);
v___x_915_ = lean_unbox(v___x_914_);
if (v___x_915_ == 0)
{
lean_dec(v_i_x27_911_);
lean_dec_ref(v_p_906_);
return v_i_907_;
}
else
{
lean_dec(v_i_907_);
v_i_907_ = v_i_x27_911_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux___boxed(lean_object* v_s_917_, lean_object* v_begPos_918_, lean_object* v_p_919_, lean_object* v_i_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Substring_Raw_takeRightWhileAux(v_s_917_, v_begPos_918_, v_p_919_, v_i_920_);
lean_dec(v_begPos_918_);
lean_dec_ref(v_s_917_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhile(lean_object* v_x_922_, lean_object* v_x_923_){
_start:
{
lean_object* v_str_924_; lean_object* v_startPos_925_; lean_object* v_stopPos_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_934_; 
v_str_924_ = lean_ctor_get(v_x_922_, 0);
v_startPos_925_ = lean_ctor_get(v_x_922_, 1);
v_stopPos_926_ = lean_ctor_get(v_x_922_, 2);
v_isSharedCheck_934_ = !lean_is_exclusive(v_x_922_);
if (v_isSharedCheck_934_ == 0)
{
v___x_928_ = v_x_922_;
v_isShared_929_ = v_isSharedCheck_934_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_stopPos_926_);
lean_inc(v_startPos_925_);
lean_inc(v_str_924_);
lean_dec(v_x_922_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_934_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v_b_930_; lean_object* v___x_932_; 
lean_inc(v_stopPos_926_);
v_b_930_ = l_Substring_Raw_takeRightWhileAux(v_str_924_, v_startPos_925_, v_x_923_, v_stopPos_926_);
lean_dec(v_startPos_925_);
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 1, v_b_930_);
v___x_932_ = v___x_928_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_str_924_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v_b_930_);
lean_ctor_set(v_reuseFailAlloc_933_, 2, v_stopPos_926_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropRightWhile(lean_object* v_x_935_, lean_object* v_x_936_){
_start:
{
lean_object* v_str_937_; lean_object* v_startPos_938_; lean_object* v_stopPos_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_947_; 
v_str_937_ = lean_ctor_get(v_x_935_, 0);
v_startPos_938_ = lean_ctor_get(v_x_935_, 1);
v_stopPos_939_ = lean_ctor_get(v_x_935_, 2);
v_isSharedCheck_947_ = !lean_is_exclusive(v_x_935_);
if (v_isSharedCheck_947_ == 0)
{
v___x_941_ = v_x_935_;
v_isShared_942_ = v_isSharedCheck_947_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_stopPos_939_);
lean_inc(v_startPos_938_);
lean_inc(v_str_937_);
lean_dec(v_x_935_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_947_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v_e_943_; lean_object* v___x_945_; 
v_e_943_ = l_Substring_Raw_takeRightWhileAux(v_str_937_, v_startPos_938_, v_x_936_, v_stopPos_939_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 2, v_e_943_);
v___x_945_ = v___x_941_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_str_937_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_startPos_938_);
lean_ctor_set(v_reuseFailAlloc_946_, 2, v_e_943_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_trimLeft(lean_object* v_s_949_){
_start:
{
lean_object* v_str_950_; lean_object* v_startPos_951_; lean_object* v_stopPos_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_961_; 
v_str_950_ = lean_ctor_get(v_s_949_, 0);
v_startPos_951_ = lean_ctor_get(v_s_949_, 1);
v_stopPos_952_ = lean_ctor_get(v_s_949_, 2);
v_isSharedCheck_961_ = !lean_is_exclusive(v_s_949_);
if (v_isSharedCheck_961_ == 0)
{
v___x_954_ = v_s_949_;
v_isShared_955_ = v_isSharedCheck_961_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_stopPos_952_);
lean_inc(v_startPos_951_);
lean_inc(v_str_950_);
lean_dec(v_s_949_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_961_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_956_; lean_object* v_b_957_; lean_object* v___x_959_; 
v___x_956_ = ((lean_object*)(l_Substring_Raw_trimLeft___closed__0));
v_b_957_ = l_Substring_Raw_takeWhileAux(v_str_950_, v_stopPos_952_, v___x_956_, v_startPos_951_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 1, v_b_957_);
v___x_959_ = v___x_954_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_str_950_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v_b_957_);
lean_ctor_set(v_reuseFailAlloc_960_, 2, v_stopPos_952_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_trimRight(lean_object* v_s_962_){
_start:
{
lean_object* v_str_963_; lean_object* v_startPos_964_; lean_object* v_stopPos_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_974_; 
v_str_963_ = lean_ctor_get(v_s_962_, 0);
v_startPos_964_ = lean_ctor_get(v_s_962_, 1);
v_stopPos_965_ = lean_ctor_get(v_s_962_, 2);
v_isSharedCheck_974_ = !lean_is_exclusive(v_s_962_);
if (v_isSharedCheck_974_ == 0)
{
v___x_967_ = v_s_962_;
v_isShared_968_ = v_isSharedCheck_974_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_stopPos_965_);
lean_inc(v_startPos_964_);
lean_inc(v_str_963_);
lean_dec(v_s_962_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_974_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_969_; lean_object* v_e_970_; lean_object* v___x_972_; 
v___x_969_ = ((lean_object*)(l_Substring_Raw_trimLeft___closed__0));
v_e_970_ = l_Substring_Raw_takeRightWhileAux(v_str_963_, v_startPos_964_, v___x_969_, v_stopPos_965_);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 2, v_e_970_);
v___x_972_ = v___x_967_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_str_963_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v_startPos_964_);
lean_ctor_set(v_reuseFailAlloc_973_, 2, v_e_970_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_trim(lean_object* v_x_975_){
_start:
{
lean_object* v_str_976_; lean_object* v_startPos_977_; lean_object* v_stopPos_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_988_; 
v_str_976_ = lean_ctor_get(v_x_975_, 0);
v_startPos_977_ = lean_ctor_get(v_x_975_, 1);
v_stopPos_978_ = lean_ctor_get(v_x_975_, 2);
v_isSharedCheck_988_ = !lean_is_exclusive(v_x_975_);
if (v_isSharedCheck_988_ == 0)
{
v___x_980_ = v_x_975_;
v_isShared_981_ = v_isSharedCheck_988_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_stopPos_978_);
lean_inc(v_startPos_977_);
lean_inc(v_str_976_);
lean_dec(v_x_975_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_988_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_982_; lean_object* v_b_983_; lean_object* v_e_984_; lean_object* v___x_986_; 
v___x_982_ = ((lean_object*)(l_Substring_Raw_trimLeft___closed__0));
v_b_983_ = l_Substring_Raw_takeWhileAux(v_str_976_, v_stopPos_978_, v___x_982_, v_startPos_977_);
v_e_984_ = l_Substring_Raw_takeRightWhileAux(v_str_976_, v_b_983_, v___x_982_, v_stopPos_978_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 2, v_e_984_);
lean_ctor_set(v___x_980_, 1, v_b_983_);
v___x_986_ = v___x_980_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_str_976_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v_b_983_);
lean_ctor_set(v_reuseFailAlloc_987_, 2, v_e_984_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___lam__0(lean_object* v___y_989_, uint8_t v___x_990_, uint8_t v___x_991_, lean_object* v_it_992_, lean_object* v_acc_993_, lean_object* v_hP_994_, lean_object* v_recur_995_){
_start:
{
lean_object* v_str_996_; lean_object* v_startInclusive_997_; lean_object* v_endExclusive_998_; lean_object* v___x_999_; uint8_t v_decide_1000_; 
v_str_996_ = lean_ctor_get(v___y_989_, 0);
v_startInclusive_997_ = lean_ctor_get(v___y_989_, 1);
v_endExclusive_998_ = lean_ctor_get(v___y_989_, 2);
v___x_999_ = lean_nat_sub(v_endExclusive_998_, v_startInclusive_997_);
v_decide_1000_ = lean_nat_dec_eq(v_it_992_, v___x_999_);
lean_dec(v___x_999_);
if (v_decide_1000_ == 0)
{
lean_object* v_snd_1001_; lean_object* v_snd_1002_; lean_object* v_fst_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1063_; 
v_snd_1001_ = lean_ctor_get(v_acc_993_, 1);
lean_inc(v_snd_1001_);
v_snd_1002_ = lean_ctor_get(v_snd_1001_, 1);
lean_inc(v_snd_1002_);
v_fst_1003_ = lean_ctor_get(v_acc_993_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v_acc_993_);
if (v_isSharedCheck_1063_ == 0)
{
lean_object* v_unused_1064_; 
v_unused_1064_ = lean_ctor_get(v_acc_993_, 1);
lean_dec(v_unused_1064_);
v___x_1005_ = v_acc_993_;
v_isShared_1006_ = v_isSharedCheck_1063_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_fst_1003_);
lean_dec(v_acc_993_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1063_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v_fst_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1061_; 
v_fst_1007_ = lean_ctor_get(v_snd_1001_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_snd_1001_);
if (v_isSharedCheck_1061_ == 0)
{
lean_object* v_unused_1062_; 
v_unused_1062_ = lean_ctor_get(v_snd_1001_, 1);
lean_dec(v_unused_1062_);
v___x_1009_ = v_snd_1001_;
v_isShared_1010_ = v_isSharedCheck_1061_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_fst_1007_);
lean_dec(v_snd_1001_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1061_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v_snd_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1059_; 
v_snd_1011_ = lean_ctor_get(v_snd_1002_, 1);
v_isSharedCheck_1059_ = !lean_is_exclusive(v_snd_1002_);
if (v_isSharedCheck_1059_ == 0)
{
lean_object* v_unused_1060_; 
v_unused_1060_ = lean_ctor_get(v_snd_1002_, 0);
lean_dec(v_unused_1060_);
v___x_1013_ = v_snd_1002_;
v_isShared_1014_ = v_isSharedCheck_1059_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_snd_1011_);
lean_dec(v_snd_1002_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1059_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1015_; uint32_t v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; uint8_t v___y_1020_; uint8_t v___y_1021_; uint8_t v___y_1039_; uint8_t v___y_1040_; uint8_t v___y_1045_; uint8_t v___y_1046_; uint8_t v___y_1051_; uint32_t v___x_1055_; uint8_t v___x_1056_; 
v___x_1015_ = lean_nat_add(v_startInclusive_997_, v_it_992_);
v___x_1016_ = lean_string_utf8_get_fast(v_str_996_, v___x_1015_);
v___x_1017_ = lean_string_utf8_next_fast(v_str_996_, v___x_1015_);
lean_dec(v___x_1015_);
v___x_1018_ = lean_nat_sub(v___x_1017_, v_startInclusive_997_);
v___x_1055_ = 48;
v___x_1056_ = lean_uint32_dec_le(v___x_1055_, v___x_1016_);
if (v___x_1056_ == 0)
{
v___y_1051_ = v___x_1056_;
goto v___jp_1050_;
}
else
{
uint32_t v___x_1057_; uint8_t v___x_1058_; 
v___x_1057_ = 57;
v___x_1058_ = lean_uint32_dec_le(v___x_1016_, v___x_1057_);
v___y_1051_ = v___x_1058_;
goto v___jp_1050_;
}
v___jp_1019_:
{
uint32_t v___x_1022_; uint8_t v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1027_; 
v___x_1022_ = 95;
v___x_1023_ = lean_uint32_dec_eq(v___x_1016_, v___x_1022_);
v___x_1024_ = lean_box(v___y_1020_);
v___x_1025_ = lean_box(v___y_1021_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 1, v___x_1025_);
lean_ctor_set(v___x_1013_, 0, v___x_1024_);
v___x_1027_ = v___x_1013_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1024_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v___x_1025_);
v___x_1027_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1028_ = lean_box(v___x_1023_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 1, v___x_1027_);
lean_ctor_set(v___x_1009_, 0, v___x_1028_);
v___x_1030_ = v___x_1009_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1028_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v___x_1027_);
v___x_1030_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1031_; lean_object* v___x_1033_; 
v___x_1031_ = lean_box(v___x_990_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 1, v___x_1030_);
lean_ctor_set(v___x_1005_, 0, v___x_1031_);
v___x_1033_ = v___x_1005_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1031_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v___x_1030_);
v___x_1033_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
lean_object* v___x_1034_; 
v___x_1034_ = lean_apply_4(v_recur_995_, v___x_1018_, v___x_1033_, lean_box(0), lean_box(0));
return v___x_1034_;
}
}
}
}
v___jp_1038_:
{
uint8_t v___x_1041_; 
v___x_1041_ = lean_unbox(v_fst_1007_);
lean_dec(v_fst_1007_);
if (v___x_1041_ == 0)
{
v___y_1020_ = v___y_1039_;
v___y_1021_ = v___y_1040_;
goto v___jp_1019_;
}
else
{
uint32_t v___x_1042_; uint8_t v___x_1043_; 
v___x_1042_ = 95;
v___x_1043_ = lean_uint32_dec_eq(v___x_1016_, v___x_1042_);
if (v___x_1043_ == 0)
{
v___y_1020_ = v___y_1039_;
v___y_1021_ = v___y_1040_;
goto v___jp_1019_;
}
else
{
v___y_1020_ = v___y_1039_;
v___y_1021_ = v___x_990_;
goto v___jp_1019_;
}
}
}
v___jp_1044_:
{
uint8_t v___x_1047_; 
v___x_1047_ = lean_unbox(v_fst_1003_);
lean_dec(v_fst_1003_);
if (v___x_1047_ == 0)
{
v___y_1039_ = v___y_1045_;
v___y_1040_ = v___y_1046_;
goto v___jp_1038_;
}
else
{
uint32_t v___x_1048_; uint8_t v___x_1049_; 
v___x_1048_ = 95;
v___x_1049_ = lean_uint32_dec_eq(v___x_1016_, v___x_1048_);
if (v___x_1049_ == 0)
{
v___y_1039_ = v___y_1045_;
v___y_1040_ = v___y_1046_;
goto v___jp_1038_;
}
else
{
lean_dec(v_fst_1007_);
v___y_1020_ = v___y_1045_;
v___y_1021_ = v___x_990_;
goto v___jp_1019_;
}
}
}
v___jp_1050_:
{
uint8_t v___x_1052_; 
v___x_1052_ = lean_unbox(v_snd_1011_);
lean_dec(v_snd_1011_);
if (v___x_1052_ == 0)
{
lean_dec(v_fst_1007_);
lean_dec(v_fst_1003_);
v___y_1020_ = v___y_1051_;
v___y_1021_ = v___x_990_;
goto v___jp_1019_;
}
else
{
if (v___y_1051_ == 0)
{
uint32_t v___x_1053_; uint8_t v___x_1054_; 
v___x_1053_ = 95;
v___x_1054_ = lean_uint32_dec_eq(v___x_1016_, v___x_1053_);
if (v___x_1054_ == 0)
{
lean_dec(v_fst_1007_);
lean_dec(v_fst_1003_);
v___y_1020_ = v___y_1051_;
v___y_1021_ = v___x_990_;
goto v___jp_1019_;
}
else
{
v___y_1045_ = v___y_1051_;
v___y_1046_ = v___x_1054_;
goto v___jp_1044_;
}
}
else
{
v___y_1045_ = v___y_1051_;
v___y_1046_ = v___x_991_;
goto v___jp_1044_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_recur_995_);
return v_acc_993_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___lam__0___boxed(lean_object* v___y_1065_, lean_object* v___x_1066_, lean_object* v___x_1067_, lean_object* v_it_1068_, lean_object* v_acc_1069_, lean_object* v_hP_1070_, lean_object* v_recur_1071_){
_start:
{
uint8_t v___x_790__boxed_1072_; uint8_t v___x_791__boxed_1073_; lean_object* v_res_1074_; 
v___x_790__boxed_1072_ = lean_unbox(v___x_1066_);
v___x_791__boxed_1073_ = lean_unbox(v___x_1067_);
v_res_1074_ = l_Substring_Raw_isNat___lam__0(v___y_1065_, v___x_790__boxed_1072_, v___x_791__boxed_1073_, v_it_1068_, v_acc_1069_, v_hP_1070_, v_recur_1071_);
lean_dec(v_it_1068_);
lean_dec_ref(v___y_1065_);
return v_res_1074_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_isNat(lean_object* v_s_1075_){
_start:
{
lean_object* v_str_1076_; lean_object* v_startPos_1077_; lean_object* v_stopPos_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1116_; 
v_str_1076_ = lean_ctor_get(v_s_1075_, 0);
v_startPos_1077_ = lean_ctor_get(v_s_1075_, 1);
v_stopPos_1078_ = lean_ctor_get(v_s_1075_, 2);
v_isSharedCheck_1116_ = !lean_is_exclusive(v_s_1075_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1080_ = v_s_1075_;
v_isShared_1081_ = v_isSharedCheck_1116_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_stopPos_1078_);
lean_inc(v_startPos_1077_);
lean_inc(v_str_1076_);
lean_dec(v_s_1075_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1116_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; uint8_t v___x_1084_; 
v___x_1082_ = lean_nat_sub(v_stopPos_1078_, v_startPos_1077_);
v___x_1083_ = lean_unsigned_to_nat(0u);
v___x_1084_ = lean_nat_dec_eq(v___x_1082_, v___x_1083_);
lean_dec(v___x_1082_);
if (v___x_1084_ == 0)
{
uint8_t v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___y_1094_; lean_object* v___x_1105_; uint8_t v___x_1109_; 
v___x_1085_ = 1;
v___x_1086_ = lean_box(v___x_1084_);
v___x_1087_ = lean_box(v___x_1085_);
v___x_1088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1086_);
lean_ctor_set(v___x_1088_, 1, v___x_1087_);
v___x_1089_ = lean_box(v___x_1084_);
v___x_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
lean_ctor_set(v___x_1090_, 1, v___x_1088_);
v___x_1091_ = lean_box(v___x_1085_);
v___x_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1091_);
lean_ctor_set(v___x_1092_, 1, v___x_1090_);
v___x_1105_ = l_String_instInhabitedSlice;
v___x_1109_ = lean_string_is_valid_pos(v_str_1076_, v_startPos_1077_);
if (v___x_1109_ == 0)
{
lean_del_object(v___x_1080_);
lean_dec(v_stopPos_1078_);
lean_dec(v_startPos_1077_);
lean_dec_ref(v_str_1076_);
goto v___jp_1106_;
}
else
{
uint8_t v___x_1110_; 
v___x_1110_ = lean_string_is_valid_pos(v_str_1076_, v_stopPos_1078_);
if (v___x_1110_ == 0)
{
lean_del_object(v___x_1080_);
lean_dec(v_stopPos_1078_);
lean_dec(v_startPos_1077_);
lean_dec_ref(v_str_1076_);
goto v___jp_1106_;
}
else
{
uint8_t v___x_1111_; 
v___x_1111_ = lean_nat_dec_le(v_startPos_1077_, v_stopPos_1078_);
if (v___x_1111_ == 0)
{
lean_del_object(v___x_1080_);
lean_dec(v_stopPos_1078_);
lean_dec(v_startPos_1077_);
lean_dec_ref(v_str_1076_);
goto v___jp_1106_;
}
else
{
lean_object* v___x_1113_; 
if (v_isShared_1081_ == 0)
{
v___x_1113_ = v___x_1080_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_str_1076_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_startPos_1077_);
lean_ctor_set(v_reuseFailAlloc_1114_, 2, v_stopPos_1078_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
v___y_1094_ = v___x_1113_;
goto v___jp_1093_;
}
}
}
}
v___jp_1093_:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___f_1097_; lean_object* v___x_1098_; lean_object* v_snd_1099_; lean_object* v_snd_1100_; lean_object* v_snd_1101_; uint8_t v___x_1102_; 
v___x_1095_ = lean_box(v___x_1084_);
v___x_1096_ = lean_box(v___x_1085_);
v___f_1097_ = lean_alloc_closure((void*)(l_Substring_Raw_isNat___lam__0___boxed), 7, 3);
lean_closure_set(v___f_1097_, 0, v___y_1094_);
lean_closure_set(v___f_1097_, 1, v___x_1095_);
lean_closure_set(v___f_1097_, 2, v___x_1096_);
v___x_1098_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1097_, v___x_1083_, v___x_1092_, lean_box(0));
v_snd_1099_ = lean_ctor_get(v___x_1098_, 1);
lean_inc(v_snd_1099_);
lean_dec(v___x_1098_);
v_snd_1100_ = lean_ctor_get(v_snd_1099_, 1);
lean_inc(v_snd_1100_);
lean_dec(v_snd_1099_);
v_snd_1101_ = lean_ctor_get(v_snd_1100_, 1);
v___x_1102_ = lean_unbox(v_snd_1101_);
if (v___x_1102_ == 0)
{
lean_dec(v_snd_1100_);
return v___x_1084_;
}
else
{
lean_object* v_fst_1103_; uint8_t v___x_1104_; 
v_fst_1103_ = lean_ctor_get(v_snd_1100_, 0);
lean_inc(v_fst_1103_);
lean_dec(v_snd_1100_);
v___x_1104_ = lean_unbox(v_fst_1103_);
lean_dec(v_fst_1103_);
return v___x_1104_;
}
}
v___jp_1106_:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_1108_ = l_panic___redArg(v___x_1105_, v___x_1107_);
v___y_1094_ = v___x_1108_;
goto v___jp_1093_;
}
}
else
{
uint8_t v___x_1115_; 
lean_del_object(v___x_1080_);
lean_dec(v_stopPos_1078_);
lean_dec(v_startPos_1077_);
lean_dec_ref(v_str_1076_);
v___x_1115_ = 0;
return v___x_1115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___boxed(lean_object* v_s_1117_){
_start:
{
uint8_t v_res_1118_; lean_object* v_r_1119_; 
v_res_1118_ = l_Substring_Raw_isNat(v_s_1117_);
v_r_1119_ = lean_box(v_res_1118_);
return v_r_1119_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(lean_object* v___y_1120_, lean_object* v_a_1121_, lean_object* v_b_1122_){
_start:
{
lean_object* v_str_1123_; lean_object* v_startInclusive_1124_; lean_object* v_endExclusive_1125_; lean_object* v___x_1126_; uint8_t v_decide_1127_; 
v_str_1123_ = lean_ctor_get(v___y_1120_, 0);
v_startInclusive_1124_ = lean_ctor_get(v___y_1120_, 1);
v_endExclusive_1125_ = lean_ctor_get(v___y_1120_, 2);
v___x_1126_ = lean_nat_sub(v_endExclusive_1125_, v_startInclusive_1124_);
v_decide_1127_ = lean_nat_dec_eq(v_a_1121_, v___x_1126_);
lean_dec(v___x_1126_);
if (v_decide_1127_ == 0)
{
lean_object* v___x_1128_; uint32_t v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; uint32_t v___x_1132_; uint8_t v___x_1133_; 
v___x_1128_ = lean_nat_add(v_startInclusive_1124_, v_a_1121_);
lean_dec(v_a_1121_);
v___x_1129_ = lean_string_utf8_get_fast(v_str_1123_, v___x_1128_);
v___x_1130_ = lean_string_utf8_next_fast(v_str_1123_, v___x_1128_);
lean_dec(v___x_1128_);
v___x_1131_ = lean_nat_sub(v___x_1130_, v_startInclusive_1124_);
v___x_1132_ = 95;
v___x_1133_ = lean_uint32_dec_eq(v___x_1129_, v___x_1132_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1134_ = lean_unsigned_to_nat(10u);
v___x_1135_ = lean_nat_mul(v_b_1122_, v___x_1134_);
lean_dec(v_b_1122_);
v___x_1136_ = lean_uint32_to_nat(v___x_1129_);
v___x_1137_ = lean_unsigned_to_nat(48u);
v___x_1138_ = lean_nat_sub(v___x_1136_, v___x_1137_);
lean_dec(v___x_1136_);
v___x_1139_ = lean_nat_add(v___x_1135_, v___x_1138_);
lean_dec(v___x_1138_);
lean_dec(v___x_1135_);
v_a_1121_ = v___x_1131_;
v_b_1122_ = v___x_1139_;
goto _start;
}
else
{
v_a_1121_ = v___x_1131_;
goto _start;
}
}
else
{
lean_dec(v_a_1121_);
return v_b_1122_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg___boxed(lean_object* v___y_1142_, lean_object* v_a_1143_, lean_object* v_b_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(v___y_1142_, v_a_1143_, v_b_1144_);
lean_dec_ref(v___y_1142_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(lean_object* v___x_1146_, lean_object* v___y_1147_, lean_object* v_a_1148_, lean_object* v_b_1149_){
_start:
{
lean_object* v_str_1150_; lean_object* v_startInclusive_1151_; lean_object* v_endExclusive_1152_; lean_object* v___x_1153_; uint8_t v_decide_1154_; 
v_str_1150_ = lean_ctor_get(v___y_1147_, 0);
v_startInclusive_1151_ = lean_ctor_get(v___y_1147_, 1);
v_endExclusive_1152_ = lean_ctor_get(v___y_1147_, 2);
v___x_1153_ = lean_nat_sub(v_endExclusive_1152_, v_startInclusive_1151_);
v_decide_1154_ = lean_nat_dec_eq(v_a_1148_, v___x_1153_);
lean_dec(v___x_1153_);
if (v_decide_1154_ == 0)
{
lean_object* v_snd_1155_; lean_object* v_snd_1156_; lean_object* v_fst_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1220_; 
v_snd_1155_ = lean_ctor_get(v_b_1149_, 1);
lean_inc(v_snd_1155_);
v_snd_1156_ = lean_ctor_get(v_snd_1155_, 1);
lean_inc(v_snd_1156_);
v_fst_1157_ = lean_ctor_get(v_b_1149_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_b_1149_);
if (v_isSharedCheck_1220_ == 0)
{
lean_object* v_unused_1221_; 
v_unused_1221_ = lean_ctor_get(v_b_1149_, 1);
lean_dec(v_unused_1221_);
v___x_1159_ = v_b_1149_;
v_isShared_1160_ = v_isSharedCheck_1220_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_fst_1157_);
lean_dec(v_b_1149_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1220_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v_fst_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1218_; 
v_fst_1161_ = lean_ctor_get(v_snd_1155_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_snd_1155_);
if (v_isSharedCheck_1218_ == 0)
{
lean_object* v_unused_1219_; 
v_unused_1219_ = lean_ctor_get(v_snd_1155_, 1);
lean_dec(v_unused_1219_);
v___x_1163_ = v_snd_1155_;
v_isShared_1164_ = v_isSharedCheck_1218_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_fst_1161_);
lean_dec(v_snd_1155_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1218_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v_snd_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1216_; 
v_snd_1165_ = lean_ctor_get(v_snd_1156_, 1);
v_isSharedCheck_1216_ = !lean_is_exclusive(v_snd_1156_);
if (v_isSharedCheck_1216_ == 0)
{
lean_object* v_unused_1217_; 
v_unused_1217_ = lean_ctor_get(v_snd_1156_, 0);
lean_dec(v_unused_1217_);
v___x_1167_ = v_snd_1156_;
v_isShared_1168_ = v_isSharedCheck_1216_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_snd_1165_);
lean_dec(v_snd_1156_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1216_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1169_; uint8_t v___x_1170_; uint8_t v___x_1171_; lean_object* v___x_1172_; uint32_t v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; uint8_t v___y_1177_; uint8_t v___y_1178_; uint8_t v___y_1196_; uint8_t v___y_1197_; uint8_t v___y_1202_; uint8_t v___y_1203_; uint8_t v___y_1208_; uint32_t v___x_1212_; uint8_t v___x_1213_; 
v___x_1169_ = lean_unsigned_to_nat(0u);
v___x_1170_ = lean_nat_dec_eq(v___x_1146_, v___x_1169_);
v___x_1171_ = 1;
v___x_1172_ = lean_nat_add(v_startInclusive_1151_, v_a_1148_);
lean_dec(v_a_1148_);
v___x_1173_ = lean_string_utf8_get_fast(v_str_1150_, v___x_1172_);
v___x_1174_ = lean_string_utf8_next_fast(v_str_1150_, v___x_1172_);
lean_dec(v___x_1172_);
v___x_1175_ = lean_nat_sub(v___x_1174_, v_startInclusive_1151_);
v___x_1212_ = 48;
v___x_1213_ = lean_uint32_dec_le(v___x_1212_, v___x_1173_);
if (v___x_1213_ == 0)
{
v___y_1208_ = v___x_1213_;
goto v___jp_1207_;
}
else
{
uint32_t v___x_1214_; uint8_t v___x_1215_; 
v___x_1214_ = 57;
v___x_1215_ = lean_uint32_dec_le(v___x_1173_, v___x_1214_);
v___y_1208_ = v___x_1215_;
goto v___jp_1207_;
}
v___jp_1176_:
{
uint32_t v___x_1179_; uint8_t v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1184_; 
v___x_1179_ = 95;
v___x_1180_ = lean_uint32_dec_eq(v___x_1173_, v___x_1179_);
v___x_1181_ = lean_box(v___y_1177_);
v___x_1182_ = lean_box(v___y_1178_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 1, v___x_1182_);
lean_ctor_set(v___x_1167_, 0, v___x_1181_);
v___x_1184_ = v___x_1167_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1181_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v___x_1182_);
v___x_1184_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
lean_object* v___x_1185_; lean_object* v___x_1187_; 
v___x_1185_ = lean_box(v___x_1180_);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 1, v___x_1184_);
lean_ctor_set(v___x_1163_, 0, v___x_1185_);
v___x_1187_ = v___x_1163_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1185_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v___x_1184_);
v___x_1187_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
lean_object* v___x_1188_; lean_object* v___x_1190_; 
v___x_1188_ = lean_box(v___x_1170_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 1, v___x_1187_);
lean_ctor_set(v___x_1159_, 0, v___x_1188_);
v___x_1190_ = v___x_1159_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1188_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v___x_1187_);
v___x_1190_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
v_a_1148_ = v___x_1175_;
v_b_1149_ = v___x_1190_;
goto _start;
}
}
}
}
v___jp_1195_:
{
uint8_t v___x_1198_; 
v___x_1198_ = lean_unbox(v_fst_1161_);
lean_dec(v_fst_1161_);
if (v___x_1198_ == 0)
{
v___y_1177_ = v___y_1196_;
v___y_1178_ = v___y_1197_;
goto v___jp_1176_;
}
else
{
uint32_t v___x_1199_; uint8_t v___x_1200_; 
v___x_1199_ = 95;
v___x_1200_ = lean_uint32_dec_eq(v___x_1173_, v___x_1199_);
if (v___x_1200_ == 0)
{
v___y_1177_ = v___y_1196_;
v___y_1178_ = v___y_1197_;
goto v___jp_1176_;
}
else
{
v___y_1177_ = v___y_1196_;
v___y_1178_ = v___x_1170_;
goto v___jp_1176_;
}
}
}
v___jp_1201_:
{
uint8_t v___x_1204_; 
v___x_1204_ = lean_unbox(v_fst_1157_);
lean_dec(v_fst_1157_);
if (v___x_1204_ == 0)
{
v___y_1196_ = v___y_1202_;
v___y_1197_ = v___y_1203_;
goto v___jp_1195_;
}
else
{
uint32_t v___x_1205_; uint8_t v___x_1206_; 
v___x_1205_ = 95;
v___x_1206_ = lean_uint32_dec_eq(v___x_1173_, v___x_1205_);
if (v___x_1206_ == 0)
{
v___y_1196_ = v___y_1202_;
v___y_1197_ = v___y_1203_;
goto v___jp_1195_;
}
else
{
lean_dec(v_fst_1161_);
v___y_1177_ = v___y_1202_;
v___y_1178_ = v___x_1170_;
goto v___jp_1176_;
}
}
}
v___jp_1207_:
{
uint8_t v___x_1209_; 
v___x_1209_ = lean_unbox(v_snd_1165_);
lean_dec(v_snd_1165_);
if (v___x_1209_ == 0)
{
lean_dec(v_fst_1161_);
lean_dec(v_fst_1157_);
v___y_1177_ = v___y_1208_;
v___y_1178_ = v___x_1170_;
goto v___jp_1176_;
}
else
{
if (v___y_1208_ == 0)
{
uint32_t v___x_1210_; uint8_t v___x_1211_; 
v___x_1210_ = 95;
v___x_1211_ = lean_uint32_dec_eq(v___x_1173_, v___x_1210_);
if (v___x_1211_ == 0)
{
lean_dec(v_fst_1161_);
lean_dec(v_fst_1157_);
v___y_1177_ = v___y_1208_;
v___y_1178_ = v___x_1170_;
goto v___jp_1176_;
}
else
{
v___y_1202_ = v___y_1208_;
v___y_1203_ = v___x_1211_;
goto v___jp_1201_;
}
}
else
{
v___y_1202_ = v___y_1208_;
v___y_1203_ = v___x_1171_;
goto v___jp_1201_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1148_);
return v_b_1149_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg___boxed(lean_object* v___x_1222_, lean_object* v___y_1223_, lean_object* v_a_1224_, lean_object* v_b_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(v___x_1222_, v___y_1223_, v_a_1224_, v_b_1225_);
lean_dec_ref(v___y_1223_);
lean_dec(v___x_1222_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toNat_x3f(lean_object* v_s_1227_){
_start:
{
lean_object* v_str_1228_; lean_object* v_startPos_1229_; lean_object* v_stopPos_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1277_; 
v_str_1228_ = lean_ctor_get(v_s_1227_, 0);
v_startPos_1229_ = lean_ctor_get(v_s_1227_, 1);
v_stopPos_1230_ = lean_ctor_get(v_s_1227_, 2);
v_isSharedCheck_1277_ = !lean_is_exclusive(v_s_1227_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1232_ = v_s_1227_;
v_isShared_1233_ = v_isSharedCheck_1277_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_stopPos_1230_);
lean_inc(v_startPos_1229_);
lean_inc(v_str_1228_);
lean_dec(v_s_1227_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1277_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___y_1237_; uint8_t v___x_1243_; 
v___x_1234_ = lean_nat_sub(v_stopPos_1230_, v_startPos_1229_);
v___x_1235_ = lean_unsigned_to_nat(0u);
v___x_1243_ = lean_nat_dec_eq(v___x_1234_, v___x_1235_);
if (v___x_1243_ == 0)
{
uint8_t v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___y_1253_; uint8_t v___x_1272_; 
v___x_1244_ = 1;
v___x_1245_ = lean_box(v___x_1243_);
v___x_1246_ = lean_box(v___x_1244_);
v___x_1247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1245_);
lean_ctor_set(v___x_1247_, 1, v___x_1246_);
v___x_1248_ = lean_box(v___x_1243_);
v___x_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
lean_ctor_set(v___x_1249_, 1, v___x_1247_);
v___x_1250_ = lean_box(v___x_1244_);
v___x_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
lean_ctor_set(v___x_1251_, 1, v___x_1249_);
v___x_1272_ = lean_string_is_valid_pos(v_str_1228_, v_startPos_1229_);
if (v___x_1272_ == 0)
{
goto v___jp_1269_;
}
else
{
uint8_t v___x_1273_; 
v___x_1273_ = lean_string_is_valid_pos(v_str_1228_, v_stopPos_1230_);
if (v___x_1273_ == 0)
{
goto v___jp_1269_;
}
else
{
uint8_t v___x_1274_; 
v___x_1274_ = lean_nat_dec_le(v_startPos_1229_, v_stopPos_1230_);
if (v___x_1274_ == 0)
{
goto v___jp_1269_;
}
else
{
lean_object* v___x_1275_; 
lean_inc(v_stopPos_1230_);
lean_inc(v_startPos_1229_);
lean_inc_ref(v_str_1228_);
v___x_1275_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1275_, 0, v_str_1228_);
lean_ctor_set(v___x_1275_, 1, v_startPos_1229_);
lean_ctor_set(v___x_1275_, 2, v_stopPos_1230_);
v___y_1253_ = v___x_1275_;
goto v___jp_1252_;
}
}
}
v___jp_1252_:
{
lean_object* v___x_1254_; lean_object* v_snd_1255_; lean_object* v_snd_1256_; lean_object* v_snd_1257_; uint8_t v___x_1258_; 
v___x_1254_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(v___x_1234_, v___y_1253_, v___x_1235_, v___x_1251_);
lean_dec_ref(v___y_1253_);
lean_dec(v___x_1234_);
v_snd_1255_ = lean_ctor_get(v___x_1254_, 1);
lean_inc(v_snd_1255_);
lean_dec_ref(v___x_1254_);
v_snd_1256_ = lean_ctor_get(v_snd_1255_, 1);
lean_inc(v_snd_1256_);
lean_dec(v_snd_1255_);
v_snd_1257_ = lean_ctor_get(v_snd_1256_, 1);
v___x_1258_ = lean_unbox(v_snd_1257_);
if (v___x_1258_ == 0)
{
lean_object* v___x_1259_; 
lean_dec(v_snd_1256_);
lean_del_object(v___x_1232_);
lean_dec(v_stopPos_1230_);
lean_dec(v_startPos_1229_);
lean_dec_ref(v_str_1228_);
v___x_1259_ = lean_box(0);
return v___x_1259_;
}
else
{
lean_object* v_fst_1260_; uint8_t v___x_1261_; 
v_fst_1260_ = lean_ctor_get(v_snd_1256_, 0);
lean_inc(v_fst_1260_);
lean_dec(v_snd_1256_);
v___x_1261_ = lean_unbox(v_fst_1260_);
lean_dec(v_fst_1260_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; 
lean_del_object(v___x_1232_);
lean_dec(v_stopPos_1230_);
lean_dec(v_startPos_1229_);
lean_dec_ref(v_str_1228_);
v___x_1262_ = lean_box(0);
return v___x_1262_;
}
else
{
uint8_t v___x_1263_; 
v___x_1263_ = lean_string_is_valid_pos(v_str_1228_, v_startPos_1229_);
if (v___x_1263_ == 0)
{
lean_del_object(v___x_1232_);
lean_dec(v_stopPos_1230_);
lean_dec(v_startPos_1229_);
lean_dec_ref(v_str_1228_);
goto v___jp_1240_;
}
else
{
uint8_t v___x_1264_; 
v___x_1264_ = lean_string_is_valid_pos(v_str_1228_, v_stopPos_1230_);
if (v___x_1264_ == 0)
{
lean_del_object(v___x_1232_);
lean_dec(v_stopPos_1230_);
lean_dec(v_startPos_1229_);
lean_dec_ref(v_str_1228_);
goto v___jp_1240_;
}
else
{
uint8_t v___x_1265_; 
v___x_1265_ = lean_nat_dec_le(v_startPos_1229_, v_stopPos_1230_);
if (v___x_1265_ == 0)
{
lean_del_object(v___x_1232_);
lean_dec(v_stopPos_1230_);
lean_dec(v_startPos_1229_);
lean_dec_ref(v_str_1228_);
goto v___jp_1240_;
}
else
{
lean_object* v___x_1267_; 
if (v_isShared_1233_ == 0)
{
v___x_1267_ = v___x_1232_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_str_1228_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v_startPos_1229_);
lean_ctor_set(v_reuseFailAlloc_1268_, 2, v_stopPos_1230_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
v___y_1237_ = v___x_1267_;
goto v___jp_1236_;
}
}
}
}
}
}
}
v___jp_1269_:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1270_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_1271_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_1270_);
v___y_1253_ = v___x_1271_;
goto v___jp_1252_;
}
}
else
{
lean_object* v___x_1276_; 
lean_dec(v___x_1234_);
lean_del_object(v___x_1232_);
lean_dec(v_stopPos_1230_);
lean_dec(v_startPos_1229_);
lean_dec_ref(v_str_1228_);
v___x_1276_ = lean_box(0);
return v___x_1276_;
}
v___jp_1236_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1238_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(v___y_1237_, v___x_1235_, v___x_1235_);
lean_dec_ref(v___y_1237_);
v___x_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1238_);
return v___x_1239_;
}
v___jp_1240_:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_1242_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_1241_);
v___y_1237_ = v___x_1242_;
goto v___jp_1236_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0(lean_object* v___x_1278_, lean_object* v___y_1279_, lean_object* v_inst_1280_, lean_object* v_R_1281_, lean_object* v_a_1282_, lean_object* v_b_1283_, lean_object* v_c_1284_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(v___x_1278_, v___y_1279_, v_a_1282_, v_b_1283_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___boxed(lean_object* v___x_1286_, lean_object* v___y_1287_, lean_object* v_inst_1288_, lean_object* v_R_1289_, lean_object* v_a_1290_, lean_object* v_b_1291_, lean_object* v_c_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0(v___x_1286_, v___y_1287_, v_inst_1288_, v_R_1289_, v_a_1290_, v_b_1291_, v_c_1292_);
lean_dec_ref(v___y_1287_);
lean_dec(v___x_1286_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1(lean_object* v___y_1294_, lean_object* v_inst_1295_, lean_object* v_R_1296_, lean_object* v_a_1297_, lean_object* v_b_1298_, lean_object* v_c_1299_){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(v___y_1294_, v_a_1297_, v_b_1298_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___boxed(lean_object* v___y_1301_, lean_object* v_inst_1302_, lean_object* v_R_1303_, lean_object* v_a_1304_, lean_object* v_b_1305_, lean_object* v_c_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1(v___y_1301_, v_inst_1302_, v_R_1303_, v_a_1304_, v_b_1305_, v_c_1306_);
lean_dec_ref(v___y_1301_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_repair(lean_object* v_x_1308_){
_start:
{
lean_object* v_str_1309_; lean_object* v_startPos_1310_; lean_object* v_stopPos_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1327_; 
v_str_1309_ = lean_ctor_get(v_x_1308_, 0);
v_startPos_1310_ = lean_ctor_get(v_x_1308_, 1);
v_stopPos_1311_ = lean_ctor_get(v_x_1308_, 2);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_x_1308_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1313_ = v_x_1308_;
v_isShared_1314_ = v_isSharedCheck_1327_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_stopPos_1311_);
lean_inc(v_startPos_1310_);
lean_inc(v_str_1309_);
lean_dec(v_x_1308_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1327_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___y_1316_; uint8_t v___x_1325_; 
v___x_1325_ = lean_string_is_valid_pos(v_str_1309_, v_startPos_1310_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1326_; 
lean_dec(v_startPos_1310_);
v___x_1326_ = lean_string_utf8_byte_size(v_str_1309_);
v___y_1316_ = v___x_1326_;
goto v___jp_1315_;
}
else
{
v___y_1316_ = v_startPos_1310_;
goto v___jp_1315_;
}
v___jp_1315_:
{
uint8_t v___x_1317_; 
v___x_1317_ = lean_string_is_valid_pos(v_str_1309_, v_stopPos_1311_);
if (v___x_1317_ == 0)
{
lean_object* v___x_1318_; lean_object* v___x_1320_; 
lean_dec(v_stopPos_1311_);
v___x_1318_ = lean_string_utf8_byte_size(v_str_1309_);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 2, v___x_1318_);
lean_ctor_set(v___x_1313_, 1, v___y_1316_);
v___x_1320_ = v___x_1313_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_str_1309_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v___y_1316_);
lean_ctor_set(v_reuseFailAlloc_1321_, 2, v___x_1318_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
else
{
lean_object* v___x_1323_; 
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 1, v___y_1316_);
v___x_1323_ = v___x_1313_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_str_1309_);
lean_ctor_set(v_reuseFailAlloc_1324_, 1, v___y_1316_);
lean_ctor_set(v_reuseFailAlloc_1324_, 2, v_stopPos_1311_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_beq(lean_object* v_ss1_1328_, lean_object* v_ss2_1329_){
_start:
{
lean_object* v_ss1_1330_; lean_object* v_str_1331_; lean_object* v_startPos_1332_; lean_object* v_stopPos_1333_; lean_object* v_ss2_1334_; lean_object* v_str_1335_; lean_object* v_startPos_1336_; lean_object* v_stopPos_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; uint8_t v___x_1340_; 
v_ss1_1330_ = l_Substring_Raw_repair(v_ss1_1328_);
v_str_1331_ = lean_ctor_get(v_ss1_1330_, 0);
lean_inc_ref(v_str_1331_);
v_startPos_1332_ = lean_ctor_get(v_ss1_1330_, 1);
lean_inc(v_startPos_1332_);
v_stopPos_1333_ = lean_ctor_get(v_ss1_1330_, 2);
lean_inc(v_stopPos_1333_);
lean_dec_ref(v_ss1_1330_);
v_ss2_1334_ = l_Substring_Raw_repair(v_ss2_1329_);
v_str_1335_ = lean_ctor_get(v_ss2_1334_, 0);
lean_inc_ref(v_str_1335_);
v_startPos_1336_ = lean_ctor_get(v_ss2_1334_, 1);
lean_inc(v_startPos_1336_);
v_stopPos_1337_ = lean_ctor_get(v_ss2_1334_, 2);
lean_inc(v_stopPos_1337_);
lean_dec_ref(v_ss2_1334_);
v___x_1338_ = lean_nat_sub(v_stopPos_1333_, v_startPos_1332_);
lean_dec(v_stopPos_1333_);
v___x_1339_ = lean_nat_sub(v_stopPos_1337_, v_startPos_1336_);
lean_dec(v_stopPos_1337_);
v___x_1340_ = lean_nat_dec_eq(v___x_1338_, v___x_1339_);
lean_dec(v___x_1339_);
if (v___x_1340_ == 0)
{
lean_dec(v___x_1338_);
lean_dec(v_startPos_1336_);
lean_dec_ref(v_str_1335_);
lean_dec(v_startPos_1332_);
lean_dec_ref(v_str_1331_);
return v___x_1340_;
}
else
{
uint8_t v___x_1341_; 
v___x_1341_ = l_String_Pos_Raw_substrEq(v_str_1331_, v_startPos_1332_, v_str_1335_, v_startPos_1336_, v___x_1338_);
lean_dec(v___x_1338_);
lean_dec_ref(v_str_1335_);
lean_dec_ref(v_str_1331_);
return v___x_1341_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_beq___boxed(lean_object* v_ss1_1342_, lean_object* v_ss2_1343_){
_start:
{
uint8_t v_res_1344_; lean_object* v_r_1345_; 
v_res_1344_ = l_Substring_Raw_beq(v_ss1_1342_, v_ss2_1343_);
v_r_1345_ = lean_box(v_res_1344_);
return v_r_1345_;
}
}
LEAN_EXPORT uint8_t lean_substring_beq(lean_object* v_ss1_1346_, lean_object* v_ss2_1347_){
_start:
{
uint8_t v___x_1348_; 
v___x_1348_ = l_Substring_Raw_beq(v_ss1_1346_, v_ss2_1347_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_beqImpl___boxed(lean_object* v_ss1_1349_, lean_object* v_ss2_1350_){
_start:
{
uint8_t v_res_1351_; lean_object* v_r_1352_; 
v_res_1351_ = lean_substring_beq(v_ss1_1349_, v_ss2_1350_);
v_r_1352_ = lean_box(v_res_1351_);
return v_r_1352_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_sameAs(lean_object* v_ss1_1355_, lean_object* v_ss2_1356_){
_start:
{
lean_object* v_startPos_1357_; lean_object* v_startPos_1358_; uint8_t v_decide_1359_; 
v_startPos_1357_ = lean_ctor_get(v_ss1_1355_, 1);
v_startPos_1358_ = lean_ctor_get(v_ss2_1356_, 1);
v_decide_1359_ = lean_nat_dec_eq(v_startPos_1357_, v_startPos_1358_);
if (v_decide_1359_ == 0)
{
lean_dec_ref(v_ss2_1356_);
lean_dec_ref(v_ss1_1355_);
return v_decide_1359_;
}
else
{
uint8_t v___x_1360_; 
v___x_1360_ = l_Substring_Raw_beq(v_ss1_1355_, v_ss2_1356_);
return v___x_1360_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_sameAs___boxed(lean_object* v_ss1_1361_, lean_object* v_ss2_1362_){
_start:
{
uint8_t v_res_1363_; lean_object* v_r_1364_; 
v_res_1363_ = l_Substring_Raw_sameAs(v_ss1_1361_, v_ss2_1362_);
v_r_1364_ = lean_box(v_res_1363_);
return v_r_1364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(lean_object* v_s_1365_, lean_object* v_t_1366_, lean_object* v_spos_1367_, lean_object* v_tpos_1368_){
_start:
{
lean_object* v_str_1369_; lean_object* v_stopPos_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; uint8_t v___x_1373_; 
v_str_1369_ = lean_ctor_get(v_s_1365_, 0);
v_stopPos_1370_ = lean_ctor_get(v_s_1365_, 2);
v___x_1371_ = lean_unsigned_to_nat(1u);
v___x_1372_ = lean_nat_add(v_spos_1367_, v___x_1371_);
v___x_1373_ = lean_nat_dec_le(v___x_1372_, v_stopPos_1370_);
lean_dec(v___x_1372_);
if (v___x_1373_ == 0)
{
lean_dec(v_tpos_1368_);
return v_spos_1367_;
}
else
{
lean_object* v_str_1374_; lean_object* v_stopPos_1375_; lean_object* v___x_1376_; uint8_t v___x_1377_; 
v_str_1374_ = lean_ctor_get(v_t_1366_, 0);
v_stopPos_1375_ = lean_ctor_get(v_t_1366_, 2);
v___x_1376_ = lean_nat_add(v_tpos_1368_, v___x_1371_);
v___x_1377_ = lean_nat_dec_le(v___x_1376_, v_stopPos_1375_);
lean_dec(v___x_1376_);
if (v___x_1377_ == 0)
{
lean_dec(v_tpos_1368_);
return v_spos_1367_;
}
else
{
uint32_t v___x_1378_; uint32_t v___x_1379_; uint8_t v___x_1380_; 
v___x_1378_ = lean_string_utf8_get(v_str_1369_, v_spos_1367_);
v___x_1379_ = lean_string_utf8_get(v_str_1374_, v_tpos_1368_);
v___x_1380_ = lean_uint32_dec_eq(v___x_1378_, v___x_1379_);
if (v___x_1380_ == 0)
{
lean_dec(v_tpos_1368_);
return v_spos_1367_;
}
else
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = lean_string_utf8_next(v_str_1369_, v_spos_1367_);
lean_dec(v_spos_1367_);
v___x_1382_ = lean_string_utf8_next(v_str_1374_, v_tpos_1368_);
lean_dec(v_tpos_1368_);
v_spos_1367_ = v___x_1381_;
v_tpos_1368_ = v___x_1382_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop___boxed(lean_object* v_s_1384_, lean_object* v_t_1385_, lean_object* v_spos_1386_, lean_object* v_tpos_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(v_s_1384_, v_t_1385_, v_spos_1386_, v_tpos_1387_);
lean_dec_ref(v_t_1385_);
lean_dec_ref(v_s_1384_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_commonPrefix(lean_object* v_s_1389_, lean_object* v_t_1390_){
_start:
{
lean_object* v_str_1391_; lean_object* v_startPos_1392_; lean_object* v_startPos_1393_; lean_object* v___x_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
v_str_1391_ = lean_ctor_get(v_s_1389_, 0);
lean_inc_ref(v_str_1391_);
v_startPos_1392_ = lean_ctor_get(v_s_1389_, 1);
lean_inc_n(v_startPos_1392_, 2);
v_startPos_1393_ = lean_ctor_get(v_t_1390_, 1);
lean_inc(v_startPos_1393_);
v___x_1394_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(v_s_1389_, v_t_1390_, v_startPos_1392_, v_startPos_1393_);
lean_dec_ref(v_s_1389_);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_t_1390_);
if (v_isSharedCheck_1401_ == 0)
{
lean_object* v_unused_1402_; lean_object* v_unused_1403_; lean_object* v_unused_1404_; 
v_unused_1402_ = lean_ctor_get(v_t_1390_, 2);
lean_dec(v_unused_1402_);
v_unused_1403_ = lean_ctor_get(v_t_1390_, 1);
lean_dec(v_unused_1403_);
v_unused_1404_ = lean_ctor_get(v_t_1390_, 0);
lean_dec(v_unused_1404_);
v___x_1396_ = v_t_1390_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_dec(v_t_1390_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 2, v___x_1394_);
lean_ctor_set(v___x_1396_, 1, v_startPos_1392_);
lean_ctor_set(v___x_1396_, 0, v_str_1391_);
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_str_1391_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v_startPos_1392_);
lean_ctor_set(v_reuseFailAlloc_1400_, 2, v___x_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(lean_object* v_s_1405_, lean_object* v_t_1406_, lean_object* v_spos_1407_, lean_object* v_tpos_1408_){
_start:
{
lean_object* v_str_1409_; lean_object* v_startPos_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; uint8_t v___x_1413_; 
v_str_1409_ = lean_ctor_get(v_s_1405_, 0);
v_startPos_1410_ = lean_ctor_get(v_s_1405_, 1);
v___x_1411_ = lean_unsigned_to_nat(1u);
v___x_1412_ = lean_nat_add(v_startPos_1410_, v___x_1411_);
v___x_1413_ = lean_nat_dec_le(v___x_1412_, v_spos_1407_);
lean_dec(v___x_1412_);
if (v___x_1413_ == 0)
{
lean_dec(v_tpos_1408_);
return v_spos_1407_;
}
else
{
lean_object* v_str_1414_; lean_object* v_startPos_1415_; lean_object* v___x_1416_; uint8_t v___x_1417_; 
v_str_1414_ = lean_ctor_get(v_t_1406_, 0);
v_startPos_1415_ = lean_ctor_get(v_t_1406_, 1);
v___x_1416_ = lean_nat_add(v_startPos_1415_, v___x_1411_);
v___x_1417_ = lean_nat_dec_le(v___x_1416_, v_tpos_1408_);
lean_dec(v___x_1416_);
if (v___x_1417_ == 0)
{
lean_dec(v_tpos_1408_);
return v_spos_1407_;
}
else
{
lean_object* v_spos_x27_1418_; lean_object* v_tpos_x27_1419_; uint32_t v___x_1420_; uint32_t v___x_1421_; uint8_t v___x_1422_; 
v_spos_x27_1418_ = lean_string_utf8_prev(v_str_1409_, v_spos_1407_);
v_tpos_x27_1419_ = lean_string_utf8_prev(v_str_1414_, v_tpos_1408_);
lean_dec(v_tpos_1408_);
v___x_1420_ = lean_string_utf8_get(v_str_1409_, v_spos_x27_1418_);
v___x_1421_ = lean_string_utf8_get(v_str_1414_, v_tpos_x27_1419_);
v___x_1422_ = lean_uint32_dec_eq(v___x_1420_, v___x_1421_);
if (v___x_1422_ == 0)
{
lean_dec(v_tpos_x27_1419_);
lean_dec(v_spos_x27_1418_);
return v_spos_1407_;
}
else
{
lean_dec(v_spos_1407_);
v_spos_1407_ = v_spos_x27_1418_;
v_tpos_1408_ = v_tpos_x27_1419_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop___boxed(lean_object* v_s_1424_, lean_object* v_t_1425_, lean_object* v_spos_1426_, lean_object* v_tpos_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(v_s_1424_, v_t_1425_, v_spos_1426_, v_tpos_1427_);
lean_dec_ref(v_t_1425_);
lean_dec_ref(v_s_1424_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_commonSuffix(lean_object* v_s_1429_, lean_object* v_t_1430_){
_start:
{
lean_object* v_str_1431_; lean_object* v_stopPos_1432_; lean_object* v_stopPos_1433_; lean_object* v___x_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
v_str_1431_ = lean_ctor_get(v_s_1429_, 0);
lean_inc_ref(v_str_1431_);
v_stopPos_1432_ = lean_ctor_get(v_s_1429_, 2);
lean_inc_n(v_stopPos_1432_, 2);
v_stopPos_1433_ = lean_ctor_get(v_t_1430_, 2);
lean_inc(v_stopPos_1433_);
v___x_1434_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(v_s_1429_, v_t_1430_, v_stopPos_1432_, v_stopPos_1433_);
lean_dec_ref(v_s_1429_);
v_isSharedCheck_1441_ = !lean_is_exclusive(v_t_1430_);
if (v_isSharedCheck_1441_ == 0)
{
lean_object* v_unused_1442_; lean_object* v_unused_1443_; lean_object* v_unused_1444_; 
v_unused_1442_ = lean_ctor_get(v_t_1430_, 2);
lean_dec(v_unused_1442_);
v_unused_1443_ = lean_ctor_get(v_t_1430_, 1);
lean_dec(v_unused_1443_);
v_unused_1444_ = lean_ctor_get(v_t_1430_, 0);
lean_dec(v_unused_1444_);
v___x_1436_ = v_t_1430_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_dec(v_t_1430_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 2, v_stopPos_1432_);
lean_ctor_set(v___x_1436_, 1, v___x_1434_);
lean_ctor_set(v___x_1436_, 0, v_str_1431_);
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_str_1431_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v___x_1434_);
lean_ctor_set(v_reuseFailAlloc_1440_, 2, v_stopPos_1432_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropPrefix_x3f(lean_object* v_s_1445_, lean_object* v_pre_1446_){
_start:
{
lean_object* v_t_1447_; lean_object* v_startPos_1448_; lean_object* v_stopPos_1449_; lean_object* v_startPos_1450_; lean_object* v_stopPos_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; uint8_t v___x_1454_; 
lean_inc_ref(v_pre_1446_);
lean_inc_ref(v_s_1445_);
v_t_1447_ = l_Substring_Raw_commonPrefix(v_s_1445_, v_pre_1446_);
v_startPos_1448_ = lean_ctor_get(v_t_1447_, 1);
lean_inc(v_startPos_1448_);
v_stopPos_1449_ = lean_ctor_get(v_t_1447_, 2);
lean_inc(v_stopPos_1449_);
lean_dec_ref(v_t_1447_);
v_startPos_1450_ = lean_ctor_get(v_pre_1446_, 1);
lean_inc(v_startPos_1450_);
v_stopPos_1451_ = lean_ctor_get(v_pre_1446_, 2);
lean_inc(v_stopPos_1451_);
lean_dec_ref(v_pre_1446_);
v___x_1452_ = lean_nat_sub(v_stopPos_1449_, v_startPos_1448_);
lean_dec(v_startPos_1448_);
v___x_1453_ = lean_nat_sub(v_stopPos_1451_, v_startPos_1450_);
lean_dec(v_startPos_1450_);
lean_dec(v_stopPos_1451_);
v___x_1454_ = lean_nat_dec_eq(v___x_1452_, v___x_1453_);
lean_dec(v___x_1453_);
lean_dec(v___x_1452_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; 
lean_dec(v_stopPos_1449_);
lean_dec_ref(v_s_1445_);
v___x_1455_ = lean_box(0);
return v___x_1455_;
}
else
{
lean_object* v_str_1456_; lean_object* v_stopPos_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1465_; 
v_str_1456_ = lean_ctor_get(v_s_1445_, 0);
v_stopPos_1457_ = lean_ctor_get(v_s_1445_, 2);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_s_1445_);
if (v_isSharedCheck_1465_ == 0)
{
lean_object* v_unused_1466_; 
v_unused_1466_ = lean_ctor_get(v_s_1445_, 1);
lean_dec(v_unused_1466_);
v___x_1459_ = v_s_1445_;
v_isShared_1460_ = v_isSharedCheck_1465_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_stopPos_1457_);
lean_inc(v_str_1456_);
lean_dec(v_s_1445_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1465_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 1, v_stopPos_1449_);
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_str_1456_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_stopPos_1449_);
lean_ctor_set(v_reuseFailAlloc_1464_, 2, v_stopPos_1457_);
v___x_1462_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
lean_object* v___x_1463_; 
v___x_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
return v___x_1463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropSuffix_x3f(lean_object* v_s_1467_, lean_object* v_suff_1468_){
_start:
{
lean_object* v_t_1469_; lean_object* v_startPos_1470_; lean_object* v_stopPos_1471_; lean_object* v_startPos_1472_; lean_object* v_stopPos_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; uint8_t v___x_1476_; 
lean_inc_ref(v_suff_1468_);
lean_inc_ref(v_s_1467_);
v_t_1469_ = l_Substring_Raw_commonSuffix(v_s_1467_, v_suff_1468_);
v_startPos_1470_ = lean_ctor_get(v_t_1469_, 1);
lean_inc(v_startPos_1470_);
v_stopPos_1471_ = lean_ctor_get(v_t_1469_, 2);
lean_inc(v_stopPos_1471_);
lean_dec_ref(v_t_1469_);
v_startPos_1472_ = lean_ctor_get(v_suff_1468_, 1);
lean_inc(v_startPos_1472_);
v_stopPos_1473_ = lean_ctor_get(v_suff_1468_, 2);
lean_inc(v_stopPos_1473_);
lean_dec_ref(v_suff_1468_);
v___x_1474_ = lean_nat_sub(v_stopPos_1471_, v_startPos_1470_);
lean_dec(v_stopPos_1471_);
v___x_1475_ = lean_nat_sub(v_stopPos_1473_, v_startPos_1472_);
lean_dec(v_startPos_1472_);
lean_dec(v_stopPos_1473_);
v___x_1476_ = lean_nat_dec_eq(v___x_1474_, v___x_1475_);
lean_dec(v___x_1475_);
lean_dec(v___x_1474_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; 
lean_dec(v_startPos_1470_);
lean_dec_ref(v_s_1467_);
v___x_1477_ = lean_box(0);
return v___x_1477_;
}
else
{
lean_object* v_str_1478_; lean_object* v_startPos_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1487_; 
v_str_1478_ = lean_ctor_get(v_s_1467_, 0);
v_startPos_1479_ = lean_ctor_get(v_s_1467_, 1);
v_isSharedCheck_1487_ = !lean_is_exclusive(v_s_1467_);
if (v_isSharedCheck_1487_ == 0)
{
lean_object* v_unused_1488_; 
v_unused_1488_ = lean_ctor_get(v_s_1467_, 2);
lean_dec(v_unused_1488_);
v___x_1481_ = v_s_1467_;
v_isShared_1482_ = v_isSharedCheck_1487_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_startPos_1479_);
lean_inc(v_str_1478_);
lean_dec(v_s_1467_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1487_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 2, v_startPos_1470_);
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_str_1478_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v_startPos_1479_);
lean_ctor_set(v_reuseFailAlloc_1486_, 2, v_startPos_1470_);
v___x_1484_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1485_; 
v___x_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
return v___x_1485_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg(lean_object* v_x_1489_, lean_object* v_x_1490_, lean_object* v_x_1491_, lean_object* v_h__1_1492_, lean_object* v_h__2_1493_){
_start:
{
lean_object* v_zero_1494_; uint8_t v_isZero_1495_; 
v_zero_1494_ = lean_unsigned_to_nat(0u);
v_isZero_1495_ = lean_nat_dec_eq(v_x_1490_, v_zero_1494_);
if (v_isZero_1495_ == 1)
{
lean_object* v___x_1496_; 
lean_dec(v_h__2_1493_);
v___x_1496_ = lean_apply_2(v_h__1_1492_, v_x_1489_, v_x_1491_);
return v___x_1496_;
}
else
{
lean_object* v_one_1497_; lean_object* v_n_1498_; lean_object* v___x_1499_; 
lean_dec(v_h__1_1492_);
v_one_1497_ = lean_unsigned_to_nat(1u);
v_n_1498_ = lean_nat_sub(v_x_1490_, v_one_1497_);
v___x_1499_ = lean_apply_3(v_h__2_1493_, v_x_1489_, v_n_1498_, v_x_1491_);
return v___x_1499_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg___boxed(lean_object* v_x_1500_, lean_object* v_x_1501_, lean_object* v_x_1502_, lean_object* v_h__1_1503_, lean_object* v_h__2_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg(v_x_1500_, v_x_1501_, v_x_1502_, v_h__1_1503_, v_h__2_1504_);
lean_dec(v_x_1501_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter(lean_object* v_motive_1506_, lean_object* v_x_1507_, lean_object* v_x_1508_, lean_object* v_x_1509_, lean_object* v_h__1_1510_, lean_object* v_h__2_1511_){
_start:
{
lean_object* v_zero_1512_; uint8_t v_isZero_1513_; 
v_zero_1512_ = lean_unsigned_to_nat(0u);
v_isZero_1513_ = lean_nat_dec_eq(v_x_1508_, v_zero_1512_);
if (v_isZero_1513_ == 1)
{
lean_object* v___x_1514_; 
lean_dec(v_h__2_1511_);
v___x_1514_ = lean_apply_2(v_h__1_1510_, v_x_1507_, v_x_1509_);
return v___x_1514_;
}
else
{
lean_object* v_one_1515_; lean_object* v_n_1516_; lean_object* v___x_1517_; 
lean_dec(v_h__1_1510_);
v_one_1515_ = lean_unsigned_to_nat(1u);
v_n_1516_ = lean_nat_sub(v_x_1508_, v_one_1515_);
v___x_1517_ = lean_apply_3(v_h__2_1511_, v_x_1507_, v_n_1516_, v_x_1509_);
return v___x_1517_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___boxed(lean_object* v_motive_1518_, lean_object* v_x_1519_, lean_object* v_x_1520_, lean_object* v_x_1521_, lean_object* v_h__1_1522_, lean_object* v_h__2_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter(v_motive_1518_, v_x_1519_, v_x_1520_, v_x_1521_, v_h__1_1522_, v_h__2_1523_);
lean_dec(v_x_1520_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_Substring_bsize(lean_object* v_a_1525_){
_start:
{
lean_object* v_startPos_1526_; lean_object* v_stopPos_1527_; lean_object* v___x_1528_; 
v_startPos_1526_ = lean_ctor_get(v_a_1525_, 1);
v_stopPos_1527_ = lean_ctor_get(v_a_1525_, 2);
v___x_1528_ = lean_nat_sub(v_stopPos_1527_, v_startPos_1526_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Substring_bsize___boxed(lean_object* v_a_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Substring_bsize(v_a_1529_);
lean_dec_ref(v_a_1529_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Substring_toString(lean_object* v_a_1531_){
_start:
{
lean_object* v_str_1532_; lean_object* v_startPos_1533_; lean_object* v_stopPos_1534_; lean_object* v___x_1535_; 
v_str_1532_ = lean_ctor_get(v_a_1531_, 0);
v_startPos_1533_ = lean_ctor_get(v_a_1531_, 1);
v_stopPos_1534_ = lean_ctor_get(v_a_1531_, 2);
v___x_1535_ = lean_string_utf8_extract(v_str_1532_, v_startPos_1533_, v_stopPos_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Substring_toString___boxed(lean_object* v_a_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l_Substring_toString(v_a_1536_);
lean_dec_ref(v_a_1536_);
return v_res_1537_;
}
}
LEAN_EXPORT uint8_t l_Substring_isEmpty(lean_object* v_ss_1538_){
_start:
{
lean_object* v_startPos_1539_; lean_object* v_stopPos_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; uint8_t v___x_1543_; 
v_startPos_1539_ = lean_ctor_get(v_ss_1538_, 1);
v_stopPos_1540_ = lean_ctor_get(v_ss_1538_, 2);
v___x_1541_ = lean_nat_sub(v_stopPos_1540_, v_startPos_1539_);
v___x_1542_ = lean_unsigned_to_nat(0u);
v___x_1543_ = lean_nat_dec_eq(v___x_1541_, v___x_1542_);
lean_dec(v___x_1541_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Substring_isEmpty___boxed(lean_object* v_ss_1544_){
_start:
{
uint8_t v_res_1545_; lean_object* v_r_1546_; 
v_res_1545_ = l_Substring_isEmpty(v_ss_1544_);
lean_dec_ref(v_ss_1544_);
v_r_1546_ = lean_box(v_res_1545_);
return v_r_1546_;
}
}
LEAN_EXPORT lean_object* l_Substring_next(lean_object* v_a_1547_, lean_object* v_a_1548_){
_start:
{
lean_object* v_str_1549_; lean_object* v_startPos_1550_; lean_object* v_stopPos_1551_; lean_object* v_absP_1552_; uint8_t v_decide_1553_; 
v_str_1549_ = lean_ctor_get(v_a_1547_, 0);
v_startPos_1550_ = lean_ctor_get(v_a_1547_, 1);
v_stopPos_1551_ = lean_ctor_get(v_a_1547_, 2);
v_absP_1552_ = lean_nat_add(v_startPos_1550_, v_a_1548_);
v_decide_1553_ = lean_nat_dec_eq(v_absP_1552_, v_stopPos_1551_);
if (v_decide_1553_ == 0)
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = lean_string_utf8_next(v_str_1549_, v_absP_1552_);
lean_dec(v_absP_1552_);
v___x_1555_ = lean_nat_sub(v___x_1554_, v_startPos_1550_);
lean_dec(v___x_1554_);
return v___x_1555_;
}
else
{
lean_dec(v_absP_1552_);
lean_inc(v_a_1548_);
return v_a_1548_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_next___boxed(lean_object* v_a_1556_, lean_object* v_a_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Substring_next(v_a_1556_, v_a_1557_);
lean_dec(v_a_1557_);
lean_dec_ref(v_a_1556_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Substring_prev(lean_object* v_a_1559_, lean_object* v_a_1560_){
_start:
{
lean_object* v_str_1561_; lean_object* v_startPos_1562_; lean_object* v_absP_1563_; uint8_t v_decide_1564_; 
v_str_1561_ = lean_ctor_get(v_a_1559_, 0);
v_startPos_1562_ = lean_ctor_get(v_a_1559_, 1);
v_absP_1563_ = lean_nat_add(v_startPos_1562_, v_a_1560_);
v_decide_1564_ = lean_nat_dec_eq(v_absP_1563_, v_startPos_1562_);
if (v_decide_1564_ == 0)
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = lean_string_utf8_prev(v_str_1561_, v_absP_1563_);
lean_dec(v_absP_1563_);
v___x_1566_ = lean_nat_sub(v___x_1565_, v_startPos_1562_);
lean_dec(v___x_1565_);
return v___x_1566_;
}
else
{
lean_dec(v_absP_1563_);
lean_inc(v_a_1560_);
return v_a_1560_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_prev___boxed(lean_object* v_a_1567_, lean_object* v_a_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Substring_prev(v_a_1567_, v_a_1568_);
lean_dec(v_a_1568_);
lean_dec_ref(v_a_1567_);
return v_res_1569_;
}
}
LEAN_EXPORT uint8_t l_Substring_atEnd(lean_object* v_a_1570_, lean_object* v_a_1571_){
_start:
{
lean_object* v_startPos_1572_; lean_object* v_stopPos_1573_; lean_object* v___x_1574_; uint8_t v_decide_1575_; 
v_startPos_1572_ = lean_ctor_get(v_a_1570_, 1);
v_stopPos_1573_ = lean_ctor_get(v_a_1570_, 2);
v___x_1574_ = lean_nat_add(v_startPos_1572_, v_a_1571_);
v_decide_1575_ = lean_nat_dec_eq(v___x_1574_, v_stopPos_1573_);
lean_dec(v___x_1574_);
return v_decide_1575_;
}
}
LEAN_EXPORT lean_object* l_Substring_atEnd___boxed(lean_object* v_a_1576_, lean_object* v_a_1577_){
_start:
{
uint8_t v_res_1578_; lean_object* v_r_1579_; 
v_res_1578_ = l_Substring_atEnd(v_a_1576_, v_a_1577_);
lean_dec(v_a_1577_);
lean_dec_ref(v_a_1576_);
v_r_1579_ = lean_box(v_res_1578_);
return v_r_1579_;
}
}
LEAN_EXPORT uint8_t l_Substring_beq(lean_object* v_ss1_1580_, lean_object* v_ss2_1581_){
_start:
{
uint8_t v___x_1582_; 
v___x_1582_ = l_Substring_Raw_beq(v_ss1_1580_, v_ss2_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Substring_beq___boxed(lean_object* v_ss1_1583_, lean_object* v_ss2_1584_){
_start:
{
uint8_t v_res_1585_; lean_object* v_r_1586_; 
v_res_1585_ = l_Substring_beq(v_ss1_1583_, v_ss2_1584_);
v_r_1586_ = lean_box(v_res_1585_);
return v_r_1586_;
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

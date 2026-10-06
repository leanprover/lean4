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
lean_object* v_str_210_; lean_object* v_startPos_211_; lean_object* v_stopPos_212_; uint8_t v___y_214_; uint8_t v___x_223_; 
v_str_210_ = lean_ctor_get(v_s_208_, 0);
lean_inc_ref(v_str_210_);
v_startPos_211_ = lean_ctor_get(v_s_208_, 1);
lean_inc(v_startPos_211_);
v_stopPos_212_ = lean_ctor_get(v_s_208_, 2);
lean_inc(v_stopPos_212_);
lean_dec_ref(v_s_208_);
v___x_223_ = lean_string_is_valid_pos(v_str_210_, v_startPos_211_);
if (v___x_223_ == 0)
{
v___y_214_ = v___x_223_;
goto v___jp_213_;
}
else
{
uint8_t v___x_224_; 
v___x_224_ = lean_string_is_valid_pos(v_str_210_, v_stopPos_212_);
if (v___x_224_ == 0)
{
v___y_214_ = v___x_224_;
goto v___jp_213_;
}
else
{
uint8_t v___x_225_; 
v___x_225_ = lean_nat_dec_le(v_startPos_211_, v_stopPos_212_);
v___y_214_ = v___x_225_;
goto v___jp_213_;
}
}
v___jp_213_:
{
if (v___y_214_ == 0)
{
lean_object* v___x_215_; 
lean_dec_ref(v_str_210_);
v___x_215_ = lean_nat_sub(v_stopPos_212_, v_startPos_211_);
lean_dec(v_startPos_211_);
lean_dec(v_stopPos_212_);
return v___x_215_;
}
else
{
lean_object* v_searcher_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___f_219_; lean_object* v___x_220_; 
v_searcher_216_ = lean_unsigned_to_nat(0u);
v___x_217_ = lean_box(0);
v___x_218_ = lean_box_uint32(v_c_209_);
lean_inc(v_startPos_211_);
lean_inc(v_stopPos_212_);
v___f_219_ = lean_alloc_closure((void*)(l_Substring_Raw_posOf___lam__0___boxed), 9, 5);
lean_closure_set(v___f_219_, 0, v_stopPos_212_);
lean_closure_set(v___f_219_, 1, v_startPos_211_);
lean_closure_set(v___f_219_, 2, v_str_210_);
lean_closure_set(v___f_219_, 3, v___x_218_);
lean_closure_set(v___f_219_, 4, v___x_217_);
v___x_220_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_219_, v_searcher_216_, v___x_217_, lean_box(0));
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v___x_221_; 
v___x_221_ = lean_nat_sub(v_stopPos_212_, v_startPos_211_);
lean_dec(v_startPos_211_);
lean_dec(v_stopPos_212_);
return v___x_221_;
}
else
{
lean_object* v_val_222_; 
lean_dec(v_stopPos_212_);
lean_dec(v_startPos_211_);
v_val_222_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_val_222_);
lean_dec_ref_known(v___x_220_, 1);
return v_val_222_;
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
lean_inc(v___y_401_);
v_b_387_ = v___y_401_;
v_i_388_ = v___y_401_;
v_j_389_ = v___y_400_;
v_r_390_ = v___x_403_;
goto _start;
}
v___jp_408_:
{
lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_413_ = lean_nat_add(v_startPos_406_, v___y_409_);
lean_dec(v___y_409_);
v___x_414_ = lean_nat_dec_le(v_stopPos_407_, v___x_413_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; 
lean_inc_ref(v_str_405_);
v___x_415_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_415_, 0, v_str_405_);
lean_ctor_set(v___x_415_, 1, v___y_412_);
lean_ctor_set(v___x_415_, 2, v___x_413_);
v___y_400_ = v___y_410_;
v___y_401_ = v___y_411_;
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
v___y_400_ = v___y_410_;
v___y_401_ = v___y_411_;
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
v___y_409_ = v___x_423_;
v___y_410_ = v___x_422_;
v___y_411_ = v___y_418_;
v___y_412_ = v___x_425_;
goto v___jp_408_;
}
else
{
lean_dec(v___x_425_);
lean_inc(v_stopPos_407_);
v___y_409_ = v___x_423_;
v___y_410_ = v___x_422_;
v___y_411_ = v___y_418_;
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
v___y_400_ = v___x_422_;
v___y_401_ = v___y_418_;
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
lean_object* v___y_535_; lean_object* v_str_539_; lean_object* v_startPos_540_; lean_object* v_stopPos_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_556_; 
v_str_539_ = lean_ctor_get(v_s_533_, 0);
v_startPos_540_ = lean_ctor_get(v_s_533_, 1);
v_stopPos_541_ = lean_ctor_get(v_s_533_, 2);
v_isSharedCheck_556_ = !lean_is_exclusive(v_s_533_);
if (v_isSharedCheck_556_ == 0)
{
v___x_543_ = v_s_533_;
v_isShared_544_ = v_isSharedCheck_556_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_stopPos_541_);
lean_inc(v_startPos_540_);
lean_inc(v_str_539_);
lean_dec(v_s_533_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_556_;
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
lean_object* v___x_545_; uint8_t v___y_547_; uint8_t v___x_553_; 
v___x_545_ = l_String_instInhabitedSlice;
v___x_553_ = lean_string_is_valid_pos(v_str_539_, v_startPos_540_);
if (v___x_553_ == 0)
{
v___y_547_ = v___x_553_;
goto v___jp_546_;
}
else
{
uint8_t v___x_554_; 
v___x_554_ = lean_string_is_valid_pos(v_str_539_, v_stopPos_541_);
if (v___x_554_ == 0)
{
v___y_547_ = v___x_554_;
goto v___jp_546_;
}
else
{
uint8_t v___x_555_; 
v___x_555_ = lean_nat_dec_le(v_startPos_540_, v_stopPos_541_);
v___y_547_ = v___x_555_;
goto v___jp_546_;
}
}
v___jp_546_:
{
if (v___y_547_ == 0)
{
lean_object* v___x_548_; lean_object* v___x_549_; 
lean_del_object(v___x_543_);
lean_dec(v_stopPos_541_);
lean_dec(v_startPos_540_);
lean_dec_ref(v_str_539_);
v___x_548_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_549_ = l_panic___redArg(v___x_545_, v___x_548_);
v___y_535_ = v___x_549_;
goto v___jp_534_;
}
else
{
lean_object* v___x_551_; 
if (v_isShared_544_ == 0)
{
v___x_551_ = v___x_543_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_str_539_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_startPos_540_);
lean_ctor_set(v_reuseFailAlloc_552_, 2, v_stopPos_541_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
v___y_535_ = v___x_551_;
goto v___jp_534_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldl(lean_object* v_00_u03b1_557_, lean_object* v_f_558_, lean_object* v_init_559_, lean_object* v_s_560_){
_start:
{
lean_object* v___y_562_; lean_object* v_str_566_; lean_object* v_startPos_567_; lean_object* v_stopPos_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_583_; 
v_str_566_ = lean_ctor_get(v_s_560_, 0);
v_startPos_567_ = lean_ctor_get(v_s_560_, 1);
v_stopPos_568_ = lean_ctor_get(v_s_560_, 2);
v_isSharedCheck_583_ = !lean_is_exclusive(v_s_560_);
if (v_isSharedCheck_583_ == 0)
{
v___x_570_ = v_s_560_;
v_isShared_571_ = v_isSharedCheck_583_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_stopPos_568_);
lean_inc(v_startPos_567_);
lean_inc(v_str_566_);
lean_dec(v_s_560_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_583_;
goto v_resetjp_569_;
}
v___jp_561_:
{
lean_object* v___f_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___f_563_ = lean_alloc_closure((void*)(l_Substring_Raw_foldl___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_563_, 0, v___y_562_);
lean_closure_set(v___f_563_, 1, v_f_558_);
v___x_564_ = lean_unsigned_to_nat(0u);
v___x_565_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_563_, v___x_564_, v_init_559_, lean_box(0));
return v___x_565_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; uint8_t v___y_574_; uint8_t v___x_580_; 
v___x_572_ = l_String_instInhabitedSlice;
v___x_580_ = lean_string_is_valid_pos(v_str_566_, v_startPos_567_);
if (v___x_580_ == 0)
{
v___y_574_ = v___x_580_;
goto v___jp_573_;
}
else
{
uint8_t v___x_581_; 
v___x_581_ = lean_string_is_valid_pos(v_str_566_, v_stopPos_568_);
if (v___x_581_ == 0)
{
v___y_574_ = v___x_581_;
goto v___jp_573_;
}
else
{
uint8_t v___x_582_; 
v___x_582_ = lean_nat_dec_le(v_startPos_567_, v_stopPos_568_);
v___y_574_ = v___x_582_;
goto v___jp_573_;
}
}
v___jp_573_:
{
if (v___y_574_ == 0)
{
lean_object* v___x_575_; lean_object* v___x_576_; 
lean_del_object(v___x_570_);
lean_dec(v_stopPos_568_);
lean_dec(v_startPos_567_);
lean_dec_ref(v_str_566_);
v___x_575_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_576_ = l_panic___redArg(v___x_572_, v___x_575_);
v___y_562_ = v___x_576_;
goto v___jp_561_;
}
else
{
lean_object* v___x_578_; 
if (v_isShared_571_ == 0)
{
v___x_578_ = v___x_570_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_str_566_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_startPos_567_);
lean_ctor_set(v_reuseFailAlloc_579_, 2, v_stopPos_568_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
v___y_562_ = v___x_578_;
goto v___jp_561_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr___redArg___lam__0(lean_object* v___y_584_, lean_object* v_f_585_, lean_object* v_it_586_, lean_object* v_acc_587_, lean_object* v_hP_588_, lean_object* v_recur_589_){
_start:
{
lean_object* v___x_590_; uint8_t v_decide_591_; 
v___x_590_ = lean_unsigned_to_nat(0u);
v_decide_591_ = lean_nat_dec_eq(v_it_586_, v___x_590_);
if (v_decide_591_ == 0)
{
lean_object* v_str_592_; lean_object* v_startInclusive_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v_prevPos_596_; lean_object* v___x_597_; uint32_t v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v_str_592_ = lean_ctor_get(v___y_584_, 0);
v_startInclusive_593_ = lean_ctor_get(v___y_584_, 1);
v___x_594_ = lean_unsigned_to_nat(1u);
v___x_595_ = lean_nat_sub(v_it_586_, v___x_594_);
v_prevPos_596_ = l_String_Slice_posLE(v___y_584_, v___x_595_);
v___x_597_ = lean_nat_add(v_startInclusive_593_, v_prevPos_596_);
v___x_598_ = lean_string_utf8_get_fast(v_str_592_, v___x_597_);
lean_dec(v___x_597_);
v___x_599_ = lean_box_uint32(v___x_598_);
v___x_600_ = lean_apply_2(v_f_585_, v___x_599_, v_acc_587_);
v___x_601_ = lean_apply_4(v_recur_589_, v_prevPos_596_, v___x_600_, lean_box(0), lean_box(0));
return v___x_601_;
}
else
{
lean_dec(v_recur_589_);
lean_dec(v_f_585_);
return v_acc_587_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr___redArg___lam__0___boxed(lean_object* v___y_602_, lean_object* v_f_603_, lean_object* v_it_604_, lean_object* v_acc_605_, lean_object* v_hP_606_, lean_object* v_recur_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Substring_Raw_foldr___redArg___lam__0(v___y_602_, v_f_603_, v_it_604_, v_acc_605_, v_hP_606_, v_recur_607_);
lean_dec(v_it_604_);
lean_dec_ref(v___y_602_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr___redArg(lean_object* v_f_609_, lean_object* v_init_610_, lean_object* v_s_611_){
_start:
{
lean_object* v___y_613_; lean_object* v_str_617_; lean_object* v_startPos_618_; lean_object* v_stopPos_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_634_; 
v_str_617_ = lean_ctor_get(v_s_611_, 0);
v_startPos_618_ = lean_ctor_get(v_s_611_, 1);
v_stopPos_619_ = lean_ctor_get(v_s_611_, 2);
v_isSharedCheck_634_ = !lean_is_exclusive(v_s_611_);
if (v_isSharedCheck_634_ == 0)
{
v___x_621_ = v_s_611_;
v_isShared_622_ = v_isSharedCheck_634_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_stopPos_619_);
lean_inc(v_startPos_618_);
lean_inc(v_str_617_);
lean_dec(v_s_611_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_634_;
goto v_resetjp_620_;
}
v___jp_612_:
{
lean_object* v___f_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
lean_inc_ref(v___y_613_);
v___f_614_ = lean_alloc_closure((void*)(l_Substring_Raw_foldr___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_614_, 0, v___y_613_);
lean_closure_set(v___f_614_, 1, v_f_609_);
v___x_615_ = l_String_Slice_revPositions(v___y_613_);
lean_dec_ref(v___y_613_);
v___x_616_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_614_, v___x_615_, v_init_610_, lean_box(0));
return v___x_616_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; uint8_t v___y_625_; uint8_t v___x_631_; 
v___x_623_ = l_String_instInhabitedSlice;
v___x_631_ = lean_string_is_valid_pos(v_str_617_, v_startPos_618_);
if (v___x_631_ == 0)
{
v___y_625_ = v___x_631_;
goto v___jp_624_;
}
else
{
uint8_t v___x_632_; 
v___x_632_ = lean_string_is_valid_pos(v_str_617_, v_stopPos_619_);
if (v___x_632_ == 0)
{
v___y_625_ = v___x_632_;
goto v___jp_624_;
}
else
{
uint8_t v___x_633_; 
v___x_633_ = lean_nat_dec_le(v_startPos_618_, v_stopPos_619_);
v___y_625_ = v___x_633_;
goto v___jp_624_;
}
}
v___jp_624_:
{
if (v___y_625_ == 0)
{
lean_object* v___x_626_; lean_object* v___x_627_; 
lean_del_object(v___x_621_);
lean_dec(v_stopPos_619_);
lean_dec(v_startPos_618_);
lean_dec_ref(v_str_617_);
v___x_626_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_627_ = l_panic___redArg(v___x_623_, v___x_626_);
v___y_613_ = v___x_627_;
goto v___jp_612_;
}
else
{
lean_object* v___x_629_; 
if (v_isShared_622_ == 0)
{
v___x_629_ = v___x_621_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_str_617_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_startPos_618_);
lean_ctor_set(v_reuseFailAlloc_630_, 2, v_stopPos_619_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
v___y_613_ = v___x_629_;
goto v___jp_612_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr(lean_object* v_00_u03b1_635_, lean_object* v_f_636_, lean_object* v_init_637_, lean_object* v_s_638_){
_start:
{
lean_object* v___y_640_; lean_object* v_str_644_; lean_object* v_startPos_645_; lean_object* v_stopPos_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_661_; 
v_str_644_ = lean_ctor_get(v_s_638_, 0);
v_startPos_645_ = lean_ctor_get(v_s_638_, 1);
v_stopPos_646_ = lean_ctor_get(v_s_638_, 2);
v_isSharedCheck_661_ = !lean_is_exclusive(v_s_638_);
if (v_isSharedCheck_661_ == 0)
{
v___x_648_ = v_s_638_;
v_isShared_649_ = v_isSharedCheck_661_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_stopPos_646_);
lean_inc(v_startPos_645_);
lean_inc(v_str_644_);
lean_dec(v_s_638_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_661_;
goto v_resetjp_647_;
}
v___jp_639_:
{
lean_object* v___f_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
lean_inc_ref(v___y_640_);
v___f_641_ = lean_alloc_closure((void*)(l_Substring_Raw_foldr___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_641_, 0, v___y_640_);
lean_closure_set(v___f_641_, 1, v_f_636_);
v___x_642_ = l_String_Slice_revPositions(v___y_640_);
lean_dec_ref(v___y_640_);
v___x_643_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_641_, v___x_642_, v_init_637_, lean_box(0));
return v___x_643_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; uint8_t v___y_652_; uint8_t v___x_658_; 
v___x_650_ = l_String_instInhabitedSlice;
v___x_658_ = lean_string_is_valid_pos(v_str_644_, v_startPos_645_);
if (v___x_658_ == 0)
{
v___y_652_ = v___x_658_;
goto v___jp_651_;
}
else
{
uint8_t v___x_659_; 
v___x_659_ = lean_string_is_valid_pos(v_str_644_, v_stopPos_646_);
if (v___x_659_ == 0)
{
v___y_652_ = v___x_659_;
goto v___jp_651_;
}
else
{
uint8_t v___x_660_; 
v___x_660_ = lean_nat_dec_le(v_startPos_645_, v_stopPos_646_);
v___y_652_ = v___x_660_;
goto v___jp_651_;
}
}
v___jp_651_:
{
if (v___y_652_ == 0)
{
lean_object* v___x_653_; lean_object* v___x_654_; 
lean_del_object(v___x_648_);
lean_dec(v_stopPos_646_);
lean_dec(v_startPos_645_);
lean_dec_ref(v_str_644_);
v___x_653_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_654_ = l_panic___redArg(v___x_650_, v___x_653_);
v___y_640_ = v___x_654_;
goto v___jp_639_;
}
else
{
lean_object* v___x_656_; 
if (v_isShared_649_ == 0)
{
v___x_656_ = v___x_648_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_str_644_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v_startPos_645_);
lean_ctor_set(v_reuseFailAlloc_657_, 2, v_stopPos_646_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
v___y_640_ = v___x_656_;
goto v___jp_639_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_any___lam__0(lean_object* v___x_662_, lean_object* v_s_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(v_s_663_, v___x_662_, v___y_664_, lean_box(0), lean_box(0), v___y_667_, v___y_668_, v___y_669_);
return v___x_670_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_any(lean_object* v_s_671_, lean_object* v_p_672_){
_start:
{
lean_object* v___x_673_; lean_object* v_str_674_; lean_object* v_startPos_675_; lean_object* v_stopPos_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_695_; 
lean_inc_ref(v_p_672_);
v___x_673_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v_p_672_);
v_str_674_ = lean_ctor_get(v_s_671_, 0);
v_startPos_675_ = lean_ctor_get(v_s_671_, 1);
v_stopPos_676_ = lean_ctor_get(v_s_671_, 2);
v_isSharedCheck_695_ = !lean_is_exclusive(v_s_671_);
if (v_isSharedCheck_695_ == 0)
{
v___x_678_ = v_s_671_;
v_isShared_679_ = v_isSharedCheck_695_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_stopPos_676_);
lean_inc(v_startPos_675_);
lean_inc(v_str_674_);
lean_dec(v_s_671_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_695_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_680_; lean_object* v___f_681_; lean_object* v___x_682_; uint8_t v___y_684_; uint8_t v___x_692_; 
v___x_680_ = l_String_instInhabitedSlice;
v___f_681_ = lean_alloc_closure((void*)(l_Substring_Raw_any___lam__0), 8, 1);
lean_closure_set(v___f_681_, 0, v___x_673_);
v___x_682_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_682_, 0, lean_box(0));
lean_closure_set(v___x_682_, 1, v_p_672_);
v___x_692_ = lean_string_is_valid_pos(v_str_674_, v_startPos_675_);
if (v___x_692_ == 0)
{
v___y_684_ = v___x_692_;
goto v___jp_683_;
}
else
{
uint8_t v___x_693_; 
v___x_693_ = lean_string_is_valid_pos(v_str_674_, v_stopPos_676_);
if (v___x_693_ == 0)
{
v___y_684_ = v___x_693_;
goto v___jp_683_;
}
else
{
uint8_t v___x_694_; 
v___x_694_ = lean_nat_dec_le(v_startPos_675_, v_stopPos_676_);
v___y_684_ = v___x_694_;
goto v___jp_683_;
}
}
v___jp_683_:
{
if (v___y_684_ == 0)
{
lean_object* v___x_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
lean_del_object(v___x_678_);
lean_dec(v_stopPos_676_);
lean_dec(v_startPos_675_);
lean_dec_ref(v_str_674_);
v___x_685_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_686_ = l_panic___redArg(v___x_680_, v___x_685_);
v___x_687_ = l_String_Slice_contains___redArg(v___f_681_, v___x_686_, v___x_682_);
return v___x_687_;
}
else
{
lean_object* v___x_689_; 
if (v_isShared_679_ == 0)
{
v___x_689_ = v___x_678_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_str_674_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v_startPos_675_);
lean_ctor_set(v_reuseFailAlloc_691_, 2, v_stopPos_676_);
v___x_689_ = v_reuseFailAlloc_691_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
uint8_t v___x_690_; 
v___x_690_ = l_String_Slice_contains___redArg(v___f_681_, v___x_689_, v___x_682_);
return v___x_690_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_any___boxed(lean_object* v_s_696_, lean_object* v_p_697_){
_start:
{
uint8_t v_res_698_; lean_object* v_r_699_; 
v_res_698_ = l_Substring_Raw_any(v_s_696_, v_p_697_);
v_r_699_ = lean_box(v_res_698_);
return v_r_699_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_all(lean_object* v_s_700_, lean_object* v_p_701_){
_start:
{
lean_object* v___y_703_; lean_object* v_startInclusive_704_; lean_object* v_endExclusive_705_; lean_object* v_str_711_; lean_object* v_startPos_712_; lean_object* v_stopPos_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_730_; 
v_str_711_ = lean_ctor_get(v_s_700_, 0);
v_startPos_712_ = lean_ctor_get(v_s_700_, 1);
v_stopPos_713_ = lean_ctor_get(v_s_700_, 2);
v_isSharedCheck_730_ = !lean_is_exclusive(v_s_700_);
if (v_isSharedCheck_730_ == 0)
{
v___x_715_ = v_s_700_;
v_isShared_716_ = v_isSharedCheck_730_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_stopPos_713_);
lean_inc(v_startPos_712_);
lean_inc(v_str_711_);
lean_dec(v_s_700_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_730_;
goto v_resetjp_714_;
}
v___jp_702_:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; uint8_t v_decide_710_; 
v___x_706_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v_p_701_);
v___x_707_ = lean_unsigned_to_nat(0u);
v___x_708_ = l_String_Slice_Pos_skipWhile___redArg(v___y_703_, v___x_707_, v___x_706_);
lean_dec_ref(v___y_703_);
v___x_709_ = lean_nat_sub(v_endExclusive_705_, v_startInclusive_704_);
lean_dec(v_startInclusive_704_);
lean_dec(v_endExclusive_705_);
v_decide_710_ = lean_nat_dec_eq(v___x_708_, v___x_709_);
lean_dec(v___x_709_);
lean_dec(v___x_708_);
return v_decide_710_;
}
v_resetjp_714_:
{
lean_object* v___x_717_; uint8_t v___y_719_; uint8_t v___x_727_; 
v___x_717_ = l_String_instInhabitedSlice;
v___x_727_ = lean_string_is_valid_pos(v_str_711_, v_startPos_712_);
if (v___x_727_ == 0)
{
v___y_719_ = v___x_727_;
goto v___jp_718_;
}
else
{
uint8_t v___x_728_; 
v___x_728_ = lean_string_is_valid_pos(v_str_711_, v_stopPos_713_);
if (v___x_728_ == 0)
{
v___y_719_ = v___x_728_;
goto v___jp_718_;
}
else
{
uint8_t v___x_729_; 
v___x_729_ = lean_nat_dec_le(v_startPos_712_, v_stopPos_713_);
v___y_719_ = v___x_729_;
goto v___jp_718_;
}
}
v___jp_718_:
{
if (v___y_719_ == 0)
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v_startInclusive_722_; lean_object* v_endExclusive_723_; 
lean_del_object(v___x_715_);
lean_dec(v_stopPos_713_);
lean_dec(v_startPos_712_);
lean_dec_ref(v_str_711_);
v___x_720_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_721_ = l_panic___redArg(v___x_717_, v___x_720_);
v_startInclusive_722_ = lean_ctor_get(v___x_721_, 1);
lean_inc(v_startInclusive_722_);
v_endExclusive_723_ = lean_ctor_get(v___x_721_, 2);
lean_inc(v_endExclusive_723_);
v___y_703_ = v___x_721_;
v_startInclusive_704_ = v_startInclusive_722_;
v_endExclusive_705_ = v_endExclusive_723_;
goto v___jp_702_;
}
else
{
lean_object* v___x_725_; 
lean_inc(v_stopPos_713_);
lean_inc(v_startPos_712_);
if (v_isShared_716_ == 0)
{
v___x_725_ = v___x_715_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_str_711_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_startPos_712_);
lean_ctor_set(v_reuseFailAlloc_726_, 2, v_stopPos_713_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
v___y_703_ = v___x_725_;
v_startInclusive_704_ = v_startPos_712_;
v_endExclusive_705_ = v_stopPos_713_;
goto v___jp_702_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_all___boxed(lean_object* v_s_731_, lean_object* v_p_732_){
_start:
{
uint8_t v_res_733_; lean_object* v_r_734_; 
v_res_733_ = l_Substring_Raw_all(v_s_731_, v_p_732_);
v_r_734_ = lean_box(v_res_733_);
return v_r_734_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(lean_object* v_msg_735_){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = l_String_instInhabitedSlice;
v___x_737_ = lean_panic_fn_borrowed(v___x_736_, v_msg_735_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0(lean_object* v_p_738_, lean_object* v_s_739_, lean_object* v_pos_740_){
_start:
{
lean_object* v_str_741_; lean_object* v_startInclusive_742_; lean_object* v_endExclusive_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; uint8_t v_decide_747_; 
v_str_741_ = lean_ctor_get(v_s_739_, 0);
v_startInclusive_742_ = lean_ctor_get(v_s_739_, 1);
v_endExclusive_743_ = lean_ctor_get(v_s_739_, 2);
v___x_744_ = lean_nat_add(v_startInclusive_742_, v_pos_740_);
v___x_745_ = lean_unsigned_to_nat(0u);
v___x_746_ = lean_nat_sub(v_endExclusive_743_, v___x_744_);
v_decide_747_ = lean_nat_dec_eq(v___x_745_, v___x_746_);
lean_dec(v___x_746_);
if (v_decide_747_ == 0)
{
uint32_t v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_748_ = lean_string_utf8_get_fast(v_str_741_, v___x_744_);
v___x_749_ = lean_box_uint32(v___x_748_);
lean_inc_ref(v_p_738_);
v___x_750_ = lean_apply_1(v_p_738_, v___x_749_);
v___x_751_ = lean_unbox(v___x_750_);
if (v___x_751_ == 0)
{
lean_dec(v___x_744_);
lean_dec_ref(v_p_738_);
return v_pos_740_;
}
else
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_752_ = lean_string_utf8_next_fast(v_str_741_, v___x_744_);
v___x_753_ = lean_nat_sub(v___x_752_, v___x_744_);
lean_dec(v___x_744_);
v___x_754_ = lean_nat_add(v_pos_740_, v___x_753_);
lean_dec(v___x_753_);
v___x_755_ = lean_unsigned_to_nat(1u);
v___x_756_ = lean_nat_add(v_pos_740_, v___x_755_);
v___x_757_ = lean_nat_dec_le(v___x_756_, v___x_754_);
lean_dec(v___x_756_);
if (v___x_757_ == 0)
{
lean_dec(v___x_754_);
lean_dec_ref(v_p_738_);
return v_pos_740_;
}
else
{
lean_dec(v_pos_740_);
v_pos_740_ = v___x_754_;
goto _start;
}
}
}
else
{
lean_dec(v___x_744_);
lean_dec_ref(v_p_738_);
return v_pos_740_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0___boxed(lean_object* v_p_759_, lean_object* v_s_760_, lean_object* v_pos_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0(v_p_759_, v_s_760_, v_pos_761_);
lean_dec_ref(v_s_760_);
return v_res_762_;
}
}
LEAN_EXPORT uint8_t lean_substring_all(lean_object* v_s_763_, lean_object* v_p_764_){
_start:
{
lean_object* v___y_766_; lean_object* v_startInclusive_767_; lean_object* v_endExclusive_768_; lean_object* v_str_773_; lean_object* v_startPos_774_; lean_object* v_stopPos_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_791_; 
v_str_773_ = lean_ctor_get(v_s_763_, 0);
v_startPos_774_ = lean_ctor_get(v_s_763_, 1);
v_stopPos_775_ = lean_ctor_get(v_s_763_, 2);
v_isSharedCheck_791_ = !lean_is_exclusive(v_s_763_);
if (v_isSharedCheck_791_ == 0)
{
v___x_777_ = v_s_763_;
v_isShared_778_ = v_isSharedCheck_791_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_stopPos_775_);
lean_inc(v_startPos_774_);
lean_inc(v_str_773_);
lean_dec(v_s_763_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_791_;
goto v_resetjp_776_;
}
v___jp_765_:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; uint8_t v_decide_772_; 
v___x_769_ = lean_unsigned_to_nat(0u);
v___x_770_ = l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0(v_p_764_, v___y_766_, v___x_769_);
lean_dec_ref(v___y_766_);
v___x_771_ = lean_nat_sub(v_endExclusive_768_, v_startInclusive_767_);
lean_dec(v_startInclusive_767_);
lean_dec(v_endExclusive_768_);
v_decide_772_ = lean_nat_dec_eq(v___x_770_, v___x_771_);
lean_dec(v___x_771_);
lean_dec(v___x_770_);
return v_decide_772_;
}
v_resetjp_776_:
{
uint8_t v___y_780_; uint8_t v___x_788_; 
v___x_788_ = lean_string_is_valid_pos(v_str_773_, v_startPos_774_);
if (v___x_788_ == 0)
{
v___y_780_ = v___x_788_;
goto v___jp_779_;
}
else
{
uint8_t v___x_789_; 
v___x_789_ = lean_string_is_valid_pos(v_str_773_, v_stopPos_775_);
if (v___x_789_ == 0)
{
v___y_780_ = v___x_789_;
goto v___jp_779_;
}
else
{
uint8_t v___x_790_; 
v___x_790_ = lean_nat_dec_le(v_startPos_774_, v_stopPos_775_);
v___y_780_ = v___x_790_;
goto v___jp_779_;
}
}
v___jp_779_:
{
if (v___y_780_ == 0)
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v_startInclusive_783_; lean_object* v_endExclusive_784_; 
lean_del_object(v___x_777_);
lean_dec(v_stopPos_775_);
lean_dec(v_startPos_774_);
lean_dec_ref(v_str_773_);
v___x_781_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_782_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_781_);
v_startInclusive_783_ = lean_ctor_get(v___x_782_, 1);
lean_inc(v_startInclusive_783_);
v_endExclusive_784_ = lean_ctor_get(v___x_782_, 2);
lean_inc(v_endExclusive_784_);
v___y_766_ = v___x_782_;
v_startInclusive_767_ = v_startInclusive_783_;
v_endExclusive_768_ = v_endExclusive_784_;
goto v___jp_765_;
}
else
{
lean_object* v___x_786_; 
lean_inc(v_stopPos_775_);
lean_inc(v_startPos_774_);
if (v_isShared_778_ == 0)
{
v___x_786_ = v___x_777_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_str_773_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_startPos_774_);
lean_ctor_set(v_reuseFailAlloc_787_, 2, v_stopPos_775_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
v___y_766_ = v___x_786_;
v_startInclusive_767_ = v_startPos_774_;
v_endExclusive_768_ = v_stopPos_775_;
goto v___jp_765_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_allImpl___boxed(lean_object* v_s_792_, lean_object* v_p_793_){
_start:
{
uint8_t v_res_794_; lean_object* v_r_795_; 
v_res_794_ = lean_substring_all(v_s_792_, v_p_793_);
v_r_795_ = lean_box(v_res_794_);
return v_r_795_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_contains___lam__0(uint32_t v_c_796_, uint32_t v_a_797_){
_start:
{
uint8_t v___x_798_; 
v___x_798_ = lean_uint32_dec_eq(v_a_797_, v_c_796_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_contains___lam__0___boxed(lean_object* v_c_799_, lean_object* v_a_800_){
_start:
{
uint32_t v_c_boxed_801_; uint32_t v_a_boxed_802_; uint8_t v_res_803_; lean_object* v_r_804_; 
v_c_boxed_801_ = lean_unbox_uint32(v_c_799_);
lean_dec(v_c_799_);
v_a_boxed_802_ = lean_unbox_uint32(v_a_800_);
lean_dec(v_a_800_);
v_res_803_ = l_Substring_Raw_contains___lam__0(v_c_boxed_801_, v_a_boxed_802_);
v_r_804_ = lean_box(v_res_803_);
return v_r_804_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_contains(lean_object* v_s_805_, uint32_t v_c_806_){
_start:
{
lean_object* v___x_807_; lean_object* v___f_808_; lean_object* v___x_809_; lean_object* v_str_810_; lean_object* v_startPos_811_; lean_object* v_stopPos_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_831_; 
v___x_807_ = lean_box_uint32(v_c_806_);
v___f_808_ = lean_alloc_closure((void*)(l_Substring_Raw_contains___lam__0___boxed), 2, 1);
lean_closure_set(v___f_808_, 0, v___x_807_);
lean_inc_ref(v___f_808_);
v___x_809_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___f_808_);
v_str_810_ = lean_ctor_get(v_s_805_, 0);
v_startPos_811_ = lean_ctor_get(v_s_805_, 1);
v_stopPos_812_ = lean_ctor_get(v_s_805_, 2);
v_isSharedCheck_831_ = !lean_is_exclusive(v_s_805_);
if (v_isSharedCheck_831_ == 0)
{
v___x_814_ = v_s_805_;
v_isShared_815_ = v_isSharedCheck_831_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_stopPos_812_);
lean_inc(v_startPos_811_);
lean_inc(v_str_810_);
lean_dec(v_s_805_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_831_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; lean_object* v___f_817_; lean_object* v___x_818_; uint8_t v___y_820_; uint8_t v___x_828_; 
v___x_816_ = l_String_instInhabitedSlice;
v___f_817_ = lean_alloc_closure((void*)(l_Substring_Raw_any___lam__0), 8, 1);
lean_closure_set(v___f_817_, 0, v___x_809_);
v___x_818_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_818_, 0, lean_box(0));
lean_closure_set(v___x_818_, 1, v___f_808_);
v___x_828_ = lean_string_is_valid_pos(v_str_810_, v_startPos_811_);
if (v___x_828_ == 0)
{
v___y_820_ = v___x_828_;
goto v___jp_819_;
}
else
{
uint8_t v___x_829_; 
v___x_829_ = lean_string_is_valid_pos(v_str_810_, v_stopPos_812_);
if (v___x_829_ == 0)
{
v___y_820_ = v___x_829_;
goto v___jp_819_;
}
else
{
uint8_t v___x_830_; 
v___x_830_ = lean_nat_dec_le(v_startPos_811_, v_stopPos_812_);
v___y_820_ = v___x_830_;
goto v___jp_819_;
}
}
v___jp_819_:
{
if (v___y_820_ == 0)
{
lean_object* v___x_821_; lean_object* v___x_822_; uint8_t v___x_823_; 
lean_del_object(v___x_814_);
lean_dec(v_stopPos_812_);
lean_dec(v_startPos_811_);
lean_dec_ref(v_str_810_);
v___x_821_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_822_ = l_panic___redArg(v___x_816_, v___x_821_);
v___x_823_ = l_String_Slice_contains___redArg(v___f_817_, v___x_822_, v___x_818_);
return v___x_823_;
}
else
{
lean_object* v___x_825_; 
if (v_isShared_815_ == 0)
{
v___x_825_ = v___x_814_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_str_810_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v_startPos_811_);
lean_ctor_set(v_reuseFailAlloc_827_, 2, v_stopPos_812_);
v___x_825_ = v_reuseFailAlloc_827_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
uint8_t v___x_826_; 
v___x_826_ = l_String_Slice_contains___redArg(v___f_817_, v___x_825_, v___x_818_);
return v___x_826_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_contains___boxed(lean_object* v_s_832_, lean_object* v_c_833_){
_start:
{
uint32_t v_c_boxed_834_; uint8_t v_res_835_; lean_object* v_r_836_; 
v_c_boxed_834_ = lean_unbox_uint32(v_c_833_);
lean_dec(v_c_833_);
v_res_835_ = l_Substring_Raw_contains(v_s_832_, v_c_boxed_834_);
v_r_836_ = lean_box(v_res_835_);
return v_r_836_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux(lean_object* v_s_837_, lean_object* v_stopPos_838_, lean_object* v_p_839_, lean_object* v_i_840_){
_start:
{
uint8_t v___y_842_; lean_object* v___x_845_; lean_object* v___x_846_; uint8_t v___x_847_; 
v___x_845_ = lean_unsigned_to_nat(1u);
v___x_846_ = lean_nat_add(v_i_840_, v___x_845_);
v___x_847_ = lean_nat_dec_le(v___x_846_, v_stopPos_838_);
lean_dec(v___x_846_);
if (v___x_847_ == 0)
{
lean_dec_ref(v_p_839_);
return v_i_840_;
}
else
{
if (v___x_847_ == 0)
{
v___y_842_ = v___x_847_;
goto v___jp_841_;
}
else
{
uint32_t v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; uint8_t v___x_851_; 
v___x_848_ = lean_string_utf8_get(v_s_837_, v_i_840_);
v___x_849_ = lean_box_uint32(v___x_848_);
lean_inc_ref(v_p_839_);
v___x_850_ = lean_apply_1(v_p_839_, v___x_849_);
v___x_851_ = lean_unbox(v___x_850_);
v___y_842_ = v___x_851_;
goto v___jp_841_;
}
}
v___jp_841_:
{
if (v___y_842_ == 0)
{
lean_dec_ref(v_p_839_);
return v_i_840_;
}
else
{
lean_object* v___x_843_; 
v___x_843_ = lean_string_utf8_next(v_s_837_, v_i_840_);
lean_dec(v_i_840_);
v_i_840_ = v___x_843_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___boxed(lean_object* v_s_852_, lean_object* v_stopPos_853_, lean_object* v_p_854_, lean_object* v_i_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Substring_Raw_takeWhileAux(v_s_852_, v_stopPos_853_, v_p_854_, v_i_855_);
lean_dec(v_stopPos_853_);
lean_dec_ref(v_s_852_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhile(lean_object* v_x_857_, lean_object* v_x_858_){
_start:
{
lean_object* v_str_859_; lean_object* v_startPos_860_; lean_object* v_stopPos_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_869_; 
v_str_859_ = lean_ctor_get(v_x_857_, 0);
v_startPos_860_ = lean_ctor_get(v_x_857_, 1);
v_stopPos_861_ = lean_ctor_get(v_x_857_, 2);
v_isSharedCheck_869_ = !lean_is_exclusive(v_x_857_);
if (v_isSharedCheck_869_ == 0)
{
v___x_863_ = v_x_857_;
v_isShared_864_ = v_isSharedCheck_869_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_stopPos_861_);
lean_inc(v_startPos_860_);
lean_inc(v_str_859_);
lean_dec(v_x_857_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_869_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v_e_865_; lean_object* v___x_867_; 
lean_inc(v_startPos_860_);
v_e_865_ = l_Substring_Raw_takeWhileAux(v_str_859_, v_stopPos_861_, v_x_858_, v_startPos_860_);
lean_dec(v_stopPos_861_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 2, v_e_865_);
v___x_867_ = v___x_863_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_str_859_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v_startPos_860_);
lean_ctor_set(v_reuseFailAlloc_868_, 2, v_e_865_);
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
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(lean_object* v_a_870_, lean_object* v_s_871_, lean_object* v_stopPos_872_, lean_object* v_i_873_){
_start:
{
uint8_t v___y_875_; lean_object* v___x_878_; lean_object* v___x_879_; uint8_t v___x_880_; 
v___x_878_ = lean_unsigned_to_nat(1u);
v___x_879_ = lean_nat_add(v_i_873_, v___x_878_);
v___x_880_ = lean_nat_dec_le(v___x_879_, v_stopPos_872_);
lean_dec(v___x_879_);
if (v___x_880_ == 0)
{
lean_dec_ref(v_a_870_);
return v_i_873_;
}
else
{
if (v___x_880_ == 0)
{
v___y_875_ = v___x_880_;
goto v___jp_874_;
}
else
{
uint32_t v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; uint8_t v___x_884_; 
v___x_881_ = lean_string_utf8_get(v_s_871_, v_i_873_);
v___x_882_ = lean_box_uint32(v___x_881_);
lean_inc_ref(v_a_870_);
v___x_883_ = lean_apply_1(v_a_870_, v___x_882_);
v___x_884_ = lean_unbox(v___x_883_);
v___y_875_ = v___x_884_;
goto v___jp_874_;
}
}
v___jp_874_:
{
if (v___y_875_ == 0)
{
lean_dec_ref(v_a_870_);
return v_i_873_;
}
else
{
lean_object* v___x_876_; 
v___x_876_ = lean_string_utf8_next(v_s_871_, v_i_873_);
lean_dec(v_i_873_);
v_i_873_ = v___x_876_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0___boxed(lean_object* v_a_885_, lean_object* v_s_886_, lean_object* v_stopPos_887_, lean_object* v_i_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(v_a_885_, v_s_886_, v_stopPos_887_, v_i_888_);
lean_dec(v_stopPos_887_);
lean_dec_ref(v_s_886_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* lean_substring_takewhile(lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_str_892_; lean_object* v_startPos_893_; lean_object* v_stopPos_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_902_; 
v_str_892_ = lean_ctor_get(v_a_890_, 0);
v_startPos_893_ = lean_ctor_get(v_a_890_, 1);
v_stopPos_894_ = lean_ctor_get(v_a_890_, 2);
v_isSharedCheck_902_ = !lean_is_exclusive(v_a_890_);
if (v_isSharedCheck_902_ == 0)
{
v___x_896_ = v_a_890_;
v_isShared_897_ = v_isSharedCheck_902_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_stopPos_894_);
lean_inc(v_startPos_893_);
lean_inc(v_str_892_);
lean_dec(v_a_890_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_902_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v_e_898_; lean_object* v___x_900_; 
lean_inc(v_startPos_893_);
v_e_898_ = l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(v_a_891_, v_str_892_, v_stopPos_894_, v_startPos_893_);
lean_dec(v_stopPos_894_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 2, v_e_898_);
v___x_900_ = v___x_896_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_str_892_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_startPos_893_);
lean_ctor_set(v_reuseFailAlloc_901_, 2, v_e_898_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropWhile(lean_object* v_x_903_, lean_object* v_x_904_){
_start:
{
lean_object* v_str_905_; lean_object* v_startPos_906_; lean_object* v_stopPos_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_915_; 
v_str_905_ = lean_ctor_get(v_x_903_, 0);
v_startPos_906_ = lean_ctor_get(v_x_903_, 1);
v_stopPos_907_ = lean_ctor_get(v_x_903_, 2);
v_isSharedCheck_915_ = !lean_is_exclusive(v_x_903_);
if (v_isSharedCheck_915_ == 0)
{
v___x_909_ = v_x_903_;
v_isShared_910_ = v_isSharedCheck_915_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_stopPos_907_);
lean_inc(v_startPos_906_);
lean_inc(v_str_905_);
lean_dec(v_x_903_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_915_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v_b_911_; lean_object* v___x_913_; 
v_b_911_ = l_Substring_Raw_takeWhileAux(v_str_905_, v_stopPos_907_, v_x_904_, v_startPos_906_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 1, v_b_911_);
v___x_913_ = v___x_909_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_str_905_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v_b_911_);
lean_ctor_set(v_reuseFailAlloc_914_, 2, v_stopPos_907_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux(lean_object* v_s_916_, lean_object* v_begPos_917_, lean_object* v_p_918_, lean_object* v_i_919_){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; uint8_t v___x_922_; 
v___x_920_ = lean_unsigned_to_nat(1u);
v___x_921_ = lean_nat_add(v_begPos_917_, v___x_920_);
v___x_922_ = lean_nat_dec_le(v___x_921_, v_i_919_);
lean_dec(v___x_921_);
if (v___x_922_ == 0)
{
lean_dec_ref(v_p_918_);
return v_i_919_;
}
else
{
lean_object* v_i_x27_923_; uint8_t v___y_925_; uint8_t v___y_928_; uint32_t v_c_929_; lean_object* v___x_930_; lean_object* v___x_931_; uint8_t v___x_932_; 
v_i_x27_923_ = lean_string_utf8_prev(v_s_916_, v_i_919_);
v_c_929_ = lean_string_utf8_get(v_s_916_, v_i_x27_923_);
v___x_930_ = lean_box_uint32(v_c_929_);
lean_inc_ref(v_p_918_);
v___x_931_ = lean_apply_1(v_p_918_, v___x_930_);
v___x_932_ = lean_unbox(v___x_931_);
if (v___x_932_ == 0)
{
v___y_928_ = v___x_922_;
goto v___jp_927_;
}
else
{
uint8_t v___x_933_; 
v___x_933_ = 0;
v___y_928_ = v___x_933_;
goto v___jp_927_;
}
v___jp_924_:
{
if (v___y_925_ == 0)
{
lean_dec(v_i_919_);
v_i_919_ = v_i_x27_923_;
goto _start;
}
else
{
lean_dec(v_i_x27_923_);
lean_dec_ref(v_p_918_);
return v_i_919_;
}
}
v___jp_927_:
{
if (v___x_922_ == 0)
{
v___y_925_ = v___x_922_;
goto v___jp_924_;
}
else
{
v___y_925_ = v___y_928_;
goto v___jp_924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux___boxed(lean_object* v_s_934_, lean_object* v_begPos_935_, lean_object* v_p_936_, lean_object* v_i_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Substring_Raw_takeRightWhileAux(v_s_934_, v_begPos_935_, v_p_936_, v_i_937_);
lean_dec(v_begPos_935_);
lean_dec_ref(v_s_934_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhile(lean_object* v_x_939_, lean_object* v_x_940_){
_start:
{
lean_object* v_str_941_; lean_object* v_startPos_942_; lean_object* v_stopPos_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_951_; 
v_str_941_ = lean_ctor_get(v_x_939_, 0);
v_startPos_942_ = lean_ctor_get(v_x_939_, 1);
v_stopPos_943_ = lean_ctor_get(v_x_939_, 2);
v_isSharedCheck_951_ = !lean_is_exclusive(v_x_939_);
if (v_isSharedCheck_951_ == 0)
{
v___x_945_ = v_x_939_;
v_isShared_946_ = v_isSharedCheck_951_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_stopPos_943_);
lean_inc(v_startPos_942_);
lean_inc(v_str_941_);
lean_dec(v_x_939_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_951_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v_b_947_; lean_object* v___x_949_; 
lean_inc(v_stopPos_943_);
v_b_947_ = l_Substring_Raw_takeRightWhileAux(v_str_941_, v_startPos_942_, v_x_940_, v_stopPos_943_);
lean_dec(v_startPos_942_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 1, v_b_947_);
v___x_949_ = v___x_945_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_str_941_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_b_947_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_stopPos_943_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropRightWhile(lean_object* v_x_952_, lean_object* v_x_953_){
_start:
{
lean_object* v_str_954_; lean_object* v_startPos_955_; lean_object* v_stopPos_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_964_; 
v_str_954_ = lean_ctor_get(v_x_952_, 0);
v_startPos_955_ = lean_ctor_get(v_x_952_, 1);
v_stopPos_956_ = lean_ctor_get(v_x_952_, 2);
v_isSharedCheck_964_ = !lean_is_exclusive(v_x_952_);
if (v_isSharedCheck_964_ == 0)
{
v___x_958_ = v_x_952_;
v_isShared_959_ = v_isSharedCheck_964_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_stopPos_956_);
lean_inc(v_startPos_955_);
lean_inc(v_str_954_);
lean_dec(v_x_952_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_964_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v_e_960_; lean_object* v___x_962_; 
v_e_960_ = l_Substring_Raw_takeRightWhileAux(v_str_954_, v_startPos_955_, v_x_953_, v_stopPos_956_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 2, v_e_960_);
v___x_962_ = v___x_958_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_str_954_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_startPos_955_);
lean_ctor_set(v_reuseFailAlloc_963_, 2, v_e_960_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_trimLeft(lean_object* v_s_966_){
_start:
{
lean_object* v_str_967_; lean_object* v_startPos_968_; lean_object* v_stopPos_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_978_; 
v_str_967_ = lean_ctor_get(v_s_966_, 0);
v_startPos_968_ = lean_ctor_get(v_s_966_, 1);
v_stopPos_969_ = lean_ctor_get(v_s_966_, 2);
v_isSharedCheck_978_ = !lean_is_exclusive(v_s_966_);
if (v_isSharedCheck_978_ == 0)
{
v___x_971_ = v_s_966_;
v_isShared_972_ = v_isSharedCheck_978_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_stopPos_969_);
lean_inc(v_startPos_968_);
lean_inc(v_str_967_);
lean_dec(v_s_966_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_978_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; lean_object* v_b_974_; lean_object* v___x_976_; 
v___x_973_ = ((lean_object*)(l_Substring_Raw_trimLeft___closed__0));
v_b_974_ = l_Substring_Raw_takeWhileAux(v_str_967_, v_stopPos_969_, v___x_973_, v_startPos_968_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 1, v_b_974_);
v___x_976_ = v___x_971_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_str_967_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_b_974_);
lean_ctor_set(v_reuseFailAlloc_977_, 2, v_stopPos_969_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_trimRight(lean_object* v_s_979_){
_start:
{
lean_object* v_str_980_; lean_object* v_startPos_981_; lean_object* v_stopPos_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_991_; 
v_str_980_ = lean_ctor_get(v_s_979_, 0);
v_startPos_981_ = lean_ctor_get(v_s_979_, 1);
v_stopPos_982_ = lean_ctor_get(v_s_979_, 2);
v_isSharedCheck_991_ = !lean_is_exclusive(v_s_979_);
if (v_isSharedCheck_991_ == 0)
{
v___x_984_ = v_s_979_;
v_isShared_985_ = v_isSharedCheck_991_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_stopPos_982_);
lean_inc(v_startPos_981_);
lean_inc(v_str_980_);
lean_dec(v_s_979_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_991_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_986_; lean_object* v_e_987_; lean_object* v___x_989_; 
v___x_986_ = ((lean_object*)(l_Substring_Raw_trimLeft___closed__0));
v_e_987_ = l_Substring_Raw_takeRightWhileAux(v_str_980_, v_startPos_981_, v___x_986_, v_stopPos_982_);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 2, v_e_987_);
v___x_989_ = v___x_984_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_str_980_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_startPos_981_);
lean_ctor_set(v_reuseFailAlloc_990_, 2, v_e_987_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_trim(lean_object* v_x_992_){
_start:
{
lean_object* v_str_993_; lean_object* v_startPos_994_; lean_object* v_stopPos_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1005_; 
v_str_993_ = lean_ctor_get(v_x_992_, 0);
v_startPos_994_ = lean_ctor_get(v_x_992_, 1);
v_stopPos_995_ = lean_ctor_get(v_x_992_, 2);
v_isSharedCheck_1005_ = !lean_is_exclusive(v_x_992_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_997_ = v_x_992_;
v_isShared_998_ = v_isSharedCheck_1005_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_stopPos_995_);
lean_inc(v_startPos_994_);
lean_inc(v_str_993_);
lean_dec(v_x_992_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1005_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_999_; lean_object* v_b_1000_; lean_object* v_e_1001_; lean_object* v___x_1003_; 
v___x_999_ = ((lean_object*)(l_Substring_Raw_trimLeft___closed__0));
v_b_1000_ = l_Substring_Raw_takeWhileAux(v_str_993_, v_stopPos_995_, v___x_999_, v_startPos_994_);
v_e_1001_ = l_Substring_Raw_takeRightWhileAux(v_str_993_, v_b_1000_, v___x_999_, v_stopPos_995_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 2, v_e_1001_);
lean_ctor_set(v___x_997_, 1, v_b_1000_);
v___x_1003_ = v___x_997_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_str_993_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v_b_1000_);
lean_ctor_set(v_reuseFailAlloc_1004_, 2, v_e_1001_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___lam__0(lean_object* v___y_1006_, uint8_t v___x_1007_, uint8_t v___x_1008_, lean_object* v_it_1009_, lean_object* v_acc_1010_, lean_object* v_hP_1011_, lean_object* v_recur_1012_){
_start:
{
lean_object* v_str_1013_; lean_object* v_startInclusive_1014_; lean_object* v_endExclusive_1015_; lean_object* v___x_1016_; uint8_t v_decide_1017_; 
v_str_1013_ = lean_ctor_get(v___y_1006_, 0);
v_startInclusive_1014_ = lean_ctor_get(v___y_1006_, 1);
v_endExclusive_1015_ = lean_ctor_get(v___y_1006_, 2);
v___x_1016_ = lean_nat_sub(v_endExclusive_1015_, v_startInclusive_1014_);
v_decide_1017_ = lean_nat_dec_eq(v_it_1009_, v___x_1016_);
lean_dec(v___x_1016_);
if (v_decide_1017_ == 0)
{
lean_object* v_snd_1018_; lean_object* v_snd_1019_; lean_object* v_fst_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1080_; 
v_snd_1018_ = lean_ctor_get(v_acc_1010_, 1);
lean_inc(v_snd_1018_);
v_snd_1019_ = lean_ctor_get(v_snd_1018_, 1);
lean_inc(v_snd_1019_);
v_fst_1020_ = lean_ctor_get(v_acc_1010_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_acc_1010_);
if (v_isSharedCheck_1080_ == 0)
{
lean_object* v_unused_1081_; 
v_unused_1081_ = lean_ctor_get(v_acc_1010_, 1);
lean_dec(v_unused_1081_);
v___x_1022_ = v_acc_1010_;
v_isShared_1023_ = v_isSharedCheck_1080_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_fst_1020_);
lean_dec(v_acc_1010_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1080_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v_fst_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1078_; 
v_fst_1024_ = lean_ctor_get(v_snd_1018_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_snd_1018_);
if (v_isSharedCheck_1078_ == 0)
{
lean_object* v_unused_1079_; 
v_unused_1079_ = lean_ctor_get(v_snd_1018_, 1);
lean_dec(v_unused_1079_);
v___x_1026_ = v_snd_1018_;
v_isShared_1027_ = v_isSharedCheck_1078_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_fst_1024_);
lean_dec(v_snd_1018_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1078_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v_snd_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1076_; 
v_snd_1028_ = lean_ctor_get(v_snd_1019_, 1);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_snd_1019_);
if (v_isSharedCheck_1076_ == 0)
{
lean_object* v_unused_1077_; 
v_unused_1077_ = lean_ctor_get(v_snd_1019_, 0);
lean_dec(v_unused_1077_);
v___x_1030_ = v_snd_1019_;
v_isShared_1031_ = v_isSharedCheck_1076_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_snd_1028_);
lean_dec(v_snd_1019_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1076_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1032_; uint32_t v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; uint8_t v___y_1037_; uint8_t v___y_1038_; uint8_t v___y_1056_; uint8_t v___y_1057_; uint8_t v___y_1062_; uint8_t v___y_1063_; uint8_t v___y_1068_; uint32_t v___x_1072_; uint8_t v___x_1073_; 
v___x_1032_ = lean_nat_add(v_startInclusive_1014_, v_it_1009_);
v___x_1033_ = lean_string_utf8_get_fast(v_str_1013_, v___x_1032_);
v___x_1034_ = lean_string_utf8_next_fast(v_str_1013_, v___x_1032_);
lean_dec(v___x_1032_);
v___x_1035_ = lean_nat_sub(v___x_1034_, v_startInclusive_1014_);
v___x_1072_ = 48;
v___x_1073_ = lean_uint32_dec_le(v___x_1072_, v___x_1033_);
if (v___x_1073_ == 0)
{
v___y_1068_ = v___x_1073_;
goto v___jp_1067_;
}
else
{
uint32_t v___x_1074_; uint8_t v___x_1075_; 
v___x_1074_ = 57;
v___x_1075_ = lean_uint32_dec_le(v___x_1033_, v___x_1074_);
v___y_1068_ = v___x_1075_;
goto v___jp_1067_;
}
v___jp_1036_:
{
uint32_t v___x_1039_; uint8_t v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1044_; 
v___x_1039_ = 95;
v___x_1040_ = lean_uint32_dec_eq(v___x_1033_, v___x_1039_);
v___x_1041_ = lean_box(v___y_1037_);
v___x_1042_ = lean_box(v___y_1038_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 1, v___x_1042_);
lean_ctor_set(v___x_1030_, 0, v___x_1041_);
v___x_1044_ = v___x_1030_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1041_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
lean_object* v___x_1045_; lean_object* v___x_1047_; 
v___x_1045_ = lean_box(v___x_1040_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 1, v___x_1044_);
lean_ctor_set(v___x_1026_, 0, v___x_1045_);
v___x_1047_ = v___x_1026_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v___x_1044_);
v___x_1047_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
lean_object* v___x_1048_; lean_object* v___x_1050_; 
v___x_1048_ = lean_box(v___x_1007_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 1, v___x_1047_);
lean_ctor_set(v___x_1022_, 0, v___x_1048_);
v___x_1050_ = v___x_1022_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1048_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v___x_1047_);
v___x_1050_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1051_; 
v___x_1051_ = lean_apply_4(v_recur_1012_, v___x_1035_, v___x_1050_, lean_box(0), lean_box(0));
return v___x_1051_;
}
}
}
}
v___jp_1055_:
{
uint8_t v___x_1058_; 
v___x_1058_ = lean_unbox(v_fst_1024_);
lean_dec(v_fst_1024_);
if (v___x_1058_ == 0)
{
v___y_1037_ = v___y_1056_;
v___y_1038_ = v___y_1057_;
goto v___jp_1036_;
}
else
{
uint32_t v___x_1059_; uint8_t v___x_1060_; 
v___x_1059_ = 95;
v___x_1060_ = lean_uint32_dec_eq(v___x_1033_, v___x_1059_);
if (v___x_1060_ == 0)
{
v___y_1037_ = v___y_1056_;
v___y_1038_ = v___y_1057_;
goto v___jp_1036_;
}
else
{
v___y_1037_ = v___y_1056_;
v___y_1038_ = v___x_1007_;
goto v___jp_1036_;
}
}
}
v___jp_1061_:
{
uint8_t v___x_1064_; 
v___x_1064_ = lean_unbox(v_fst_1020_);
lean_dec(v_fst_1020_);
if (v___x_1064_ == 0)
{
v___y_1056_ = v___y_1062_;
v___y_1057_ = v___y_1063_;
goto v___jp_1055_;
}
else
{
uint32_t v___x_1065_; uint8_t v___x_1066_; 
v___x_1065_ = 95;
v___x_1066_ = lean_uint32_dec_eq(v___x_1033_, v___x_1065_);
if (v___x_1066_ == 0)
{
v___y_1056_ = v___y_1062_;
v___y_1057_ = v___y_1063_;
goto v___jp_1055_;
}
else
{
lean_dec(v_fst_1024_);
v___y_1037_ = v___y_1062_;
v___y_1038_ = v___x_1007_;
goto v___jp_1036_;
}
}
}
v___jp_1067_:
{
uint8_t v___x_1069_; 
v___x_1069_ = lean_unbox(v_snd_1028_);
lean_dec(v_snd_1028_);
if (v___x_1069_ == 0)
{
lean_dec(v_fst_1024_);
lean_dec(v_fst_1020_);
v___y_1037_ = v___y_1068_;
v___y_1038_ = v___x_1007_;
goto v___jp_1036_;
}
else
{
if (v___y_1068_ == 0)
{
uint32_t v___x_1070_; uint8_t v___x_1071_; 
v___x_1070_ = 95;
v___x_1071_ = lean_uint32_dec_eq(v___x_1033_, v___x_1070_);
if (v___x_1071_ == 0)
{
lean_dec(v_fst_1024_);
lean_dec(v_fst_1020_);
v___y_1037_ = v___y_1068_;
v___y_1038_ = v___x_1007_;
goto v___jp_1036_;
}
else
{
v___y_1062_ = v___y_1068_;
v___y_1063_ = v___x_1071_;
goto v___jp_1061_;
}
}
else
{
v___y_1062_ = v___y_1068_;
v___y_1063_ = v___x_1008_;
goto v___jp_1061_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_recur_1012_);
return v_acc_1010_;
}
}
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
LEAN_EXPORT uint8_t l_Substring_Raw_isNat(lean_object* v_s_1092_){
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
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___boxed(lean_object* v_s_1135_){
_start:
{
uint8_t v_res_1136_; lean_object* v_r_1137_; 
v_res_1136_ = l_Substring_Raw_isNat(v_s_1135_);
v_r_1137_ = lean_box(v_res_1136_);
return v_r_1137_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(lean_object* v___y_1138_, lean_object* v_a_1139_, lean_object* v_b_1140_){
_start:
{
lean_object* v_str_1141_; lean_object* v_startInclusive_1142_; lean_object* v_endExclusive_1143_; lean_object* v___x_1144_; uint8_t v_decide_1145_; 
v_str_1141_ = lean_ctor_get(v___y_1138_, 0);
v_startInclusive_1142_ = lean_ctor_get(v___y_1138_, 1);
v_endExclusive_1143_ = lean_ctor_get(v___y_1138_, 2);
v___x_1144_ = lean_nat_sub(v_endExclusive_1143_, v_startInclusive_1142_);
v_decide_1145_ = lean_nat_dec_eq(v_a_1139_, v___x_1144_);
lean_dec(v___x_1144_);
if (v_decide_1145_ == 0)
{
lean_object* v___x_1146_; uint32_t v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; uint32_t v___x_1150_; uint8_t v___x_1151_; 
v___x_1146_ = lean_nat_add(v_startInclusive_1142_, v_a_1139_);
lean_dec(v_a_1139_);
v___x_1147_ = lean_string_utf8_get_fast(v_str_1141_, v___x_1146_);
v___x_1148_ = lean_string_utf8_next_fast(v_str_1141_, v___x_1146_);
lean_dec(v___x_1146_);
v___x_1149_ = lean_nat_sub(v___x_1148_, v_startInclusive_1142_);
v___x_1150_ = 95;
v___x_1151_ = lean_uint32_dec_eq(v___x_1147_, v___x_1150_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1152_ = lean_unsigned_to_nat(10u);
v___x_1153_ = lean_nat_mul(v_b_1140_, v___x_1152_);
lean_dec(v_b_1140_);
v___x_1154_ = lean_uint32_to_nat(v___x_1147_);
v___x_1155_ = lean_unsigned_to_nat(48u);
v___x_1156_ = lean_nat_sub(v___x_1154_, v___x_1155_);
lean_dec(v___x_1154_);
v___x_1157_ = lean_nat_add(v___x_1153_, v___x_1156_);
lean_dec(v___x_1156_);
lean_dec(v___x_1153_);
v_a_1139_ = v___x_1149_;
v_b_1140_ = v___x_1157_;
goto _start;
}
else
{
v_a_1139_ = v___x_1149_;
goto _start;
}
}
else
{
lean_dec(v_a_1139_);
return v_b_1140_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg___boxed(lean_object* v___y_1160_, lean_object* v_a_1161_, lean_object* v_b_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(v___y_1160_, v_a_1161_, v_b_1162_);
lean_dec_ref(v___y_1160_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(lean_object* v___x_1164_, lean_object* v___y_1165_, lean_object* v_a_1166_, lean_object* v_b_1167_){
_start:
{
lean_object* v_str_1168_; lean_object* v_startInclusive_1169_; lean_object* v_endExclusive_1170_; lean_object* v___x_1171_; uint8_t v_decide_1172_; 
v_str_1168_ = lean_ctor_get(v___y_1165_, 0);
v_startInclusive_1169_ = lean_ctor_get(v___y_1165_, 1);
v_endExclusive_1170_ = lean_ctor_get(v___y_1165_, 2);
v___x_1171_ = lean_nat_sub(v_endExclusive_1170_, v_startInclusive_1169_);
v_decide_1172_ = lean_nat_dec_eq(v_a_1166_, v___x_1171_);
lean_dec(v___x_1171_);
if (v_decide_1172_ == 0)
{
lean_object* v_snd_1173_; lean_object* v_snd_1174_; lean_object* v_fst_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1238_; 
v_snd_1173_ = lean_ctor_get(v_b_1167_, 1);
lean_inc(v_snd_1173_);
v_snd_1174_ = lean_ctor_get(v_snd_1173_, 1);
lean_inc(v_snd_1174_);
v_fst_1175_ = lean_ctor_get(v_b_1167_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v_b_1167_);
if (v_isSharedCheck_1238_ == 0)
{
lean_object* v_unused_1239_; 
v_unused_1239_ = lean_ctor_get(v_b_1167_, 1);
lean_dec(v_unused_1239_);
v___x_1177_ = v_b_1167_;
v_isShared_1178_ = v_isSharedCheck_1238_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_fst_1175_);
lean_dec(v_b_1167_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1238_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v_fst_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1236_; 
v_fst_1179_ = lean_ctor_get(v_snd_1173_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v_snd_1173_);
if (v_isSharedCheck_1236_ == 0)
{
lean_object* v_unused_1237_; 
v_unused_1237_ = lean_ctor_get(v_snd_1173_, 1);
lean_dec(v_unused_1237_);
v___x_1181_ = v_snd_1173_;
v_isShared_1182_ = v_isSharedCheck_1236_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_fst_1179_);
lean_dec(v_snd_1173_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1236_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v_snd_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1234_; 
v_snd_1183_ = lean_ctor_get(v_snd_1174_, 1);
v_isSharedCheck_1234_ = !lean_is_exclusive(v_snd_1174_);
if (v_isSharedCheck_1234_ == 0)
{
lean_object* v_unused_1235_; 
v_unused_1235_ = lean_ctor_get(v_snd_1174_, 0);
lean_dec(v_unused_1235_);
v___x_1185_ = v_snd_1174_;
v_isShared_1186_ = v_isSharedCheck_1234_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_snd_1183_);
lean_dec(v_snd_1174_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1234_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1187_; uint8_t v___x_1188_; uint8_t v___x_1189_; lean_object* v___x_1190_; uint32_t v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; uint8_t v___y_1195_; uint8_t v___y_1196_; uint8_t v___y_1214_; uint8_t v___y_1215_; uint8_t v___y_1220_; uint8_t v___y_1221_; uint8_t v___y_1226_; uint32_t v___x_1230_; uint8_t v___x_1231_; 
v___x_1187_ = lean_unsigned_to_nat(0u);
v___x_1188_ = lean_nat_dec_eq(v___x_1164_, v___x_1187_);
v___x_1189_ = 1;
v___x_1190_ = lean_nat_add(v_startInclusive_1169_, v_a_1166_);
lean_dec(v_a_1166_);
v___x_1191_ = lean_string_utf8_get_fast(v_str_1168_, v___x_1190_);
v___x_1192_ = lean_string_utf8_next_fast(v_str_1168_, v___x_1190_);
lean_dec(v___x_1190_);
v___x_1193_ = lean_nat_sub(v___x_1192_, v_startInclusive_1169_);
v___x_1230_ = 48;
v___x_1231_ = lean_uint32_dec_le(v___x_1230_, v___x_1191_);
if (v___x_1231_ == 0)
{
v___y_1226_ = v___x_1231_;
goto v___jp_1225_;
}
else
{
uint32_t v___x_1232_; uint8_t v___x_1233_; 
v___x_1232_ = 57;
v___x_1233_ = lean_uint32_dec_le(v___x_1191_, v___x_1232_);
v___y_1226_ = v___x_1233_;
goto v___jp_1225_;
}
v___jp_1194_:
{
uint32_t v___x_1197_; uint8_t v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1202_; 
v___x_1197_ = 95;
v___x_1198_ = lean_uint32_dec_eq(v___x_1191_, v___x_1197_);
v___x_1199_ = lean_box(v___y_1195_);
v___x_1200_ = lean_box(v___y_1196_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 1, v___x_1200_);
lean_ctor_set(v___x_1185_, 0, v___x_1199_);
v___x_1202_ = v___x_1185_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1199_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1203_ = lean_box(v___x_1198_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 1, v___x_1202_);
lean_ctor_set(v___x_1181_, 0, v___x_1203_);
v___x_1205_ = v___x_1181_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v___x_1202_);
v___x_1205_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1206_; lean_object* v___x_1208_; 
v___x_1206_ = lean_box(v___x_1188_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 1, v___x_1205_);
lean_ctor_set(v___x_1177_, 0, v___x_1206_);
v___x_1208_ = v___x_1177_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1206_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v___x_1205_);
v___x_1208_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
v_a_1166_ = v___x_1193_;
v_b_1167_ = v___x_1208_;
goto _start;
}
}
}
}
v___jp_1213_:
{
uint8_t v___x_1216_; 
v___x_1216_ = lean_unbox(v_fst_1179_);
lean_dec(v_fst_1179_);
if (v___x_1216_ == 0)
{
v___y_1195_ = v___y_1214_;
v___y_1196_ = v___y_1215_;
goto v___jp_1194_;
}
else
{
uint32_t v___x_1217_; uint8_t v___x_1218_; 
v___x_1217_ = 95;
v___x_1218_ = lean_uint32_dec_eq(v___x_1191_, v___x_1217_);
if (v___x_1218_ == 0)
{
v___y_1195_ = v___y_1214_;
v___y_1196_ = v___y_1215_;
goto v___jp_1194_;
}
else
{
v___y_1195_ = v___y_1214_;
v___y_1196_ = v___x_1188_;
goto v___jp_1194_;
}
}
}
v___jp_1219_:
{
uint8_t v___x_1222_; 
v___x_1222_ = lean_unbox(v_fst_1175_);
lean_dec(v_fst_1175_);
if (v___x_1222_ == 0)
{
v___y_1214_ = v___y_1220_;
v___y_1215_ = v___y_1221_;
goto v___jp_1213_;
}
else
{
uint32_t v___x_1223_; uint8_t v___x_1224_; 
v___x_1223_ = 95;
v___x_1224_ = lean_uint32_dec_eq(v___x_1191_, v___x_1223_);
if (v___x_1224_ == 0)
{
v___y_1214_ = v___y_1220_;
v___y_1215_ = v___y_1221_;
goto v___jp_1213_;
}
else
{
lean_dec(v_fst_1179_);
v___y_1195_ = v___y_1220_;
v___y_1196_ = v___x_1188_;
goto v___jp_1194_;
}
}
}
v___jp_1225_:
{
uint8_t v___x_1227_; 
v___x_1227_ = lean_unbox(v_snd_1183_);
lean_dec(v_snd_1183_);
if (v___x_1227_ == 0)
{
lean_dec(v_fst_1179_);
lean_dec(v_fst_1175_);
v___y_1195_ = v___y_1226_;
v___y_1196_ = v___x_1188_;
goto v___jp_1194_;
}
else
{
if (v___y_1226_ == 0)
{
uint32_t v___x_1228_; uint8_t v___x_1229_; 
v___x_1228_ = 95;
v___x_1229_ = lean_uint32_dec_eq(v___x_1191_, v___x_1228_);
if (v___x_1229_ == 0)
{
lean_dec(v_fst_1179_);
lean_dec(v_fst_1175_);
v___y_1195_ = v___y_1226_;
v___y_1196_ = v___x_1188_;
goto v___jp_1194_;
}
else
{
v___y_1220_ = v___y_1226_;
v___y_1221_ = v___x_1229_;
goto v___jp_1219_;
}
}
else
{
v___y_1220_ = v___y_1226_;
v___y_1221_ = v___x_1189_;
goto v___jp_1219_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1166_);
return v_b_1167_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg___boxed(lean_object* v___x_1240_, lean_object* v___y_1241_, lean_object* v_a_1242_, lean_object* v_b_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(v___x_1240_, v___y_1241_, v_a_1242_, v_b_1243_);
lean_dec_ref(v___y_1241_);
lean_dec(v___x_1240_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toNat_x3f(lean_object* v_s_1245_){
_start:
{
lean_object* v_str_1246_; lean_object* v_startPos_1247_; lean_object* v_stopPos_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1297_; 
v_str_1246_ = lean_ctor_get(v_s_1245_, 0);
v_startPos_1247_ = lean_ctor_get(v_s_1245_, 1);
v_stopPos_1248_ = lean_ctor_get(v_s_1245_, 2);
v_isSharedCheck_1297_ = !lean_is_exclusive(v_s_1245_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1250_ = v_s_1245_;
v_isShared_1251_ = v_isSharedCheck_1297_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_stopPos_1248_);
lean_inc(v_startPos_1247_);
lean_inc(v_str_1246_);
lean_dec(v_s_1245_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1297_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___y_1255_; uint8_t v___y_1259_; uint8_t v___x_1265_; 
v___x_1252_ = lean_nat_sub(v_stopPos_1248_, v_startPos_1247_);
v___x_1253_ = lean_unsigned_to_nat(0u);
v___x_1265_ = lean_nat_dec_eq(v___x_1252_, v___x_1253_);
if (v___x_1265_ == 0)
{
uint8_t v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___y_1275_; uint8_t v___y_1289_; uint8_t v___x_1293_; 
v___x_1266_ = 1;
v___x_1267_ = lean_box(v___x_1265_);
v___x_1268_ = lean_box(v___x_1266_);
v___x_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1267_);
lean_ctor_set(v___x_1269_, 1, v___x_1268_);
v___x_1270_ = lean_box(v___x_1265_);
v___x_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
lean_ctor_set(v___x_1271_, 1, v___x_1269_);
v___x_1272_ = lean_box(v___x_1266_);
v___x_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1272_);
lean_ctor_set(v___x_1273_, 1, v___x_1271_);
v___x_1293_ = lean_string_is_valid_pos(v_str_1246_, v_startPos_1247_);
if (v___x_1293_ == 0)
{
v___y_1289_ = v___x_1293_;
goto v___jp_1288_;
}
else
{
uint8_t v___x_1294_; 
v___x_1294_ = lean_string_is_valid_pos(v_str_1246_, v_stopPos_1248_);
if (v___x_1294_ == 0)
{
v___y_1289_ = v___x_1294_;
goto v___jp_1288_;
}
else
{
uint8_t v___x_1295_; 
v___x_1295_ = lean_nat_dec_le(v_startPos_1247_, v_stopPos_1248_);
v___y_1289_ = v___x_1295_;
goto v___jp_1288_;
}
}
v___jp_1274_:
{
lean_object* v___x_1276_; lean_object* v_snd_1277_; lean_object* v_snd_1278_; lean_object* v_snd_1279_; uint8_t v___x_1280_; 
v___x_1276_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(v___x_1252_, v___y_1275_, v___x_1253_, v___x_1273_);
lean_dec_ref(v___y_1275_);
lean_dec(v___x_1252_);
v_snd_1277_ = lean_ctor_get(v___x_1276_, 1);
lean_inc(v_snd_1277_);
lean_dec_ref(v___x_1276_);
v_snd_1278_ = lean_ctor_get(v_snd_1277_, 1);
lean_inc(v_snd_1278_);
lean_dec(v_snd_1277_);
v_snd_1279_ = lean_ctor_get(v_snd_1278_, 1);
v___x_1280_ = lean_unbox(v_snd_1279_);
if (v___x_1280_ == 0)
{
lean_object* v___x_1281_; 
lean_dec(v_snd_1278_);
lean_del_object(v___x_1250_);
lean_dec(v_stopPos_1248_);
lean_dec(v_startPos_1247_);
lean_dec_ref(v_str_1246_);
v___x_1281_ = lean_box(0);
return v___x_1281_;
}
else
{
lean_object* v_fst_1282_; uint8_t v___x_1283_; 
v_fst_1282_ = lean_ctor_get(v_snd_1278_, 0);
lean_inc(v_fst_1282_);
lean_dec(v_snd_1278_);
v___x_1283_ = lean_unbox(v_fst_1282_);
lean_dec(v_fst_1282_);
if (v___x_1283_ == 0)
{
lean_object* v___x_1284_; 
lean_del_object(v___x_1250_);
lean_dec(v_stopPos_1248_);
lean_dec(v_startPos_1247_);
lean_dec_ref(v_str_1246_);
v___x_1284_ = lean_box(0);
return v___x_1284_;
}
else
{
uint8_t v___x_1285_; 
v___x_1285_ = lean_string_is_valid_pos(v_str_1246_, v_startPos_1247_);
if (v___x_1285_ == 0)
{
v___y_1259_ = v___x_1285_;
goto v___jp_1258_;
}
else
{
uint8_t v___x_1286_; 
v___x_1286_ = lean_string_is_valid_pos(v_str_1246_, v_stopPos_1248_);
if (v___x_1286_ == 0)
{
v___y_1259_ = v___x_1286_;
goto v___jp_1258_;
}
else
{
uint8_t v___x_1287_; 
v___x_1287_ = lean_nat_dec_le(v_startPos_1247_, v_stopPos_1248_);
v___y_1259_ = v___x_1287_;
goto v___jp_1258_;
}
}
}
}
}
v___jp_1288_:
{
if (v___y_1289_ == 0)
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_1291_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_1290_);
v___y_1275_ = v___x_1291_;
goto v___jp_1274_;
}
else
{
lean_object* v___x_1292_; 
lean_inc(v_stopPos_1248_);
lean_inc(v_startPos_1247_);
lean_inc_ref(v_str_1246_);
v___x_1292_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1292_, 0, v_str_1246_);
lean_ctor_set(v___x_1292_, 1, v_startPos_1247_);
lean_ctor_set(v___x_1292_, 2, v_stopPos_1248_);
v___y_1275_ = v___x_1292_;
goto v___jp_1274_;
}
}
}
else
{
lean_object* v___x_1296_; 
lean_dec(v___x_1252_);
lean_del_object(v___x_1250_);
lean_dec(v_stopPos_1248_);
lean_dec(v_startPos_1247_);
lean_dec_ref(v_str_1246_);
v___x_1296_ = lean_box(0);
return v___x_1296_;
}
v___jp_1254_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(v___y_1255_, v___x_1253_, v___x_1253_);
lean_dec_ref(v___y_1255_);
v___x_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
return v___x_1257_;
}
v___jp_1258_:
{
if (v___y_1259_ == 0)
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
lean_del_object(v___x_1250_);
lean_dec(v_stopPos_1248_);
lean_dec(v_startPos_1247_);
lean_dec_ref(v_str_1246_);
v___x_1260_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_1261_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_1260_);
v___y_1255_ = v___x_1261_;
goto v___jp_1254_;
}
else
{
lean_object* v___x_1263_; 
if (v_isShared_1251_ == 0)
{
v___x_1263_ = v___x_1250_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_str_1246_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v_startPos_1247_);
lean_ctor_set(v_reuseFailAlloc_1264_, 2, v_stopPos_1248_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
v___y_1255_ = v___x_1263_;
goto v___jp_1254_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0(lean_object* v___x_1298_, lean_object* v___y_1299_, lean_object* v_inst_1300_, lean_object* v_R_1301_, lean_object* v_a_1302_, lean_object* v_b_1303_, lean_object* v_c_1304_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(v___x_1298_, v___y_1299_, v_a_1302_, v_b_1303_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___boxed(lean_object* v___x_1306_, lean_object* v___y_1307_, lean_object* v_inst_1308_, lean_object* v_R_1309_, lean_object* v_a_1310_, lean_object* v_b_1311_, lean_object* v_c_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0(v___x_1306_, v___y_1307_, v_inst_1308_, v_R_1309_, v_a_1310_, v_b_1311_, v_c_1312_);
lean_dec_ref(v___y_1307_);
lean_dec(v___x_1306_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1(lean_object* v___y_1314_, lean_object* v_inst_1315_, lean_object* v_R_1316_, lean_object* v_a_1317_, lean_object* v_b_1318_, lean_object* v_c_1319_){
_start:
{
lean_object* v___x_1320_; 
v___x_1320_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(v___y_1314_, v_a_1317_, v_b_1318_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___boxed(lean_object* v___y_1321_, lean_object* v_inst_1322_, lean_object* v_R_1323_, lean_object* v_a_1324_, lean_object* v_b_1325_, lean_object* v_c_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1(v___y_1321_, v_inst_1322_, v_R_1323_, v_a_1324_, v_b_1325_, v_c_1326_);
lean_dec_ref(v___y_1321_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_repair(lean_object* v_x_1328_){
_start:
{
lean_object* v_str_1329_; lean_object* v_startPos_1330_; lean_object* v_stopPos_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1347_; 
v_str_1329_ = lean_ctor_get(v_x_1328_, 0);
v_startPos_1330_ = lean_ctor_get(v_x_1328_, 1);
v_stopPos_1331_ = lean_ctor_get(v_x_1328_, 2);
v_isSharedCheck_1347_ = !lean_is_exclusive(v_x_1328_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1333_ = v_x_1328_;
v_isShared_1334_ = v_isSharedCheck_1347_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_stopPos_1331_);
lean_inc(v_startPos_1330_);
lean_inc(v_str_1329_);
lean_dec(v_x_1328_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1347_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___y_1336_; uint8_t v___x_1345_; 
v___x_1345_ = lean_string_is_valid_pos(v_str_1329_, v_startPos_1330_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; 
lean_dec(v_startPos_1330_);
v___x_1346_ = lean_string_utf8_byte_size(v_str_1329_);
v___y_1336_ = v___x_1346_;
goto v___jp_1335_;
}
else
{
v___y_1336_ = v_startPos_1330_;
goto v___jp_1335_;
}
v___jp_1335_:
{
uint8_t v___x_1337_; 
v___x_1337_ = lean_string_is_valid_pos(v_str_1329_, v_stopPos_1331_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; lean_object* v___x_1340_; 
lean_dec(v_stopPos_1331_);
v___x_1338_ = lean_string_utf8_byte_size(v_str_1329_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 2, v___x_1338_);
lean_ctor_set(v___x_1333_, 1, v___y_1336_);
v___x_1340_ = v___x_1333_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_str_1329_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v___y_1336_);
lean_ctor_set(v_reuseFailAlloc_1341_, 2, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
else
{
lean_object* v___x_1343_; 
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 1, v___y_1336_);
v___x_1343_ = v___x_1333_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_str_1329_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v___y_1336_);
lean_ctor_set(v_reuseFailAlloc_1344_, 2, v_stopPos_1331_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_beq(lean_object* v_ss1_1348_, lean_object* v_ss2_1349_){
_start:
{
lean_object* v_ss1_1350_; lean_object* v_str_1351_; lean_object* v_startPos_1352_; lean_object* v_stopPos_1353_; lean_object* v_ss2_1354_; lean_object* v_str_1355_; lean_object* v_startPos_1356_; lean_object* v_stopPos_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; uint8_t v___x_1360_; 
v_ss1_1350_ = l_Substring_Raw_repair(v_ss1_1348_);
v_str_1351_ = lean_ctor_get(v_ss1_1350_, 0);
lean_inc_ref(v_str_1351_);
v_startPos_1352_ = lean_ctor_get(v_ss1_1350_, 1);
lean_inc(v_startPos_1352_);
v_stopPos_1353_ = lean_ctor_get(v_ss1_1350_, 2);
lean_inc(v_stopPos_1353_);
lean_dec_ref(v_ss1_1350_);
v_ss2_1354_ = l_Substring_Raw_repair(v_ss2_1349_);
v_str_1355_ = lean_ctor_get(v_ss2_1354_, 0);
lean_inc_ref(v_str_1355_);
v_startPos_1356_ = lean_ctor_get(v_ss2_1354_, 1);
lean_inc(v_startPos_1356_);
v_stopPos_1357_ = lean_ctor_get(v_ss2_1354_, 2);
lean_inc(v_stopPos_1357_);
lean_dec_ref(v_ss2_1354_);
v___x_1358_ = lean_nat_sub(v_stopPos_1353_, v_startPos_1352_);
lean_dec(v_stopPos_1353_);
v___x_1359_ = lean_nat_sub(v_stopPos_1357_, v_startPos_1356_);
lean_dec(v_stopPos_1357_);
v___x_1360_ = lean_nat_dec_eq(v___x_1358_, v___x_1359_);
lean_dec(v___x_1359_);
if (v___x_1360_ == 0)
{
lean_dec(v___x_1358_);
lean_dec(v_startPos_1356_);
lean_dec_ref(v_str_1355_);
lean_dec(v_startPos_1352_);
lean_dec_ref(v_str_1351_);
return v___x_1360_;
}
else
{
uint8_t v___x_1361_; 
v___x_1361_ = l_String_Pos_Raw_substrEq(v_str_1351_, v_startPos_1352_, v_str_1355_, v_startPos_1356_, v___x_1358_);
lean_dec(v___x_1358_);
lean_dec_ref(v_str_1355_);
lean_dec_ref(v_str_1351_);
return v___x_1361_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_beq___boxed(lean_object* v_ss1_1362_, lean_object* v_ss2_1363_){
_start:
{
uint8_t v_res_1364_; lean_object* v_r_1365_; 
v_res_1364_ = l_Substring_Raw_beq(v_ss1_1362_, v_ss2_1363_);
v_r_1365_ = lean_box(v_res_1364_);
return v_r_1365_;
}
}
LEAN_EXPORT uint8_t lean_substring_beq(lean_object* v_ss1_1366_, lean_object* v_ss2_1367_){
_start:
{
uint8_t v___x_1368_; 
v___x_1368_ = l_Substring_Raw_beq(v_ss1_1366_, v_ss2_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_beqImpl___boxed(lean_object* v_ss1_1369_, lean_object* v_ss2_1370_){
_start:
{
uint8_t v_res_1371_; lean_object* v_r_1372_; 
v_res_1371_ = lean_substring_beq(v_ss1_1369_, v_ss2_1370_);
v_r_1372_ = lean_box(v_res_1371_);
return v_r_1372_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_sameAs(lean_object* v_ss1_1375_, lean_object* v_ss2_1376_){
_start:
{
lean_object* v_startPos_1377_; lean_object* v_startPos_1378_; uint8_t v_decide_1379_; 
v_startPos_1377_ = lean_ctor_get(v_ss1_1375_, 1);
v_startPos_1378_ = lean_ctor_get(v_ss2_1376_, 1);
v_decide_1379_ = lean_nat_dec_eq(v_startPos_1377_, v_startPos_1378_);
if (v_decide_1379_ == 0)
{
lean_dec_ref(v_ss2_1376_);
lean_dec_ref(v_ss1_1375_);
return v_decide_1379_;
}
else
{
uint8_t v___x_1380_; 
v___x_1380_ = l_Substring_Raw_beq(v_ss1_1375_, v_ss2_1376_);
return v___x_1380_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_sameAs___boxed(lean_object* v_ss1_1381_, lean_object* v_ss2_1382_){
_start:
{
uint8_t v_res_1383_; lean_object* v_r_1384_; 
v_res_1383_ = l_Substring_Raw_sameAs(v_ss1_1381_, v_ss2_1382_);
v_r_1384_ = lean_box(v_res_1383_);
return v_r_1384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(lean_object* v_s_1385_, lean_object* v_t_1386_, lean_object* v_spos_1387_, lean_object* v_tpos_1388_){
_start:
{
lean_object* v_str_1389_; lean_object* v_stopPos_1390_; uint8_t v___y_1392_; lean_object* v___x_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; 
v_str_1389_ = lean_ctor_get(v_s_1385_, 0);
v_stopPos_1390_ = lean_ctor_get(v_s_1385_, 2);
v___x_1400_ = lean_unsigned_to_nat(1u);
v___x_1401_ = lean_nat_add(v_spos_1387_, v___x_1400_);
v___x_1402_ = lean_nat_dec_le(v___x_1401_, v_stopPos_1390_);
lean_dec(v___x_1401_);
if (v___x_1402_ == 0)
{
v___y_1392_ = v___x_1402_;
goto v___jp_1391_;
}
else
{
lean_object* v_stopPos_1403_; lean_object* v___x_1404_; uint8_t v___x_1405_; 
v_stopPos_1403_ = lean_ctor_get(v_t_1386_, 2);
v___x_1404_ = lean_nat_add(v_tpos_1388_, v___x_1400_);
v___x_1405_ = lean_nat_dec_le(v___x_1404_, v_stopPos_1403_);
lean_dec(v___x_1404_);
v___y_1392_ = v___x_1405_;
goto v___jp_1391_;
}
v___jp_1391_:
{
if (v___y_1392_ == 0)
{
lean_dec(v_tpos_1388_);
return v_spos_1387_;
}
else
{
lean_object* v_str_1393_; uint32_t v___x_1394_; uint32_t v___x_1395_; uint8_t v___x_1396_; 
v_str_1393_ = lean_ctor_get(v_t_1386_, 0);
v___x_1394_ = lean_string_utf8_get(v_str_1389_, v_spos_1387_);
v___x_1395_ = lean_string_utf8_get(v_str_1393_, v_tpos_1388_);
v___x_1396_ = lean_uint32_dec_eq(v___x_1394_, v___x_1395_);
if (v___x_1396_ == 0)
{
lean_dec(v_tpos_1388_);
return v_spos_1387_;
}
else
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1397_ = lean_string_utf8_next(v_str_1389_, v_spos_1387_);
lean_dec(v_spos_1387_);
v___x_1398_ = lean_string_utf8_next(v_str_1393_, v_tpos_1388_);
lean_dec(v_tpos_1388_);
v_spos_1387_ = v___x_1397_;
v_tpos_1388_ = v___x_1398_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop___boxed(lean_object* v_s_1406_, lean_object* v_t_1407_, lean_object* v_spos_1408_, lean_object* v_tpos_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(v_s_1406_, v_t_1407_, v_spos_1408_, v_tpos_1409_);
lean_dec_ref(v_t_1407_);
lean_dec_ref(v_s_1406_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_commonPrefix(lean_object* v_s_1411_, lean_object* v_t_1412_){
_start:
{
lean_object* v_str_1413_; lean_object* v_startPos_1414_; lean_object* v_startPos_1415_; lean_object* v___x_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
v_str_1413_ = lean_ctor_get(v_s_1411_, 0);
lean_inc_ref(v_str_1413_);
v_startPos_1414_ = lean_ctor_get(v_s_1411_, 1);
lean_inc_n(v_startPos_1414_, 2);
v_startPos_1415_ = lean_ctor_get(v_t_1412_, 1);
lean_inc(v_startPos_1415_);
v___x_1416_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(v_s_1411_, v_t_1412_, v_startPos_1414_, v_startPos_1415_);
lean_dec_ref(v_s_1411_);
v_isSharedCheck_1423_ = !lean_is_exclusive(v_t_1412_);
if (v_isSharedCheck_1423_ == 0)
{
lean_object* v_unused_1424_; lean_object* v_unused_1425_; lean_object* v_unused_1426_; 
v_unused_1424_ = lean_ctor_get(v_t_1412_, 2);
lean_dec(v_unused_1424_);
v_unused_1425_ = lean_ctor_get(v_t_1412_, 1);
lean_dec(v_unused_1425_);
v_unused_1426_ = lean_ctor_get(v_t_1412_, 0);
lean_dec(v_unused_1426_);
v___x_1418_ = v_t_1412_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_dec(v_t_1412_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 2, v___x_1416_);
lean_ctor_set(v___x_1418_, 1, v_startPos_1414_);
lean_ctor_set(v___x_1418_, 0, v_str_1413_);
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_str_1413_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_startPos_1414_);
lean_ctor_set(v_reuseFailAlloc_1422_, 2, v___x_1416_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(lean_object* v_s_1427_, lean_object* v_t_1428_, lean_object* v_spos_1429_, lean_object* v_tpos_1430_){
_start:
{
lean_object* v_str_1431_; lean_object* v_startPos_1432_; uint8_t v___y_1434_; lean_object* v___x_1442_; lean_object* v___x_1443_; uint8_t v___x_1444_; 
v_str_1431_ = lean_ctor_get(v_s_1427_, 0);
v_startPos_1432_ = lean_ctor_get(v_s_1427_, 1);
v___x_1442_ = lean_unsigned_to_nat(1u);
v___x_1443_ = lean_nat_add(v_startPos_1432_, v___x_1442_);
v___x_1444_ = lean_nat_dec_le(v___x_1443_, v_spos_1429_);
lean_dec(v___x_1443_);
if (v___x_1444_ == 0)
{
v___y_1434_ = v___x_1444_;
goto v___jp_1433_;
}
else
{
lean_object* v_startPos_1445_; lean_object* v___x_1446_; uint8_t v___x_1447_; 
v_startPos_1445_ = lean_ctor_get(v_t_1428_, 1);
v___x_1446_ = lean_nat_add(v_startPos_1445_, v___x_1442_);
v___x_1447_ = lean_nat_dec_le(v___x_1446_, v_tpos_1430_);
lean_dec(v___x_1446_);
v___y_1434_ = v___x_1447_;
goto v___jp_1433_;
}
v___jp_1433_:
{
if (v___y_1434_ == 0)
{
lean_dec(v_tpos_1430_);
return v_spos_1429_;
}
else
{
lean_object* v_str_1435_; lean_object* v_spos_x27_1436_; lean_object* v_tpos_x27_1437_; uint32_t v___x_1438_; uint32_t v___x_1439_; uint8_t v___x_1440_; 
v_str_1435_ = lean_ctor_get(v_t_1428_, 0);
v_spos_x27_1436_ = lean_string_utf8_prev(v_str_1431_, v_spos_1429_);
v_tpos_x27_1437_ = lean_string_utf8_prev(v_str_1435_, v_tpos_1430_);
lean_dec(v_tpos_1430_);
v___x_1438_ = lean_string_utf8_get(v_str_1431_, v_spos_x27_1436_);
v___x_1439_ = lean_string_utf8_get(v_str_1435_, v_tpos_x27_1437_);
v___x_1440_ = lean_uint32_dec_eq(v___x_1438_, v___x_1439_);
if (v___x_1440_ == 0)
{
lean_dec(v_tpos_x27_1437_);
lean_dec(v_spos_x27_1436_);
return v_spos_1429_;
}
else
{
lean_dec(v_spos_1429_);
v_spos_1429_ = v_spos_x27_1436_;
v_tpos_1430_ = v_tpos_x27_1437_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop___boxed(lean_object* v_s_1448_, lean_object* v_t_1449_, lean_object* v_spos_1450_, lean_object* v_tpos_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(v_s_1448_, v_t_1449_, v_spos_1450_, v_tpos_1451_);
lean_dec_ref(v_t_1449_);
lean_dec_ref(v_s_1448_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_commonSuffix(lean_object* v_s_1453_, lean_object* v_t_1454_){
_start:
{
lean_object* v_str_1455_; lean_object* v_stopPos_1456_; lean_object* v_stopPos_1457_; lean_object* v___x_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
v_str_1455_ = lean_ctor_get(v_s_1453_, 0);
lean_inc_ref(v_str_1455_);
v_stopPos_1456_ = lean_ctor_get(v_s_1453_, 2);
lean_inc_n(v_stopPos_1456_, 2);
v_stopPos_1457_ = lean_ctor_get(v_t_1454_, 2);
lean_inc(v_stopPos_1457_);
v___x_1458_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(v_s_1453_, v_t_1454_, v_stopPos_1456_, v_stopPos_1457_);
lean_dec_ref(v_s_1453_);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_t_1454_);
if (v_isSharedCheck_1465_ == 0)
{
lean_object* v_unused_1466_; lean_object* v_unused_1467_; lean_object* v_unused_1468_; 
v_unused_1466_ = lean_ctor_get(v_t_1454_, 2);
lean_dec(v_unused_1466_);
v_unused_1467_ = lean_ctor_get(v_t_1454_, 1);
lean_dec(v_unused_1467_);
v_unused_1468_ = lean_ctor_get(v_t_1454_, 0);
lean_dec(v_unused_1468_);
v___x_1460_ = v_t_1454_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_dec(v_t_1454_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 2, v_stopPos_1456_);
lean_ctor_set(v___x_1460_, 1, v___x_1458_);
lean_ctor_set(v___x_1460_, 0, v_str_1455_);
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_str_1455_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v___x_1458_);
lean_ctor_set(v_reuseFailAlloc_1464_, 2, v_stopPos_1456_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropPrefix_x3f(lean_object* v_s_1469_, lean_object* v_pre_1470_){
_start:
{
lean_object* v_t_1471_; lean_object* v_startPos_1472_; lean_object* v_stopPos_1473_; lean_object* v_startPos_1474_; lean_object* v_stopPos_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; uint8_t v___x_1478_; 
lean_inc_ref(v_pre_1470_);
lean_inc_ref(v_s_1469_);
v_t_1471_ = l_Substring_Raw_commonPrefix(v_s_1469_, v_pre_1470_);
v_startPos_1472_ = lean_ctor_get(v_t_1471_, 1);
lean_inc(v_startPos_1472_);
v_stopPos_1473_ = lean_ctor_get(v_t_1471_, 2);
lean_inc(v_stopPos_1473_);
lean_dec_ref(v_t_1471_);
v_startPos_1474_ = lean_ctor_get(v_pre_1470_, 1);
lean_inc(v_startPos_1474_);
v_stopPos_1475_ = lean_ctor_get(v_pre_1470_, 2);
lean_inc(v_stopPos_1475_);
lean_dec_ref(v_pre_1470_);
v___x_1476_ = lean_nat_sub(v_stopPos_1473_, v_startPos_1472_);
lean_dec(v_startPos_1472_);
v___x_1477_ = lean_nat_sub(v_stopPos_1475_, v_startPos_1474_);
lean_dec(v_startPos_1474_);
lean_dec(v_stopPos_1475_);
v___x_1478_ = lean_nat_dec_eq(v___x_1476_, v___x_1477_);
lean_dec(v___x_1477_);
lean_dec(v___x_1476_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1479_; 
lean_dec(v_stopPos_1473_);
lean_dec_ref(v_s_1469_);
v___x_1479_ = lean_box(0);
return v___x_1479_;
}
else
{
lean_object* v_str_1480_; lean_object* v_stopPos_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1489_; 
v_str_1480_ = lean_ctor_get(v_s_1469_, 0);
v_stopPos_1481_ = lean_ctor_get(v_s_1469_, 2);
v_isSharedCheck_1489_ = !lean_is_exclusive(v_s_1469_);
if (v_isSharedCheck_1489_ == 0)
{
lean_object* v_unused_1490_; 
v_unused_1490_ = lean_ctor_get(v_s_1469_, 1);
lean_dec(v_unused_1490_);
v___x_1483_ = v_s_1469_;
v_isShared_1484_ = v_isSharedCheck_1489_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_stopPos_1481_);
lean_inc(v_str_1480_);
lean_dec(v_s_1469_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1489_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 1, v_stopPos_1473_);
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_str_1480_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_stopPos_1473_);
lean_ctor_set(v_reuseFailAlloc_1488_, 2, v_stopPos_1481_);
v___x_1486_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
lean_object* v___x_1487_; 
v___x_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1486_);
return v___x_1487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropSuffix_x3f(lean_object* v_s_1491_, lean_object* v_suff_1492_){
_start:
{
lean_object* v_t_1493_; lean_object* v_startPos_1494_; lean_object* v_stopPos_1495_; lean_object* v_startPos_1496_; lean_object* v_stopPos_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; uint8_t v___x_1500_; 
lean_inc_ref(v_suff_1492_);
lean_inc_ref(v_s_1491_);
v_t_1493_ = l_Substring_Raw_commonSuffix(v_s_1491_, v_suff_1492_);
v_startPos_1494_ = lean_ctor_get(v_t_1493_, 1);
lean_inc(v_startPos_1494_);
v_stopPos_1495_ = lean_ctor_get(v_t_1493_, 2);
lean_inc(v_stopPos_1495_);
lean_dec_ref(v_t_1493_);
v_startPos_1496_ = lean_ctor_get(v_suff_1492_, 1);
lean_inc(v_startPos_1496_);
v_stopPos_1497_ = lean_ctor_get(v_suff_1492_, 2);
lean_inc(v_stopPos_1497_);
lean_dec_ref(v_suff_1492_);
v___x_1498_ = lean_nat_sub(v_stopPos_1495_, v_startPos_1494_);
lean_dec(v_stopPos_1495_);
v___x_1499_ = lean_nat_sub(v_stopPos_1497_, v_startPos_1496_);
lean_dec(v_startPos_1496_);
lean_dec(v_stopPos_1497_);
v___x_1500_ = lean_nat_dec_eq(v___x_1498_, v___x_1499_);
lean_dec(v___x_1499_);
lean_dec(v___x_1498_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; 
lean_dec(v_startPos_1494_);
lean_dec_ref(v_s_1491_);
v___x_1501_ = lean_box(0);
return v___x_1501_;
}
else
{
lean_object* v_str_1502_; lean_object* v_startPos_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1511_; 
v_str_1502_ = lean_ctor_get(v_s_1491_, 0);
v_startPos_1503_ = lean_ctor_get(v_s_1491_, 1);
v_isSharedCheck_1511_ = !lean_is_exclusive(v_s_1491_);
if (v_isSharedCheck_1511_ == 0)
{
lean_object* v_unused_1512_; 
v_unused_1512_ = lean_ctor_get(v_s_1491_, 2);
lean_dec(v_unused_1512_);
v___x_1505_ = v_s_1491_;
v_isShared_1506_ = v_isSharedCheck_1511_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_startPos_1503_);
lean_inc(v_str_1502_);
lean_dec(v_s_1491_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1511_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 2, v_startPos_1494_);
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_str_1502_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_startPos_1503_);
lean_ctor_set(v_reuseFailAlloc_1510_, 2, v_startPos_1494_);
v___x_1508_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
lean_object* v___x_1509_; 
v___x_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
return v___x_1509_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg(lean_object* v_x_1513_, lean_object* v_x_1514_, lean_object* v_x_1515_, lean_object* v_h__1_1516_, lean_object* v_h__2_1517_){
_start:
{
lean_object* v_zero_1518_; uint8_t v_isZero_1519_; 
v_zero_1518_ = lean_unsigned_to_nat(0u);
v_isZero_1519_ = lean_nat_dec_eq(v_x_1514_, v_zero_1518_);
if (v_isZero_1519_ == 1)
{
lean_object* v___x_1520_; 
lean_dec(v_h__2_1517_);
v___x_1520_ = lean_apply_2(v_h__1_1516_, v_x_1513_, v_x_1515_);
return v___x_1520_;
}
else
{
lean_object* v_one_1521_; lean_object* v_n_1522_; lean_object* v___x_1523_; 
lean_dec(v_h__1_1516_);
v_one_1521_ = lean_unsigned_to_nat(1u);
v_n_1522_ = lean_nat_sub(v_x_1514_, v_one_1521_);
v___x_1523_ = lean_apply_3(v_h__2_1517_, v_x_1513_, v_n_1522_, v_x_1515_);
return v___x_1523_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg___boxed(lean_object* v_x_1524_, lean_object* v_x_1525_, lean_object* v_x_1526_, lean_object* v_h__1_1527_, lean_object* v_h__2_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg(v_x_1524_, v_x_1525_, v_x_1526_, v_h__1_1527_, v_h__2_1528_);
lean_dec(v_x_1525_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter(lean_object* v_motive_1530_, lean_object* v_x_1531_, lean_object* v_x_1532_, lean_object* v_x_1533_, lean_object* v_h__1_1534_, lean_object* v_h__2_1535_){
_start:
{
lean_object* v_zero_1536_; uint8_t v_isZero_1537_; 
v_zero_1536_ = lean_unsigned_to_nat(0u);
v_isZero_1537_ = lean_nat_dec_eq(v_x_1532_, v_zero_1536_);
if (v_isZero_1537_ == 1)
{
lean_object* v___x_1538_; 
lean_dec(v_h__2_1535_);
v___x_1538_ = lean_apply_2(v_h__1_1534_, v_x_1531_, v_x_1533_);
return v___x_1538_;
}
else
{
lean_object* v_one_1539_; lean_object* v_n_1540_; lean_object* v___x_1541_; 
lean_dec(v_h__1_1534_);
v_one_1539_ = lean_unsigned_to_nat(1u);
v_n_1540_ = lean_nat_sub(v_x_1532_, v_one_1539_);
v___x_1541_ = lean_apply_3(v_h__2_1535_, v_x_1531_, v_n_1540_, v_x_1533_);
return v___x_1541_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___boxed(lean_object* v_motive_1542_, lean_object* v_x_1543_, lean_object* v_x_1544_, lean_object* v_x_1545_, lean_object* v_h__1_1546_, lean_object* v_h__2_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter(v_motive_1542_, v_x_1543_, v_x_1544_, v_x_1545_, v_h__1_1546_, v_h__2_1547_);
lean_dec(v_x_1544_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l_Substring_bsize(lean_object* v_a_1549_){
_start:
{
lean_object* v_startPos_1550_; lean_object* v_stopPos_1551_; lean_object* v___x_1552_; 
v_startPos_1550_ = lean_ctor_get(v_a_1549_, 1);
v_stopPos_1551_ = lean_ctor_get(v_a_1549_, 2);
v___x_1552_ = lean_nat_sub(v_stopPos_1551_, v_startPos_1550_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Substring_bsize___boxed(lean_object* v_a_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Substring_bsize(v_a_1553_);
lean_dec_ref(v_a_1553_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Substring_toString(lean_object* v_a_1555_){
_start:
{
lean_object* v_str_1556_; lean_object* v_startPos_1557_; lean_object* v_stopPos_1558_; lean_object* v___x_1559_; 
v_str_1556_ = lean_ctor_get(v_a_1555_, 0);
v_startPos_1557_ = lean_ctor_get(v_a_1555_, 1);
v_stopPos_1558_ = lean_ctor_get(v_a_1555_, 2);
v___x_1559_ = lean_string_utf8_extract(v_str_1556_, v_startPos_1557_, v_stopPos_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Substring_toString___boxed(lean_object* v_a_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_Substring_toString(v_a_1560_);
lean_dec_ref(v_a_1560_);
return v_res_1561_;
}
}
LEAN_EXPORT uint8_t l_Substring_isEmpty(lean_object* v_ss_1562_){
_start:
{
lean_object* v_startPos_1563_; lean_object* v_stopPos_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; uint8_t v___x_1567_; 
v_startPos_1563_ = lean_ctor_get(v_ss_1562_, 1);
v_stopPos_1564_ = lean_ctor_get(v_ss_1562_, 2);
v___x_1565_ = lean_nat_sub(v_stopPos_1564_, v_startPos_1563_);
v___x_1566_ = lean_unsigned_to_nat(0u);
v___x_1567_ = lean_nat_dec_eq(v___x_1565_, v___x_1566_);
lean_dec(v___x_1565_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Substring_isEmpty___boxed(lean_object* v_ss_1568_){
_start:
{
uint8_t v_res_1569_; lean_object* v_r_1570_; 
v_res_1569_ = l_Substring_isEmpty(v_ss_1568_);
lean_dec_ref(v_ss_1568_);
v_r_1570_ = lean_box(v_res_1569_);
return v_r_1570_;
}
}
LEAN_EXPORT lean_object* l_Substring_next(lean_object* v_a_1571_, lean_object* v_a_1572_){
_start:
{
lean_object* v_str_1573_; lean_object* v_startPos_1574_; lean_object* v_stopPos_1575_; lean_object* v_absP_1576_; uint8_t v_decide_1577_; 
v_str_1573_ = lean_ctor_get(v_a_1571_, 0);
v_startPos_1574_ = lean_ctor_get(v_a_1571_, 1);
v_stopPos_1575_ = lean_ctor_get(v_a_1571_, 2);
v_absP_1576_ = lean_nat_add(v_startPos_1574_, v_a_1572_);
v_decide_1577_ = lean_nat_dec_eq(v_absP_1576_, v_stopPos_1575_);
if (v_decide_1577_ == 0)
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1578_ = lean_string_utf8_next(v_str_1573_, v_absP_1576_);
lean_dec(v_absP_1576_);
v___x_1579_ = lean_nat_sub(v___x_1578_, v_startPos_1574_);
lean_dec(v___x_1578_);
return v___x_1579_;
}
else
{
lean_dec(v_absP_1576_);
lean_inc(v_a_1572_);
return v_a_1572_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_next___boxed(lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Substring_next(v_a_1580_, v_a_1581_);
lean_dec(v_a_1581_);
lean_dec_ref(v_a_1580_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Substring_prev(lean_object* v_a_1583_, lean_object* v_a_1584_){
_start:
{
lean_object* v_str_1585_; lean_object* v_startPos_1586_; lean_object* v_absP_1587_; uint8_t v_decide_1588_; 
v_str_1585_ = lean_ctor_get(v_a_1583_, 0);
v_startPos_1586_ = lean_ctor_get(v_a_1583_, 1);
v_absP_1587_ = lean_nat_add(v_startPos_1586_, v_a_1584_);
v_decide_1588_ = lean_nat_dec_eq(v_absP_1587_, v_startPos_1586_);
if (v_decide_1588_ == 0)
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1589_ = lean_string_utf8_prev(v_str_1585_, v_absP_1587_);
lean_dec(v_absP_1587_);
v___x_1590_ = lean_nat_sub(v___x_1589_, v_startPos_1586_);
lean_dec(v___x_1589_);
return v___x_1590_;
}
else
{
lean_dec(v_absP_1587_);
lean_inc(v_a_1584_);
return v_a_1584_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_prev___boxed(lean_object* v_a_1591_, lean_object* v_a_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Substring_prev(v_a_1591_, v_a_1592_);
lean_dec(v_a_1592_);
lean_dec_ref(v_a_1591_);
return v_res_1593_;
}
}
LEAN_EXPORT uint8_t l_Substring_atEnd(lean_object* v_a_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v_startPos_1596_; lean_object* v_stopPos_1597_; lean_object* v___x_1598_; uint8_t v_decide_1599_; 
v_startPos_1596_ = lean_ctor_get(v_a_1594_, 1);
v_stopPos_1597_ = lean_ctor_get(v_a_1594_, 2);
v___x_1598_ = lean_nat_add(v_startPos_1596_, v_a_1595_);
v_decide_1599_ = lean_nat_dec_eq(v___x_1598_, v_stopPos_1597_);
lean_dec(v___x_1598_);
return v_decide_1599_;
}
}
LEAN_EXPORT lean_object* l_Substring_atEnd___boxed(lean_object* v_a_1600_, lean_object* v_a_1601_){
_start:
{
uint8_t v_res_1602_; lean_object* v_r_1603_; 
v_res_1602_ = l_Substring_atEnd(v_a_1600_, v_a_1601_);
lean_dec(v_a_1601_);
lean_dec_ref(v_a_1600_);
v_r_1603_ = lean_box(v_res_1602_);
return v_r_1603_;
}
}
LEAN_EXPORT uint8_t l_Substring_beq(lean_object* v_ss1_1604_, lean_object* v_ss2_1605_){
_start:
{
uint8_t v___x_1606_; 
v___x_1606_ = l_Substring_Raw_beq(v_ss1_1604_, v_ss2_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Substring_beq___boxed(lean_object* v_ss1_1607_, lean_object* v_ss2_1608_){
_start:
{
uint8_t v_res_1609_; lean_object* v_r_1610_; 
v_res_1609_ = l_Substring_beq(v_ss1_1607_, v_ss2_1608_);
v_r_1610_ = lean_box(v_res_1609_);
return v_r_1610_;
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

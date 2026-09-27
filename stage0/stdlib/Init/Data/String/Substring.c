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
uint8_t l_String_instDecidableLtRaw(lean_object*, lean_object*);
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
lean_object* v_str_13_; lean_object* v_startPos_14_; lean_object* v_stopPos_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_31_; 
v_str_13_ = lean_ctor_get(v_s_12_, 0);
v_startPos_14_ = lean_ctor_get(v_s_12_, 1);
v_stopPos_15_ = lean_ctor_get(v_s_12_, 2);
v_isSharedCheck_31_ = !lean_is_exclusive(v_s_12_);
if (v_isSharedCheck_31_ == 0)
{
v___x_17_ = v_s_12_;
v_isShared_18_ = v_isSharedCheck_31_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_stopPos_15_);
lean_inc(v_startPos_14_);
lean_inc(v_str_13_);
lean_dec(v_s_12_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_31_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
uint8_t v___y_20_; uint8_t v___x_26_; uint8_t v___y_28_; uint8_t v___x_29_; 
v___x_26_ = lean_string_is_valid_pos(v_str_13_, v_startPos_14_);
v___x_29_ = lean_string_is_valid_pos(v_str_13_, v_stopPos_15_);
if (v___x_29_ == 0)
{
v___y_28_ = v___x_29_;
goto v___jp_27_;
}
else
{
uint8_t v___x_30_; 
v___x_30_ = lean_nat_dec_le(v_startPos_14_, v_stopPos_15_);
v___y_28_ = v___x_30_;
goto v___jp_27_;
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
v___jp_27_:
{
if (v___x_26_ == 0)
{
v___y_20_ = v___x_26_;
goto v___jp_19_;
}
else
{
v___y_20_ = v___y_28_;
goto v___jp_19_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_isEmpty(lean_object* v_ss_32_){
_start:
{
lean_object* v_startPos_33_; lean_object* v_stopPos_34_; lean_object* v___x_35_; lean_object* v___x_36_; uint8_t v___x_37_; 
v_startPos_33_ = lean_ctor_get(v_ss_32_, 1);
v_stopPos_34_ = lean_ctor_get(v_ss_32_, 2);
v___x_35_ = lean_nat_sub(v_stopPos_34_, v_startPos_33_);
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = lean_nat_dec_eq(v___x_35_, v___x_36_);
lean_dec(v___x_35_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_isEmpty___boxed(lean_object* v_ss_38_){
_start:
{
uint8_t v_res_39_; lean_object* v_r_40_; 
v_res_39_ = l_Substring_Raw_isEmpty(v_ss_38_);
lean_dec_ref(v_ss_38_);
v_r_40_ = lean_box(v_res_39_);
return v_r_40_;
}
}
LEAN_EXPORT uint8_t lean_substring_isempty(lean_object* v_ss_41_){
_start:
{
lean_object* v_startPos_42_; lean_object* v_stopPos_43_; lean_object* v___x_44_; lean_object* v___x_45_; uint8_t v___x_46_; 
v_startPos_42_ = lean_ctor_get(v_ss_41_, 1);
lean_inc(v_startPos_42_);
v_stopPos_43_ = lean_ctor_get(v_ss_41_, 2);
lean_inc(v_stopPos_43_);
lean_dec_ref(v_ss_41_);
v___x_44_ = lean_nat_sub(v_stopPos_43_, v_startPos_42_);
lean_dec(v_startPos_42_);
lean_dec(v_stopPos_43_);
v___x_45_ = lean_unsigned_to_nat(0u);
v___x_46_ = lean_nat_dec_eq(v___x_44_, v___x_45_);
lean_dec(v___x_44_);
return v___x_46_;
}
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
LEAN_EXPORT uint32_t l_Substring_Raw_get(lean_object* v_x_62_, lean_object* v_x_63_){
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
LEAN_EXPORT lean_object* l_Substring_Raw_get___boxed(lean_object* v_x_68_, lean_object* v_x_69_){
_start:
{
uint32_t v_res_70_; lean_object* v_r_71_; 
v_res_70_ = l_Substring_Raw_get(v_x_68_, v_x_69_);
lean_dec(v_x_69_);
lean_dec_ref(v_x_68_);
v_r_71_ = lean_box_uint32(v_res_70_);
return v_r_71_;
}
}
LEAN_EXPORT uint32_t lean_substring_get(lean_object* v_a_72_, lean_object* v_a_73_){
_start:
{
lean_object* v_str_74_; lean_object* v_startPos_75_; lean_object* v___x_76_; uint32_t v___x_77_; 
v_str_74_ = lean_ctor_get(v_a_72_, 0);
lean_inc_ref(v_str_74_);
v_startPos_75_ = lean_ctor_get(v_a_72_, 1);
lean_inc(v_startPos_75_);
lean_dec_ref(v_a_72_);
v___x_76_ = lean_nat_add(v_startPos_75_, v_a_73_);
lean_dec(v_a_73_);
lean_dec(v_startPos_75_);
v___x_77_ = lean_string_utf8_get(v_str_74_, v___x_76_);
lean_dec(v___x_76_);
lean_dec_ref(v_str_74_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_getImpl___boxed(lean_object* v_a_78_, lean_object* v_a_79_){
_start:
{
uint32_t v_res_80_; lean_object* v_r_81_; 
v_res_80_ = lean_substring_get(v_a_78_, v_a_79_);
v_r_81_ = lean_box_uint32(v_res_80_);
return v_r_81_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_next(lean_object* v_x_82_, lean_object* v_x_83_){
_start:
{
lean_object* v_str_84_; lean_object* v_startPos_85_; lean_object* v_stopPos_86_; lean_object* v_absP_87_; uint8_t v_decide_88_; 
v_str_84_ = lean_ctor_get(v_x_82_, 0);
v_startPos_85_ = lean_ctor_get(v_x_82_, 1);
v_stopPos_86_ = lean_ctor_get(v_x_82_, 2);
v_absP_87_ = lean_nat_add(v_startPos_85_, v_x_83_);
v_decide_88_ = lean_nat_dec_eq(v_absP_87_, v_stopPos_86_);
if (v_decide_88_ == 0)
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_string_utf8_next(v_str_84_, v_absP_87_);
lean_dec(v_absP_87_);
v___x_90_ = lean_nat_sub(v___x_89_, v_startPos_85_);
lean_dec(v___x_89_);
return v___x_90_;
}
else
{
lean_dec(v_absP_87_);
lean_inc(v_x_83_);
return v_x_83_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_next___boxed(lean_object* v_x_91_, lean_object* v_x_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Substring_Raw_next(v_x_91_, v_x_92_);
lean_dec(v_x_92_);
lean_dec_ref(v_x_91_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_get_match__1_splitter___redArg(lean_object* v_x_94_, lean_object* v_x_95_, lean_object* v_h__1_96_){
_start:
{
lean_object* v_str_97_; lean_object* v_startPos_98_; lean_object* v_stopPos_99_; lean_object* v___x_100_; 
v_str_97_ = lean_ctor_get(v_x_94_, 0);
lean_inc_ref(v_str_97_);
v_startPos_98_ = lean_ctor_get(v_x_94_, 1);
lean_inc(v_startPos_98_);
v_stopPos_99_ = lean_ctor_get(v_x_94_, 2);
lean_inc(v_stopPos_99_);
lean_dec_ref(v_x_94_);
v___x_100_ = lean_apply_4(v_h__1_96_, v_str_97_, v_startPos_98_, v_stopPos_99_, v_x_95_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_get_match__1_splitter(lean_object* v_motive_101_, lean_object* v_x_102_, lean_object* v_x_103_, lean_object* v_h__1_104_){
_start:
{
lean_object* v_str_105_; lean_object* v_startPos_106_; lean_object* v_stopPos_107_; lean_object* v___x_108_; 
v_str_105_ = lean_ctor_get(v_x_102_, 0);
lean_inc_ref(v_str_105_);
v_startPos_106_ = lean_ctor_get(v_x_102_, 1);
lean_inc(v_startPos_106_);
v_stopPos_107_ = lean_ctor_get(v_x_102_, 2);
lean_inc(v_stopPos_107_);
lean_dec_ref(v_x_102_);
v___x_108_ = lean_apply_4(v_h__1_104_, v_str_105_, v_startPos_106_, v_stopPos_107_, v_x_103_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_prev(lean_object* v_x_109_, lean_object* v_x_110_){
_start:
{
lean_object* v_str_111_; lean_object* v_startPos_112_; lean_object* v_absP_113_; uint8_t v_decide_114_; 
v_str_111_ = lean_ctor_get(v_x_109_, 0);
v_startPos_112_ = lean_ctor_get(v_x_109_, 1);
v_absP_113_ = lean_nat_add(v_startPos_112_, v_x_110_);
v_decide_114_ = lean_nat_dec_eq(v_absP_113_, v_startPos_112_);
if (v_decide_114_ == 0)
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_string_utf8_prev(v_str_111_, v_absP_113_);
lean_dec(v_absP_113_);
v___x_116_ = lean_nat_sub(v___x_115_, v_startPos_112_);
lean_dec(v___x_115_);
return v___x_116_;
}
else
{
lean_dec(v_absP_113_);
lean_inc(v_x_110_);
return v_x_110_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_prev___boxed(lean_object* v_x_117_, lean_object* v_x_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Substring_Raw_prev(v_x_117_, v_x_118_);
lean_dec(v_x_118_);
lean_dec_ref(v_x_117_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* lean_substring_prev(lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v_str_122_; lean_object* v_startPos_123_; lean_object* v_absP_124_; uint8_t v_decide_125_; 
v_str_122_ = lean_ctor_get(v_a_120_, 0);
lean_inc_ref(v_str_122_);
v_startPos_123_ = lean_ctor_get(v_a_120_, 1);
lean_inc(v_startPos_123_);
lean_dec_ref(v_a_120_);
v_absP_124_ = lean_nat_add(v_startPos_123_, v_a_121_);
v_decide_125_ = lean_nat_dec_eq(v_absP_124_, v_startPos_123_);
if (v_decide_125_ == 0)
{
lean_object* v___x_126_; lean_object* v___x_127_; 
lean_dec(v_a_121_);
v___x_126_ = lean_string_utf8_prev(v_str_122_, v_absP_124_);
lean_dec(v_absP_124_);
lean_dec_ref(v_str_122_);
v___x_127_ = lean_nat_sub(v___x_126_, v_startPos_123_);
lean_dec(v_startPos_123_);
lean_dec(v___x_126_);
return v___x_127_;
}
else
{
lean_dec(v_absP_124_);
lean_dec(v_startPos_123_);
lean_dec_ref(v_str_122_);
return v_a_121_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_nextn(lean_object* v_x_128_, lean_object* v_x_129_, lean_object* v_x_130_){
_start:
{
lean_object* v_zero_131_; uint8_t v_isZero_132_; 
v_zero_131_ = lean_unsigned_to_nat(0u);
v_isZero_132_ = lean_nat_dec_eq(v_x_129_, v_zero_131_);
if (v_isZero_132_ == 1)
{
lean_dec(v_x_129_);
return v_x_130_;
}
else
{
lean_object* v_str_133_; lean_object* v_startPos_134_; lean_object* v_stopPos_135_; lean_object* v_one_136_; lean_object* v_n_137_; lean_object* v_absP_138_; uint8_t v_decide_139_; 
v_str_133_ = lean_ctor_get(v_x_128_, 0);
v_startPos_134_ = lean_ctor_get(v_x_128_, 1);
v_stopPos_135_ = lean_ctor_get(v_x_128_, 2);
v_one_136_ = lean_unsigned_to_nat(1u);
v_n_137_ = lean_nat_sub(v_x_129_, v_one_136_);
lean_dec(v_x_129_);
v_absP_138_ = lean_nat_add(v_startPos_134_, v_x_130_);
v_decide_139_ = lean_nat_dec_eq(v_absP_138_, v_stopPos_135_);
if (v_decide_139_ == 0)
{
lean_object* v___x_140_; lean_object* v___x_141_; 
lean_dec(v_x_130_);
v___x_140_ = lean_string_utf8_next(v_str_133_, v_absP_138_);
lean_dec(v_absP_138_);
v___x_141_ = lean_nat_sub(v___x_140_, v_startPos_134_);
lean_dec(v___x_140_);
v_x_129_ = v_n_137_;
v_x_130_ = v___x_141_;
goto _start;
}
else
{
lean_dec(v_absP_138_);
v_x_129_ = v_n_137_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_nextn___boxed(lean_object* v_x_144_, lean_object* v_x_145_, lean_object* v_x_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Substring_Raw_nextn(v_x_144_, v_x_145_, v_x_146_);
lean_dec_ref(v_x_144_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_prevn(lean_object* v_x_148_, lean_object* v_x_149_, lean_object* v_x_150_){
_start:
{
lean_object* v_zero_151_; uint8_t v_isZero_152_; 
v_zero_151_ = lean_unsigned_to_nat(0u);
v_isZero_152_ = lean_nat_dec_eq(v_x_149_, v_zero_151_);
if (v_isZero_152_ == 1)
{
lean_dec(v_x_149_);
return v_x_150_;
}
else
{
lean_object* v_str_153_; lean_object* v_startPos_154_; lean_object* v_one_155_; lean_object* v_n_156_; lean_object* v_absP_157_; uint8_t v_decide_158_; 
v_str_153_ = lean_ctor_get(v_x_148_, 0);
v_startPos_154_ = lean_ctor_get(v_x_148_, 1);
v_one_155_ = lean_unsigned_to_nat(1u);
v_n_156_ = lean_nat_sub(v_x_149_, v_one_155_);
lean_dec(v_x_149_);
v_absP_157_ = lean_nat_add(v_startPos_154_, v_x_150_);
v_decide_158_ = lean_nat_dec_eq(v_absP_157_, v_startPos_154_);
if (v_decide_158_ == 0)
{
lean_object* v___x_159_; lean_object* v___x_160_; 
lean_dec(v_x_150_);
v___x_159_ = lean_string_utf8_prev(v_str_153_, v_absP_157_);
lean_dec(v_absP_157_);
v___x_160_ = lean_nat_sub(v___x_159_, v_startPos_154_);
lean_dec(v___x_159_);
v_x_149_ = v_n_156_;
v_x_150_ = v___x_160_;
goto _start;
}
else
{
lean_dec(v_absP_157_);
v_x_149_ = v_n_156_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_prevn___boxed(lean_object* v_x_163_, lean_object* v_x_164_, lean_object* v_x_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Substring_Raw_prevn(v_x_163_, v_x_164_, v_x_165_);
lean_dec_ref(v_x_163_);
return v_res_166_;
}
}
LEAN_EXPORT uint32_t l_Substring_Raw_front(lean_object* v_s_167_){
_start:
{
lean_object* v_str_168_; lean_object* v_startPos_169_; uint32_t v___x_170_; 
v_str_168_ = lean_ctor_get(v_s_167_, 0);
v_startPos_169_ = lean_ctor_get(v_s_167_, 1);
v___x_170_ = lean_string_utf8_get(v_str_168_, v_startPos_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_front___boxed(lean_object* v_s_171_){
_start:
{
uint32_t v_res_172_; lean_object* v_r_173_; 
v_res_172_ = l_Substring_Raw_front(v_s_171_);
lean_dec_ref(v_s_171_);
v_r_173_ = lean_box_uint32(v_res_172_);
return v_r_173_;
}
}
LEAN_EXPORT uint32_t lean_substring_front(lean_object* v_s_174_){
_start:
{
lean_object* v_str_175_; lean_object* v_startPos_176_; uint32_t v___x_177_; 
v_str_175_ = lean_ctor_get(v_s_174_, 0);
lean_inc_ref(v_str_175_);
v_startPos_176_ = lean_ctor_get(v_s_174_, 1);
lean_inc(v_startPos_176_);
lean_dec_ref(v_s_174_);
v___x_177_ = lean_string_utf8_get(v_str_175_, v_startPos_176_);
lean_dec(v_startPos_176_);
lean_dec_ref(v_str_175_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_frontImpl___boxed(lean_object* v_s_178_){
_start:
{
uint32_t v_res_179_; lean_object* v_r_180_; 
v_res_179_ = lean_substring_front(v_s_178_);
v_r_180_ = lean_box_uint32(v_res_179_);
return v_r_180_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_posOf___lam__0(lean_object* v_stopPos_181_, lean_object* v_startPos_182_, lean_object* v_str_183_, uint32_t v_c_184_, lean_object* v___x_185_, lean_object* v_it_186_, lean_object* v_acc_187_, lean_object* v_hP_188_, lean_object* v_recur_189_){
_start:
{
lean_object* v___x_190_; uint8_t v_decide_191_; 
v___x_190_ = lean_nat_sub(v_stopPos_181_, v_startPos_182_);
v_decide_191_ = lean_nat_dec_eq(v_it_186_, v___x_190_);
lean_dec(v___x_190_);
if (v_decide_191_ == 0)
{
lean_object* v___x_192_; uint32_t v___x_193_; uint8_t v___x_194_; 
v___x_192_ = lean_nat_add(v_startPos_182_, v_it_186_);
v___x_193_ = lean_string_utf8_get_fast(v_str_183_, v___x_192_);
v___x_194_ = lean_uint32_dec_eq(v___x_193_, v_c_184_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
lean_dec(v_it_186_);
v___x_195_ = lean_string_utf8_next_fast(v_str_183_, v___x_192_);
lean_dec(v___x_192_);
v___x_196_ = lean_nat_sub(v___x_195_, v_startPos_182_);
v___x_197_ = lean_apply_4(v_recur_189_, v___x_196_, v___x_185_, lean_box(0), lean_box(0));
return v___x_197_;
}
else
{
lean_object* v___x_198_; 
lean_dec(v___x_192_);
lean_dec_ref(v_recur_189_);
lean_dec(v___x_185_);
v___x_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_198_, 0, v_it_186_);
return v___x_198_;
}
}
else
{
lean_dec_ref(v_recur_189_);
lean_dec(v_it_186_);
lean_dec(v___x_185_);
lean_inc(v_acc_187_);
return v_acc_187_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_posOf___lam__0___boxed(lean_object* v_stopPos_199_, lean_object* v_startPos_200_, lean_object* v_str_201_, lean_object* v_c_202_, lean_object* v___x_203_, lean_object* v_it_204_, lean_object* v_acc_205_, lean_object* v_hP_206_, lean_object* v_recur_207_){
_start:
{
uint32_t v_c_boxed_208_; lean_object* v_res_209_; 
v_c_boxed_208_ = lean_unbox_uint32(v_c_202_);
lean_dec(v_c_202_);
v_res_209_ = l_Substring_Raw_posOf___lam__0(v_stopPos_199_, v_startPos_200_, v_str_201_, v_c_boxed_208_, v___x_203_, v_it_204_, v_acc_205_, v_hP_206_, v_recur_207_);
lean_dec(v_acc_205_);
lean_dec_ref(v_str_201_);
lean_dec(v_startPos_200_);
lean_dec(v_stopPos_199_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_posOf(lean_object* v_s_210_, uint32_t v_c_211_){
_start:
{
lean_object* v_str_212_; lean_object* v_startPos_213_; lean_object* v_stopPos_214_; uint8_t v___y_216_; uint8_t v___x_225_; uint8_t v___y_227_; uint8_t v___x_228_; 
v_str_212_ = lean_ctor_get(v_s_210_, 0);
lean_inc_ref(v_str_212_);
v_startPos_213_ = lean_ctor_get(v_s_210_, 1);
lean_inc(v_startPos_213_);
v_stopPos_214_ = lean_ctor_get(v_s_210_, 2);
lean_inc(v_stopPos_214_);
lean_dec_ref(v_s_210_);
v___x_225_ = lean_string_is_valid_pos(v_str_212_, v_startPos_213_);
v___x_228_ = lean_string_is_valid_pos(v_str_212_, v_stopPos_214_);
if (v___x_228_ == 0)
{
v___y_227_ = v___x_228_;
goto v___jp_226_;
}
else
{
uint8_t v___x_229_; 
v___x_229_ = lean_nat_dec_le(v_startPos_213_, v_stopPos_214_);
v___y_227_ = v___x_229_;
goto v___jp_226_;
}
v___jp_215_:
{
if (v___y_216_ == 0)
{
lean_object* v___x_217_; 
lean_dec_ref(v_str_212_);
v___x_217_ = lean_nat_sub(v_stopPos_214_, v_startPos_213_);
lean_dec(v_startPos_213_);
lean_dec(v_stopPos_214_);
return v___x_217_;
}
else
{
lean_object* v_searcher_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___f_221_; lean_object* v___x_222_; 
v_searcher_218_ = lean_unsigned_to_nat(0u);
v___x_219_ = lean_box(0);
v___x_220_ = lean_box_uint32(v_c_211_);
lean_inc(v_startPos_213_);
lean_inc(v_stopPos_214_);
v___f_221_ = lean_alloc_closure((void*)(l_Substring_Raw_posOf___lam__0___boxed), 9, 5);
lean_closure_set(v___f_221_, 0, v_stopPos_214_);
lean_closure_set(v___f_221_, 1, v_startPos_213_);
lean_closure_set(v___f_221_, 2, v_str_212_);
lean_closure_set(v___f_221_, 3, v___x_220_);
lean_closure_set(v___f_221_, 4, v___x_219_);
v___x_222_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_221_, v_searcher_218_, v___x_219_, lean_box(0));
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v___x_223_; 
v___x_223_ = lean_nat_sub(v_stopPos_214_, v_startPos_213_);
lean_dec(v_startPos_213_);
lean_dec(v_stopPos_214_);
return v___x_223_;
}
else
{
lean_object* v_val_224_; 
lean_dec(v_stopPos_214_);
lean_dec(v_startPos_213_);
v_val_224_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_val_224_);
lean_dec_ref_known(v___x_222_, 1);
return v_val_224_;
}
}
}
v___jp_226_:
{
if (v___x_225_ == 0)
{
v___y_216_ = v___x_225_;
goto v___jp_215_;
}
else
{
v___y_216_ = v___y_227_;
goto v___jp_215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_posOf___boxed(lean_object* v_s_230_, lean_object* v_c_231_){
_start:
{
uint32_t v_c_boxed_232_; lean_object* v_res_233_; 
v_c_boxed_232_ = lean_unbox_uint32(v_c_231_);
lean_dec(v_c_231_);
v_res_233_ = l_Substring_Raw_posOf(v_s_230_, v_c_boxed_232_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_drop(lean_object* v_x_234_, lean_object* v_x_235_){
_start:
{
lean_object* v_str_236_; lean_object* v_startPos_237_; lean_object* v_stopPos_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_248_; 
v_str_236_ = lean_ctor_get(v_x_234_, 0);
lean_inc_ref(v_str_236_);
v_startPos_237_ = lean_ctor_get(v_x_234_, 1);
lean_inc(v_startPos_237_);
v_stopPos_238_ = lean_ctor_get(v_x_234_, 2);
lean_inc(v_stopPos_238_);
v___x_239_ = lean_unsigned_to_nat(0u);
v___x_240_ = l_Substring_Raw_nextn(v_x_234_, v_x_235_, v___x_239_);
v_isSharedCheck_248_ = !lean_is_exclusive(v_x_234_);
if (v_isSharedCheck_248_ == 0)
{
lean_object* v_unused_249_; lean_object* v_unused_250_; lean_object* v_unused_251_; 
v_unused_249_ = lean_ctor_get(v_x_234_, 2);
lean_dec(v_unused_249_);
v_unused_250_ = lean_ctor_get(v_x_234_, 1);
lean_dec(v_unused_250_);
v_unused_251_ = lean_ctor_get(v_x_234_, 0);
lean_dec(v_unused_251_);
v___x_242_ = v_x_234_;
v_isShared_243_ = v_isSharedCheck_248_;
goto v_resetjp_241_;
}
else
{
lean_dec(v_x_234_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_248_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_244_; lean_object* v___x_246_; 
v___x_244_ = lean_nat_add(v_startPos_237_, v___x_240_);
lean_dec(v___x_240_);
lean_dec(v_startPos_237_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 1, v___x_244_);
v___x_246_ = v___x_242_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_str_236_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v___x_244_);
lean_ctor_set(v_reuseFailAlloc_247_, 2, v_stopPos_238_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
LEAN_EXPORT lean_object* lean_substring_drop(lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_str_254_; lean_object* v_startPos_255_; lean_object* v_stopPos_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_266_; 
v_str_254_ = lean_ctor_get(v_a_252_, 0);
lean_inc_ref(v_str_254_);
v_startPos_255_ = lean_ctor_get(v_a_252_, 1);
lean_inc(v_startPos_255_);
v_stopPos_256_ = lean_ctor_get(v_a_252_, 2);
lean_inc(v_stopPos_256_);
v___x_257_ = lean_unsigned_to_nat(0u);
v___x_258_ = l_Substring_Raw_nextn(v_a_252_, v_a_253_, v___x_257_);
v_isSharedCheck_266_ = !lean_is_exclusive(v_a_252_);
if (v_isSharedCheck_266_ == 0)
{
lean_object* v_unused_267_; lean_object* v_unused_268_; lean_object* v_unused_269_; 
v_unused_267_ = lean_ctor_get(v_a_252_, 2);
lean_dec(v_unused_267_);
v_unused_268_ = lean_ctor_get(v_a_252_, 1);
lean_dec(v_unused_268_);
v_unused_269_ = lean_ctor_get(v_a_252_, 0);
lean_dec(v_unused_269_);
v___x_260_ = v_a_252_;
v_isShared_261_ = v_isSharedCheck_266_;
goto v_resetjp_259_;
}
else
{
lean_dec(v_a_252_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_266_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_262_; lean_object* v___x_264_; 
v___x_262_ = lean_nat_add(v_startPos_255_, v___x_258_);
lean_dec(v___x_258_);
lean_dec(v_startPos_255_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 1, v___x_262_);
v___x_264_ = v___x_260_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_str_254_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v___x_262_);
lean_ctor_set(v_reuseFailAlloc_265_, 2, v_stopPos_256_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropRight(lean_object* v_x_270_, lean_object* v_x_271_){
_start:
{
lean_object* v_str_272_; lean_object* v_startPos_273_; lean_object* v_stopPos_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_284_; 
v_str_272_ = lean_ctor_get(v_x_270_, 0);
lean_inc_ref(v_str_272_);
v_startPos_273_ = lean_ctor_get(v_x_270_, 1);
lean_inc(v_startPos_273_);
v_stopPos_274_ = lean_ctor_get(v_x_270_, 2);
v___x_275_ = lean_nat_sub(v_stopPos_274_, v_startPos_273_);
v___x_276_ = l_Substring_Raw_prevn(v_x_270_, v_x_271_, v___x_275_);
v_isSharedCheck_284_ = !lean_is_exclusive(v_x_270_);
if (v_isSharedCheck_284_ == 0)
{
lean_object* v_unused_285_; lean_object* v_unused_286_; lean_object* v_unused_287_; 
v_unused_285_ = lean_ctor_get(v_x_270_, 2);
lean_dec(v_unused_285_);
v_unused_286_ = lean_ctor_get(v_x_270_, 1);
lean_dec(v_unused_286_);
v_unused_287_ = lean_ctor_get(v_x_270_, 0);
lean_dec(v_unused_287_);
v___x_278_ = v_x_270_;
v_isShared_279_ = v_isSharedCheck_284_;
goto v_resetjp_277_;
}
else
{
lean_dec(v_x_270_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_284_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_280_ = lean_nat_add(v_startPos_273_, v___x_276_);
lean_dec(v___x_276_);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 2, v___x_280_);
v___x_282_ = v___x_278_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_str_272_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v_startPos_273_);
lean_ctor_set(v_reuseFailAlloc_283_, 2, v___x_280_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_take(lean_object* v_x_288_, lean_object* v_x_289_){
_start:
{
lean_object* v_str_290_; lean_object* v_startPos_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_301_; 
v_str_290_ = lean_ctor_get(v_x_288_, 0);
lean_inc_ref(v_str_290_);
v_startPos_291_ = lean_ctor_get(v_x_288_, 1);
lean_inc(v_startPos_291_);
v___x_292_ = lean_unsigned_to_nat(0u);
v___x_293_ = l_Substring_Raw_nextn(v_x_288_, v_x_289_, v___x_292_);
v_isSharedCheck_301_ = !lean_is_exclusive(v_x_288_);
if (v_isSharedCheck_301_ == 0)
{
lean_object* v_unused_302_; lean_object* v_unused_303_; lean_object* v_unused_304_; 
v_unused_302_ = lean_ctor_get(v_x_288_, 2);
lean_dec(v_unused_302_);
v_unused_303_ = lean_ctor_get(v_x_288_, 1);
lean_dec(v_unused_303_);
v_unused_304_ = lean_ctor_get(v_x_288_, 0);
lean_dec(v_unused_304_);
v___x_295_ = v_x_288_;
v_isShared_296_ = v_isSharedCheck_301_;
goto v_resetjp_294_;
}
else
{
lean_dec(v_x_288_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_301_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_297_ = lean_nat_add(v_startPos_291_, v___x_293_);
lean_dec(v___x_293_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 2, v___x_297_);
v___x_299_ = v___x_295_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_str_290_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v_startPos_291_);
lean_ctor_set(v_reuseFailAlloc_300_, 2, v___x_297_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRight(lean_object* v_x_305_, lean_object* v_x_306_){
_start:
{
lean_object* v_str_307_; lean_object* v_startPos_308_; lean_object* v_stopPos_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_319_; 
v_str_307_ = lean_ctor_get(v_x_305_, 0);
lean_inc_ref(v_str_307_);
v_startPos_308_ = lean_ctor_get(v_x_305_, 1);
lean_inc(v_startPos_308_);
v_stopPos_309_ = lean_ctor_get(v_x_305_, 2);
lean_inc(v_stopPos_309_);
v___x_310_ = lean_nat_sub(v_stopPos_309_, v_startPos_308_);
v___x_311_ = l_Substring_Raw_prevn(v_x_305_, v_x_306_, v___x_310_);
v_isSharedCheck_319_ = !lean_is_exclusive(v_x_305_);
if (v_isSharedCheck_319_ == 0)
{
lean_object* v_unused_320_; lean_object* v_unused_321_; lean_object* v_unused_322_; 
v_unused_320_ = lean_ctor_get(v_x_305_, 2);
lean_dec(v_unused_320_);
v_unused_321_ = lean_ctor_get(v_x_305_, 1);
lean_dec(v_unused_321_);
v_unused_322_ = lean_ctor_get(v_x_305_, 0);
lean_dec(v_unused_322_);
v___x_313_ = v_x_305_;
v_isShared_314_ = v_isSharedCheck_319_;
goto v_resetjp_312_;
}
else
{
lean_dec(v_x_305_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_319_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_315_; lean_object* v___x_317_; 
v___x_315_ = lean_nat_add(v_startPos_308_, v___x_311_);
lean_dec(v___x_311_);
lean_dec(v_startPos_308_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 1, v___x_315_);
v___x_317_ = v___x_313_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_str_307_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v___x_315_);
lean_ctor_set(v_reuseFailAlloc_318_, 2, v_stopPos_309_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_atEnd(lean_object* v_x_323_, lean_object* v_x_324_){
_start:
{
lean_object* v_startPos_325_; lean_object* v_stopPos_326_; lean_object* v___x_327_; uint8_t v_decide_328_; 
v_startPos_325_ = lean_ctor_get(v_x_323_, 1);
v_stopPos_326_ = lean_ctor_get(v_x_323_, 2);
v___x_327_ = lean_nat_add(v_startPos_325_, v_x_324_);
v_decide_328_ = lean_nat_dec_eq(v___x_327_, v_stopPos_326_);
lean_dec(v___x_327_);
return v_decide_328_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_atEnd___boxed(lean_object* v_x_329_, lean_object* v_x_330_){
_start:
{
uint8_t v_res_331_; lean_object* v_r_332_; 
v_res_331_ = l_Substring_Raw_atEnd(v_x_329_, v_x_330_);
lean_dec(v_x_330_);
lean_dec_ref(v_x_329_);
v_r_332_ = lean_box(v_res_331_);
return v_r_332_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_extract(lean_object* v_x_337_, lean_object* v_x_338_, lean_object* v_x_339_){
_start:
{
lean_object* v_str_340_; lean_object* v_startPos_341_; lean_object* v_stopPos_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_360_; 
v_str_340_ = lean_ctor_get(v_x_337_, 0);
v_startPos_341_ = lean_ctor_get(v_x_337_, 1);
v_stopPos_342_ = lean_ctor_get(v_x_337_, 2);
v_isSharedCheck_360_ = !lean_is_exclusive(v_x_337_);
if (v_isSharedCheck_360_ == 0)
{
v___x_344_ = v_x_337_;
v_isShared_345_ = v_isSharedCheck_360_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_stopPos_342_);
lean_inc(v_startPos_341_);
lean_inc(v_str_340_);
lean_dec(v_x_337_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_360_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___y_347_; uint8_t v___x_356_; 
v___x_356_ = lean_nat_dec_le(v_x_339_, v_x_338_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_357_ = lean_nat_add(v_startPos_341_, v_x_338_);
v___x_358_ = lean_nat_dec_le(v_stopPos_342_, v___x_357_);
if (v___x_358_ == 0)
{
v___y_347_ = v___x_357_;
goto v___jp_346_;
}
else
{
lean_dec(v___x_357_);
lean_inc(v_stopPos_342_);
v___y_347_ = v_stopPos_342_;
goto v___jp_346_;
}
}
else
{
lean_object* v___x_359_; 
lean_del_object(v___x_344_);
lean_dec(v_stopPos_342_);
lean_dec(v_startPos_341_);
lean_dec_ref(v_str_340_);
v___x_359_ = ((lean_object*)(l_Substring_Raw_extract___closed__1));
return v___x_359_;
}
v___jp_346_:
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = lean_nat_add(v_startPos_341_, v_x_339_);
lean_dec(v_startPos_341_);
v___x_349_ = lean_nat_dec_le(v_stopPos_342_, v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_351_; 
lean_dec(v_stopPos_342_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 2, v___x_348_);
lean_ctor_set(v___x_344_, 1, v___y_347_);
v___x_351_ = v___x_344_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_str_340_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v___y_347_);
lean_ctor_set(v_reuseFailAlloc_352_, 2, v___x_348_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
else
{
lean_object* v___x_354_; 
lean_dec(v___x_348_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 1, v___y_347_);
v___x_354_ = v___x_344_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_str_340_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v___y_347_);
lean_ctor_set(v_reuseFailAlloc_355_, 2, v_stopPos_342_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_extract___boxed(lean_object* v_x_361_, lean_object* v_x_362_, lean_object* v_x_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Substring_Raw_extract(v_x_361_, v_x_362_, v_x_363_);
lean_dec(v_x_363_);
lean_dec(v_x_362_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* lean_substring_extract(lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_str_368_; lean_object* v_startPos_369_; lean_object* v_stopPos_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_388_; 
v_str_368_ = lean_ctor_get(v_a_365_, 0);
v_startPos_369_ = lean_ctor_get(v_a_365_, 1);
v_stopPos_370_ = lean_ctor_get(v_a_365_, 2);
v_isSharedCheck_388_ = !lean_is_exclusive(v_a_365_);
if (v_isSharedCheck_388_ == 0)
{
v___x_372_ = v_a_365_;
v_isShared_373_ = v_isSharedCheck_388_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_stopPos_370_);
lean_inc(v_startPos_369_);
lean_inc(v_str_368_);
lean_dec(v_a_365_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_388_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___y_375_; uint8_t v___x_384_; 
v___x_384_ = lean_nat_dec_le(v_a_367_, v_a_366_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; uint8_t v___x_386_; 
v___x_385_ = lean_nat_add(v_startPos_369_, v_a_366_);
lean_dec(v_a_366_);
v___x_386_ = lean_nat_dec_le(v_stopPos_370_, v___x_385_);
if (v___x_386_ == 0)
{
v___y_375_ = v___x_385_;
goto v___jp_374_;
}
else
{
lean_dec(v___x_385_);
lean_inc(v_stopPos_370_);
v___y_375_ = v_stopPos_370_;
goto v___jp_374_;
}
}
else
{
lean_object* v___x_387_; 
lean_del_object(v___x_372_);
lean_dec(v_stopPos_370_);
lean_dec(v_startPos_369_);
lean_dec_ref(v_str_368_);
lean_dec(v_a_367_);
lean_dec(v_a_366_);
v___x_387_ = ((lean_object*)(l_Substring_Raw_extract___closed__1));
return v___x_387_;
}
v___jp_374_:
{
lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_376_ = lean_nat_add(v_startPos_369_, v_a_367_);
lean_dec(v_a_367_);
lean_dec(v_startPos_369_);
v___x_377_ = lean_nat_dec_le(v_stopPos_370_, v___x_376_);
if (v___x_377_ == 0)
{
lean_object* v___x_379_; 
lean_dec(v_stopPos_370_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 2, v___x_376_);
lean_ctor_set(v___x_372_, 1, v___y_375_);
v___x_379_ = v___x_372_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_str_368_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v___y_375_);
lean_ctor_set(v_reuseFailAlloc_380_, 2, v___x_376_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
else
{
lean_object* v___x_382_; 
lean_dec(v___x_376_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 1, v___y_375_);
v___x_382_ = v___x_372_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_str_368_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v___y_375_);
lean_ctor_set(v_reuseFailAlloc_383_, 2, v_stopPos_370_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop(lean_object* v_s_389_, lean_object* v_sep_390_, lean_object* v_b_391_, lean_object* v_i_392_, lean_object* v_j_393_, lean_object* v_r_394_){
_start:
{
lean_object* v___y_396_; lean_object* v___y_400_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v_str_409_; lean_object* v_startPos_410_; lean_object* v_stopPos_411_; lean_object* v___y_413_; lean_object* v___y_414_; lean_object* v___y_415_; lean_object* v___y_416_; lean_object* v___y_422_; lean_object* v___y_433_; lean_object* v___x_438_; uint8_t v___x_439_; 
v_str_409_ = lean_ctor_get(v_s_389_, 0);
v_startPos_410_ = lean_ctor_get(v_s_389_, 1);
v_stopPos_411_ = lean_ctor_get(v_s_389_, 2);
v___x_438_ = lean_nat_sub(v_stopPos_411_, v_startPos_410_);
v___x_439_ = lean_nat_dec_lt(v_i_392_, v___x_438_);
lean_dec(v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_468_; 
lean_inc(v_stopPos_411_);
lean_inc(v_startPos_410_);
lean_inc_ref(v_str_409_);
v_isSharedCheck_468_ = !lean_is_exclusive(v_s_389_);
if (v_isSharedCheck_468_ == 0)
{
lean_object* v_unused_469_; lean_object* v_unused_470_; lean_object* v_unused_471_; 
v_unused_469_ = lean_ctor_get(v_s_389_, 2);
lean_dec(v_unused_469_);
v_unused_470_ = lean_ctor_get(v_s_389_, 1);
lean_dec(v_unused_470_);
v_unused_471_ = lean_ctor_get(v_s_389_, 0);
lean_dec(v_unused_471_);
v___x_441_ = v_s_389_;
v_isShared_442_ = v_isSharedCheck_468_;
goto v_resetjp_440_;
}
else
{
lean_dec(v_s_389_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_468_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
uint8_t v___x_443_; 
v___x_443_ = lean_string_utf8_at_end(v_sep_390_, v_j_393_);
if (v___x_443_ == 0)
{
uint8_t v___x_444_; 
lean_del_object(v___x_441_);
lean_dec(v_j_393_);
v___x_444_ = lean_nat_dec_le(v_i_392_, v_b_391_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_445_ = lean_nat_add(v_startPos_410_, v_b_391_);
lean_dec(v_b_391_);
v___x_446_ = lean_nat_dec_le(v_stopPos_411_, v___x_445_);
if (v___x_446_ == 0)
{
v___y_433_ = v___x_445_;
goto v___jp_432_;
}
else
{
lean_dec(v___x_445_);
lean_inc(v_stopPos_411_);
v___y_433_ = v_stopPos_411_;
goto v___jp_432_;
}
}
else
{
lean_object* v___x_447_; 
lean_dec(v_stopPos_411_);
lean_dec(v_startPos_410_);
lean_dec_ref(v_str_409_);
lean_dec(v_i_392_);
lean_dec(v_b_391_);
v___x_447_ = ((lean_object*)(l_Substring_Raw_extract___closed__1));
v___y_396_ = v___x_447_;
goto v___jp_395_;
}
}
else
{
lean_object* v___x_448_; lean_object* v___y_450_; lean_object* v___x_454_; lean_object* v___y_456_; uint8_t v___x_465_; 
v___x_448_ = ((lean_object*)(l_Substring_Raw_extract___closed__1));
v___x_454_ = lean_nat_sub(v_i_392_, v_j_393_);
lean_dec(v_j_393_);
lean_dec(v_i_392_);
v___x_465_ = lean_nat_dec_le(v___x_454_, v_b_391_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_466_ = lean_nat_add(v_startPos_410_, v_b_391_);
lean_dec(v_b_391_);
v___x_467_ = lean_nat_dec_le(v_stopPos_411_, v___x_466_);
if (v___x_467_ == 0)
{
v___y_456_ = v___x_466_;
goto v___jp_455_;
}
else
{
lean_dec(v___x_466_);
lean_inc(v_stopPos_411_);
v___y_456_ = v_stopPos_411_;
goto v___jp_455_;
}
}
else
{
lean_dec(v___x_454_);
lean_del_object(v___x_441_);
lean_dec(v_stopPos_411_);
lean_dec(v_startPos_410_);
lean_dec_ref(v_str_409_);
lean_dec(v_b_391_);
v___y_450_ = v___x_448_;
goto v___jp_449_;
}
v___jp_449_:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_451_, 0, v___y_450_);
lean_ctor_set(v___x_451_, 1, v_r_394_);
v___x_452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_448_);
lean_ctor_set(v___x_452_, 1, v___x_451_);
v___x_453_ = l_List_reverse___redArg(v___x_452_);
return v___x_453_;
}
v___jp_455_:
{
lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_457_ = lean_nat_add(v_startPos_410_, v___x_454_);
lean_dec(v___x_454_);
lean_dec(v_startPos_410_);
v___x_458_ = lean_nat_dec_le(v_stopPos_411_, v___x_457_);
if (v___x_458_ == 0)
{
lean_object* v___x_460_; 
lean_dec(v_stopPos_411_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 2, v___x_457_);
lean_ctor_set(v___x_441_, 1, v___y_456_);
v___x_460_ = v___x_441_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_str_409_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v___y_456_);
lean_ctor_set(v_reuseFailAlloc_461_, 2, v___x_457_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
v___y_450_ = v___x_460_;
goto v___jp_449_;
}
}
else
{
lean_object* v___x_463_; 
lean_dec(v___x_457_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 1, v___y_456_);
v___x_463_ = v___x_441_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_str_409_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v___y_456_);
lean_ctor_set(v_reuseFailAlloc_464_, 2, v_stopPos_411_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
v___y_450_ = v___x_463_;
goto v___jp_449_;
}
}
}
}
}
}
else
{
lean_object* v___x_472_; uint32_t v___x_473_; uint32_t v___x_474_; uint8_t v___x_475_; 
v___x_472_ = lean_nat_add(v_startPos_410_, v_i_392_);
v___x_473_ = lean_string_utf8_get(v_str_409_, v___x_472_);
v___x_474_ = lean_string_utf8_get(v_sep_390_, v_j_393_);
v___x_475_ = lean_uint32_dec_eq(v___x_473_, v___x_474_);
if (v___x_475_ == 0)
{
uint8_t v_decide_476_; 
lean_dec(v_j_393_);
v_decide_476_ = lean_nat_dec_eq(v___x_472_, v_stopPos_411_);
if (v_decide_476_ == 0)
{
lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec(v_i_392_);
v___x_477_ = lean_string_utf8_next(v_str_409_, v___x_472_);
lean_dec(v___x_472_);
v___x_478_ = lean_nat_sub(v___x_477_, v_startPos_410_);
lean_dec(v___x_477_);
v___y_400_ = v___x_478_;
goto v___jp_399_;
}
else
{
lean_dec(v___x_472_);
v___y_400_ = v_i_392_;
goto v___jp_399_;
}
}
else
{
uint8_t v_decide_479_; 
v_decide_479_ = lean_nat_dec_eq(v___x_472_, v_stopPos_411_);
if (v_decide_479_ == 0)
{
lean_object* v___x_480_; lean_object* v___x_481_; 
lean_dec(v_i_392_);
v___x_480_ = lean_string_utf8_next(v_str_409_, v___x_472_);
lean_dec(v___x_472_);
v___x_481_ = lean_nat_sub(v___x_480_, v_startPos_410_);
lean_dec(v___x_480_);
v___y_422_ = v___x_481_;
goto v___jp_421_;
}
else
{
lean_dec(v___x_472_);
v___y_422_ = v_i_392_;
goto v___jp_421_;
}
}
}
v___jp_395_:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_397_, 0, v___y_396_);
lean_ctor_set(v___x_397_, 1, v_r_394_);
v___x_398_ = l_List_reverse___redArg(v___x_397_);
return v___x_398_;
}
v___jp_399_:
{
lean_object* v___x_401_; 
v___x_401_ = lean_unsigned_to_nat(0u);
v_i_392_ = v___y_400_;
v_j_393_ = v___x_401_;
goto _start;
}
v___jp_403_:
{
lean_object* v___x_407_; 
v___x_407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_407_, 0, v___y_406_);
lean_ctor_set(v___x_407_, 1, v_r_394_);
lean_inc(v___y_404_);
v_b_391_ = v___y_404_;
v_i_392_ = v___y_404_;
v_j_393_ = v___y_405_;
v_r_394_ = v___x_407_;
goto _start;
}
v___jp_412_:
{
lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_417_ = lean_nat_add(v_startPos_410_, v___y_414_);
lean_dec(v___y_414_);
v___x_418_ = lean_nat_dec_le(v_stopPos_411_, v___x_417_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; 
lean_inc_ref(v_str_409_);
v___x_419_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_419_, 0, v_str_409_);
lean_ctor_set(v___x_419_, 1, v___y_416_);
lean_ctor_set(v___x_419_, 2, v___x_417_);
v___y_404_ = v___y_413_;
v___y_405_ = v___y_415_;
v___y_406_ = v___x_419_;
goto v___jp_403_;
}
else
{
lean_object* v___x_420_; 
lean_dec(v___x_417_);
lean_inc(v_stopPos_411_);
lean_inc_ref(v_str_409_);
v___x_420_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_420_, 0, v_str_409_);
lean_ctor_set(v___x_420_, 1, v___y_416_);
lean_ctor_set(v___x_420_, 2, v_stopPos_411_);
v___y_404_ = v___y_413_;
v___y_405_ = v___y_415_;
v___y_406_ = v___x_420_;
goto v___jp_403_;
}
}
v___jp_421_:
{
lean_object* v_j_423_; uint8_t v___x_424_; 
v_j_423_ = lean_string_utf8_next(v_sep_390_, v_j_393_);
lean_dec(v_j_393_);
v___x_424_ = lean_string_utf8_at_end(v_sep_390_, v_j_423_);
if (v___x_424_ == 0)
{
v_i_392_ = v___y_422_;
v_j_393_ = v_j_423_;
goto _start;
}
else
{
lean_object* v___x_426_; lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_426_ = lean_unsigned_to_nat(0u);
v___x_427_ = lean_nat_sub(v___y_422_, v_j_423_);
lean_dec(v_j_423_);
v___x_428_ = lean_nat_dec_le(v___x_427_, v_b_391_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_429_ = lean_nat_add(v_startPos_410_, v_b_391_);
lean_dec(v_b_391_);
v___x_430_ = lean_nat_dec_le(v_stopPos_411_, v___x_429_);
if (v___x_430_ == 0)
{
v___y_413_ = v___y_422_;
v___y_414_ = v___x_427_;
v___y_415_ = v___x_426_;
v___y_416_ = v___x_429_;
goto v___jp_412_;
}
else
{
lean_dec(v___x_429_);
lean_inc(v_stopPos_411_);
v___y_413_ = v___y_422_;
v___y_414_ = v___x_427_;
v___y_415_ = v___x_426_;
v___y_416_ = v_stopPos_411_;
goto v___jp_412_;
}
}
else
{
lean_object* v___x_431_; 
lean_dec(v___x_427_);
lean_dec(v_b_391_);
v___x_431_ = ((lean_object*)(l_Substring_Raw_extract___closed__1));
v___y_404_ = v___y_422_;
v___y_405_ = v___x_426_;
v___y_406_ = v___x_431_;
goto v___jp_403_;
}
}
}
v___jp_432_:
{
lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_434_ = lean_nat_add(v_startPos_410_, v_i_392_);
lean_dec(v_i_392_);
lean_dec(v_startPos_410_);
v___x_435_ = lean_nat_dec_le(v_stopPos_411_, v___x_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; 
lean_dec(v_stopPos_411_);
v___x_436_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_436_, 0, v_str_409_);
lean_ctor_set(v___x_436_, 1, v___y_433_);
lean_ctor_set(v___x_436_, 2, v___x_434_);
v___y_396_ = v___x_436_;
goto v___jp_395_;
}
else
{
lean_object* v___x_437_; 
lean_dec(v___x_434_);
v___x_437_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_437_, 0, v_str_409_);
lean_ctor_set(v___x_437_, 1, v___y_433_);
lean_ctor_set(v___x_437_, 2, v_stopPos_411_);
v___y_396_ = v___x_437_;
goto v___jp_395_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___boxed(lean_object* v_s_482_, lean_object* v_sep_483_, lean_object* v_b_484_, lean_object* v_i_485_, lean_object* v_j_486_, lean_object* v_r_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop(v_s_482_, v_sep_483_, v_b_484_, v_i_485_, v_j_486_, v_r_487_);
lean_dec_ref(v_sep_483_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_splitOn(lean_object* v_s_489_, lean_object* v_sep_490_){
_start:
{
lean_object* v___x_491_; uint8_t v___x_492_; 
v___x_491_ = ((lean_object*)(l_Substring_Raw_extract___closed__0));
v___x_492_ = lean_string_dec_eq(v_sep_490_, v___x_491_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_493_ = lean_unsigned_to_nat(0u);
v___x_494_ = lean_box(0);
v___x_495_ = l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop(v_s_489_, v_sep_490_, v___x_493_, v___x_493_, v___x_493_, v___x_494_);
return v___x_495_;
}
else
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = lean_box(0);
v___x_497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_497_, 0, v_s_489_);
lean_ctor_set(v___x_497_, 1, v___x_496_);
return v___x_497_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_splitOn___boxed(lean_object* v_s_498_, lean_object* v_sep_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Substring_Raw_splitOn(v_s_498_, v_sep_499_);
lean_dec_ref(v_sep_499_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldl___redArg___lam__0(lean_object* v___y_501_, lean_object* v_f_502_, lean_object* v_it_503_, lean_object* v_acc_504_, lean_object* v_hP_505_, lean_object* v_recur_506_){
_start:
{
lean_object* v_str_507_; lean_object* v_startInclusive_508_; lean_object* v_endExclusive_509_; lean_object* v___x_510_; uint8_t v_decide_511_; 
v_str_507_ = lean_ctor_get(v___y_501_, 0);
v_startInclusive_508_ = lean_ctor_get(v___y_501_, 1);
v_endExclusive_509_ = lean_ctor_get(v___y_501_, 2);
v___x_510_ = lean_nat_sub(v_endExclusive_509_, v_startInclusive_508_);
v_decide_511_ = lean_nat_dec_eq(v_it_503_, v___x_510_);
lean_dec(v___x_510_);
if (v_decide_511_ == 0)
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; uint32_t v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_512_ = lean_nat_add(v_startInclusive_508_, v_it_503_);
v___x_513_ = lean_string_utf8_next_fast(v_str_507_, v___x_512_);
v___x_514_ = lean_nat_sub(v___x_513_, v_startInclusive_508_);
v___x_515_ = lean_string_utf8_get_fast(v_str_507_, v___x_512_);
lean_dec(v___x_512_);
v___x_516_ = lean_box_uint32(v___x_515_);
v___x_517_ = lean_apply_2(v_f_502_, v_acc_504_, v___x_516_);
v___x_518_ = lean_apply_4(v_recur_506_, v___x_514_, v___x_517_, lean_box(0), lean_box(0));
return v___x_518_;
}
else
{
lean_dec(v_recur_506_);
lean_dec(v_f_502_);
return v_acc_504_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldl___redArg___lam__0___boxed(lean_object* v___y_519_, lean_object* v_f_520_, lean_object* v_it_521_, lean_object* v_acc_522_, lean_object* v_hP_523_, lean_object* v_recur_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Substring_Raw_foldl___redArg___lam__0(v___y_519_, v_f_520_, v_it_521_, v_acc_522_, v_hP_523_, v_recur_524_);
lean_dec(v_it_521_);
lean_dec_ref(v___y_519_);
return v_res_525_;
}
}
static lean_object* _init_l_Substring_Raw_foldl___redArg___closed__3(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_529_ = ((lean_object*)(l_Substring_Raw_foldl___redArg___closed__2));
v___x_530_ = lean_unsigned_to_nat(14u);
v___x_531_ = lean_unsigned_to_nat(22u);
v___x_532_ = ((lean_object*)(l_Substring_Raw_foldl___redArg___closed__1));
v___x_533_ = ((lean_object*)(l_Substring_Raw_foldl___redArg___closed__0));
v___x_534_ = l_mkPanicMessageWithDecl(v___x_533_, v___x_532_, v___x_531_, v___x_530_, v___x_529_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldl___redArg(lean_object* v_f_535_, lean_object* v_init_536_, lean_object* v_s_537_){
_start:
{
lean_object* v___y_539_; lean_object* v_str_543_; lean_object* v_startPos_544_; lean_object* v_stopPos_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_562_; 
v_str_543_ = lean_ctor_get(v_s_537_, 0);
v_startPos_544_ = lean_ctor_get(v_s_537_, 1);
v_stopPos_545_ = lean_ctor_get(v_s_537_, 2);
v_isSharedCheck_562_ = !lean_is_exclusive(v_s_537_);
if (v_isSharedCheck_562_ == 0)
{
v___x_547_ = v_s_537_;
v_isShared_548_ = v_isSharedCheck_562_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_stopPos_545_);
lean_inc(v_startPos_544_);
lean_inc(v_str_543_);
lean_dec(v_s_537_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_562_;
goto v_resetjp_546_;
}
v___jp_538_:
{
lean_object* v___f_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___f_540_ = lean_alloc_closure((void*)(l_Substring_Raw_foldl___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_540_, 0, v___y_539_);
lean_closure_set(v___f_540_, 1, v_f_535_);
v___x_541_ = lean_unsigned_to_nat(0u);
v___x_542_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_540_, v___x_541_, v_init_536_, lean_box(0));
return v___x_542_;
}
v_resetjp_546_:
{
lean_object* v___x_549_; uint8_t v___y_551_; uint8_t v___x_557_; uint8_t v___y_559_; uint8_t v___x_560_; 
v___x_549_ = l_String_instInhabitedSlice;
v___x_557_ = lean_string_is_valid_pos(v_str_543_, v_startPos_544_);
v___x_560_ = lean_string_is_valid_pos(v_str_543_, v_stopPos_545_);
if (v___x_560_ == 0)
{
v___y_559_ = v___x_560_;
goto v___jp_558_;
}
else
{
uint8_t v___x_561_; 
v___x_561_ = lean_nat_dec_le(v_startPos_544_, v_stopPos_545_);
v___y_559_ = v___x_561_;
goto v___jp_558_;
}
v___jp_550_:
{
if (v___y_551_ == 0)
{
lean_object* v___x_552_; lean_object* v___x_553_; 
lean_del_object(v___x_547_);
lean_dec(v_stopPos_545_);
lean_dec(v_startPos_544_);
lean_dec_ref(v_str_543_);
v___x_552_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_553_ = l_panic___redArg(v___x_549_, v___x_552_);
v___y_539_ = v___x_553_;
goto v___jp_538_;
}
else
{
lean_object* v___x_555_; 
if (v_isShared_548_ == 0)
{
v___x_555_ = v___x_547_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_str_543_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_startPos_544_);
lean_ctor_set(v_reuseFailAlloc_556_, 2, v_stopPos_545_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
v___y_539_ = v___x_555_;
goto v___jp_538_;
}
}
}
v___jp_558_:
{
if (v___x_557_ == 0)
{
v___y_551_ = v___x_557_;
goto v___jp_550_;
}
else
{
v___y_551_ = v___y_559_;
goto v___jp_550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldl(lean_object* v_00_u03b1_563_, lean_object* v_f_564_, lean_object* v_init_565_, lean_object* v_s_566_){
_start:
{
lean_object* v___y_568_; lean_object* v_str_572_; lean_object* v_startPos_573_; lean_object* v_stopPos_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_591_; 
v_str_572_ = lean_ctor_get(v_s_566_, 0);
v_startPos_573_ = lean_ctor_get(v_s_566_, 1);
v_stopPos_574_ = lean_ctor_get(v_s_566_, 2);
v_isSharedCheck_591_ = !lean_is_exclusive(v_s_566_);
if (v_isSharedCheck_591_ == 0)
{
v___x_576_ = v_s_566_;
v_isShared_577_ = v_isSharedCheck_591_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_stopPos_574_);
lean_inc(v_startPos_573_);
lean_inc(v_str_572_);
lean_dec(v_s_566_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_591_;
goto v_resetjp_575_;
}
v___jp_567_:
{
lean_object* v___f_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___f_569_ = lean_alloc_closure((void*)(l_Substring_Raw_foldl___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_569_, 0, v___y_568_);
lean_closure_set(v___f_569_, 1, v_f_564_);
v___x_570_ = lean_unsigned_to_nat(0u);
v___x_571_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_569_, v___x_570_, v_init_565_, lean_box(0));
return v___x_571_;
}
v_resetjp_575_:
{
lean_object* v___x_578_; uint8_t v___y_580_; uint8_t v___x_586_; uint8_t v___y_588_; uint8_t v___x_589_; 
v___x_578_ = l_String_instInhabitedSlice;
v___x_586_ = lean_string_is_valid_pos(v_str_572_, v_startPos_573_);
v___x_589_ = lean_string_is_valid_pos(v_str_572_, v_stopPos_574_);
if (v___x_589_ == 0)
{
v___y_588_ = v___x_589_;
goto v___jp_587_;
}
else
{
uint8_t v___x_590_; 
v___x_590_ = lean_nat_dec_le(v_startPos_573_, v_stopPos_574_);
v___y_588_ = v___x_590_;
goto v___jp_587_;
}
v___jp_579_:
{
if (v___y_580_ == 0)
{
lean_object* v___x_581_; lean_object* v___x_582_; 
lean_del_object(v___x_576_);
lean_dec(v_stopPos_574_);
lean_dec(v_startPos_573_);
lean_dec_ref(v_str_572_);
v___x_581_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_582_ = l_panic___redArg(v___x_578_, v___x_581_);
v___y_568_ = v___x_582_;
goto v___jp_567_;
}
else
{
lean_object* v___x_584_; 
if (v_isShared_577_ == 0)
{
v___x_584_ = v___x_576_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_str_572_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_startPos_573_);
lean_ctor_set(v_reuseFailAlloc_585_, 2, v_stopPos_574_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
v___y_568_ = v___x_584_;
goto v___jp_567_;
}
}
}
v___jp_587_:
{
if (v___x_586_ == 0)
{
v___y_580_ = v___x_586_;
goto v___jp_579_;
}
else
{
v___y_580_ = v___y_588_;
goto v___jp_579_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr___redArg___lam__0(lean_object* v___y_592_, lean_object* v_f_593_, lean_object* v_it_594_, lean_object* v_acc_595_, lean_object* v_hP_596_, lean_object* v_recur_597_){
_start:
{
lean_object* v___x_598_; uint8_t v_decide_599_; 
v___x_598_ = lean_unsigned_to_nat(0u);
v_decide_599_ = lean_nat_dec_eq(v_it_594_, v___x_598_);
if (v_decide_599_ == 0)
{
lean_object* v_str_600_; lean_object* v_startInclusive_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v_prevPos_604_; lean_object* v___x_605_; uint32_t v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v_str_600_ = lean_ctor_get(v___y_592_, 0);
v_startInclusive_601_ = lean_ctor_get(v___y_592_, 1);
v___x_602_ = lean_unsigned_to_nat(1u);
v___x_603_ = lean_nat_sub(v_it_594_, v___x_602_);
v_prevPos_604_ = l_String_Slice_posLE(v___y_592_, v___x_603_);
v___x_605_ = lean_nat_add(v_startInclusive_601_, v_prevPos_604_);
v___x_606_ = lean_string_utf8_get_fast(v_str_600_, v___x_605_);
lean_dec(v___x_605_);
v___x_607_ = lean_box_uint32(v___x_606_);
v___x_608_ = lean_apply_2(v_f_593_, v___x_607_, v_acc_595_);
v___x_609_ = lean_apply_4(v_recur_597_, v_prevPos_604_, v___x_608_, lean_box(0), lean_box(0));
return v___x_609_;
}
else
{
lean_dec(v_recur_597_);
lean_dec(v_f_593_);
return v_acc_595_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr___redArg___lam__0___boxed(lean_object* v___y_610_, lean_object* v_f_611_, lean_object* v_it_612_, lean_object* v_acc_613_, lean_object* v_hP_614_, lean_object* v_recur_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Substring_Raw_foldr___redArg___lam__0(v___y_610_, v_f_611_, v_it_612_, v_acc_613_, v_hP_614_, v_recur_615_);
lean_dec(v_it_612_);
lean_dec_ref(v___y_610_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr___redArg(lean_object* v_f_617_, lean_object* v_init_618_, lean_object* v_s_619_){
_start:
{
lean_object* v___y_621_; lean_object* v_str_625_; lean_object* v_startPos_626_; lean_object* v_stopPos_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_644_; 
v_str_625_ = lean_ctor_get(v_s_619_, 0);
v_startPos_626_ = lean_ctor_get(v_s_619_, 1);
v_stopPos_627_ = lean_ctor_get(v_s_619_, 2);
v_isSharedCheck_644_ = !lean_is_exclusive(v_s_619_);
if (v_isSharedCheck_644_ == 0)
{
v___x_629_ = v_s_619_;
v_isShared_630_ = v_isSharedCheck_644_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_stopPos_627_);
lean_inc(v_startPos_626_);
lean_inc(v_str_625_);
lean_dec(v_s_619_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_644_;
goto v_resetjp_628_;
}
v___jp_620_:
{
lean_object* v___f_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
lean_inc_ref(v___y_621_);
v___f_622_ = lean_alloc_closure((void*)(l_Substring_Raw_foldr___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_622_, 0, v___y_621_);
lean_closure_set(v___f_622_, 1, v_f_617_);
v___x_623_ = l_String_Slice_revPositions(v___y_621_);
lean_dec_ref(v___y_621_);
v___x_624_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_622_, v___x_623_, v_init_618_, lean_box(0));
return v___x_624_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; uint8_t v___y_633_; uint8_t v___x_639_; uint8_t v___y_641_; uint8_t v___x_642_; 
v___x_631_ = l_String_instInhabitedSlice;
v___x_639_ = lean_string_is_valid_pos(v_str_625_, v_startPos_626_);
v___x_642_ = lean_string_is_valid_pos(v_str_625_, v_stopPos_627_);
if (v___x_642_ == 0)
{
v___y_641_ = v___x_642_;
goto v___jp_640_;
}
else
{
uint8_t v___x_643_; 
v___x_643_ = lean_nat_dec_le(v_startPos_626_, v_stopPos_627_);
v___y_641_ = v___x_643_;
goto v___jp_640_;
}
v___jp_632_:
{
if (v___y_633_ == 0)
{
lean_object* v___x_634_; lean_object* v___x_635_; 
lean_del_object(v___x_629_);
lean_dec(v_stopPos_627_);
lean_dec(v_startPos_626_);
lean_dec_ref(v_str_625_);
v___x_634_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_635_ = l_panic___redArg(v___x_631_, v___x_634_);
v___y_621_ = v___x_635_;
goto v___jp_620_;
}
else
{
lean_object* v___x_637_; 
if (v_isShared_630_ == 0)
{
v___x_637_ = v___x_629_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_str_625_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_startPos_626_);
lean_ctor_set(v_reuseFailAlloc_638_, 2, v_stopPos_627_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
v___y_621_ = v___x_637_;
goto v___jp_620_;
}
}
}
v___jp_640_:
{
if (v___x_639_ == 0)
{
v___y_633_ = v___x_639_;
goto v___jp_632_;
}
else
{
v___y_633_ = v___y_641_;
goto v___jp_632_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr(lean_object* v_00_u03b1_645_, lean_object* v_f_646_, lean_object* v_init_647_, lean_object* v_s_648_){
_start:
{
lean_object* v___y_650_; lean_object* v_str_654_; lean_object* v_startPos_655_; lean_object* v_stopPos_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_673_; 
v_str_654_ = lean_ctor_get(v_s_648_, 0);
v_startPos_655_ = lean_ctor_get(v_s_648_, 1);
v_stopPos_656_ = lean_ctor_get(v_s_648_, 2);
v_isSharedCheck_673_ = !lean_is_exclusive(v_s_648_);
if (v_isSharedCheck_673_ == 0)
{
v___x_658_ = v_s_648_;
v_isShared_659_ = v_isSharedCheck_673_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_stopPos_656_);
lean_inc(v_startPos_655_);
lean_inc(v_str_654_);
lean_dec(v_s_648_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_673_;
goto v_resetjp_657_;
}
v___jp_649_:
{
lean_object* v___f_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
lean_inc_ref(v___y_650_);
v___f_651_ = lean_alloc_closure((void*)(l_Substring_Raw_foldr___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_651_, 0, v___y_650_);
lean_closure_set(v___f_651_, 1, v_f_646_);
v___x_652_ = l_String_Slice_revPositions(v___y_650_);
lean_dec_ref(v___y_650_);
v___x_653_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_651_, v___x_652_, v_init_647_, lean_box(0));
return v___x_653_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; uint8_t v___y_662_; uint8_t v___x_668_; uint8_t v___y_670_; uint8_t v___x_671_; 
v___x_660_ = l_String_instInhabitedSlice;
v___x_668_ = lean_string_is_valid_pos(v_str_654_, v_startPos_655_);
v___x_671_ = lean_string_is_valid_pos(v_str_654_, v_stopPos_656_);
if (v___x_671_ == 0)
{
v___y_670_ = v___x_671_;
goto v___jp_669_;
}
else
{
uint8_t v___x_672_; 
v___x_672_ = lean_nat_dec_le(v_startPos_655_, v_stopPos_656_);
v___y_670_ = v___x_672_;
goto v___jp_669_;
}
v___jp_661_:
{
if (v___y_662_ == 0)
{
lean_object* v___x_663_; lean_object* v___x_664_; 
lean_del_object(v___x_658_);
lean_dec(v_stopPos_656_);
lean_dec(v_startPos_655_);
lean_dec_ref(v_str_654_);
v___x_663_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_664_ = l_panic___redArg(v___x_660_, v___x_663_);
v___y_650_ = v___x_664_;
goto v___jp_649_;
}
else
{
lean_object* v___x_666_; 
if (v_isShared_659_ == 0)
{
v___x_666_ = v___x_658_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_str_654_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v_startPos_655_);
lean_ctor_set(v_reuseFailAlloc_667_, 2, v_stopPos_656_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
v___y_650_ = v___x_666_;
goto v___jp_649_;
}
}
}
v___jp_669_:
{
if (v___x_668_ == 0)
{
v___y_662_ = v___x_668_;
goto v___jp_661_;
}
else
{
v___y_662_ = v___y_670_;
goto v___jp_661_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_any___lam__0(lean_object* v___x_674_, lean_object* v_s_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(v_s_675_, v___x_674_, v___y_676_, lean_box(0), lean_box(0), v___y_679_, v___y_680_, v___y_681_);
return v___x_682_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_any(lean_object* v_s_683_, lean_object* v_p_684_){
_start:
{
lean_object* v___x_685_; lean_object* v_str_686_; lean_object* v_startPos_687_; lean_object* v_stopPos_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_709_; 
lean_inc_ref(v_p_684_);
v___x_685_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v_p_684_);
v_str_686_ = lean_ctor_get(v_s_683_, 0);
v_startPos_687_ = lean_ctor_get(v_s_683_, 1);
v_stopPos_688_ = lean_ctor_get(v_s_683_, 2);
v_isSharedCheck_709_ = !lean_is_exclusive(v_s_683_);
if (v_isSharedCheck_709_ == 0)
{
v___x_690_ = v_s_683_;
v_isShared_691_ = v_isSharedCheck_709_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_stopPos_688_);
lean_inc(v_startPos_687_);
lean_inc(v_str_686_);
lean_dec(v_s_683_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_709_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_692_; lean_object* v___f_693_; lean_object* v___x_694_; uint8_t v___y_696_; uint8_t v___x_704_; uint8_t v___y_706_; uint8_t v___x_707_; 
v___x_692_ = l_String_instInhabitedSlice;
v___f_693_ = lean_alloc_closure((void*)(l_Substring_Raw_any___lam__0), 8, 1);
lean_closure_set(v___f_693_, 0, v___x_685_);
v___x_694_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_694_, 0, lean_box(0));
lean_closure_set(v___x_694_, 1, v_p_684_);
v___x_704_ = lean_string_is_valid_pos(v_str_686_, v_startPos_687_);
v___x_707_ = lean_string_is_valid_pos(v_str_686_, v_stopPos_688_);
if (v___x_707_ == 0)
{
v___y_706_ = v___x_707_;
goto v___jp_705_;
}
else
{
uint8_t v___x_708_; 
v___x_708_ = lean_nat_dec_le(v_startPos_687_, v_stopPos_688_);
v___y_706_ = v___x_708_;
goto v___jp_705_;
}
v___jp_695_:
{
if (v___y_696_ == 0)
{
lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
lean_del_object(v___x_690_);
lean_dec(v_stopPos_688_);
lean_dec(v_startPos_687_);
lean_dec_ref(v_str_686_);
v___x_697_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_698_ = l_panic___redArg(v___x_692_, v___x_697_);
v___x_699_ = l_String_Slice_contains___redArg(v___f_693_, v___x_698_, v___x_694_);
return v___x_699_;
}
else
{
lean_object* v___x_701_; 
if (v_isShared_691_ == 0)
{
v___x_701_ = v___x_690_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_str_686_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v_startPos_687_);
lean_ctor_set(v_reuseFailAlloc_703_, 2, v_stopPos_688_);
v___x_701_ = v_reuseFailAlloc_703_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
uint8_t v___x_702_; 
v___x_702_ = l_String_Slice_contains___redArg(v___f_693_, v___x_701_, v___x_694_);
return v___x_702_;
}
}
}
v___jp_705_:
{
if (v___x_704_ == 0)
{
v___y_696_ = v___x_704_;
goto v___jp_695_;
}
else
{
v___y_696_ = v___y_706_;
goto v___jp_695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_any___boxed(lean_object* v_s_710_, lean_object* v_p_711_){
_start:
{
uint8_t v_res_712_; lean_object* v_r_713_; 
v_res_712_ = l_Substring_Raw_any(v_s_710_, v_p_711_);
v_r_713_ = lean_box(v_res_712_);
return v_r_713_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_all(lean_object* v_s_714_, lean_object* v_p_715_){
_start:
{
lean_object* v___y_717_; lean_object* v_startInclusive_718_; lean_object* v_endExclusive_719_; lean_object* v_str_725_; lean_object* v_startPos_726_; lean_object* v_stopPos_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_746_; 
v_str_725_ = lean_ctor_get(v_s_714_, 0);
v_startPos_726_ = lean_ctor_get(v_s_714_, 1);
v_stopPos_727_ = lean_ctor_get(v_s_714_, 2);
v_isSharedCheck_746_ = !lean_is_exclusive(v_s_714_);
if (v_isSharedCheck_746_ == 0)
{
v___x_729_ = v_s_714_;
v_isShared_730_ = v_isSharedCheck_746_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_stopPos_727_);
lean_inc(v_startPos_726_);
lean_inc(v_str_725_);
lean_dec(v_s_714_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_746_;
goto v_resetjp_728_;
}
v___jp_716_:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v_decide_724_; 
v___x_720_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v_p_715_);
v___x_721_ = lean_unsigned_to_nat(0u);
v___x_722_ = l_String_Slice_Pos_skipWhile___redArg(v___y_717_, v___x_721_, v___x_720_);
lean_dec_ref(v___y_717_);
v___x_723_ = lean_nat_sub(v_endExclusive_719_, v_startInclusive_718_);
lean_dec(v_startInclusive_718_);
lean_dec(v_endExclusive_719_);
v_decide_724_ = lean_nat_dec_eq(v___x_722_, v___x_723_);
lean_dec(v___x_723_);
lean_dec(v___x_722_);
return v_decide_724_;
}
v_resetjp_728_:
{
lean_object* v___x_731_; uint8_t v___y_733_; uint8_t v___x_741_; uint8_t v___y_743_; uint8_t v___x_744_; 
v___x_731_ = l_String_instInhabitedSlice;
v___x_741_ = lean_string_is_valid_pos(v_str_725_, v_startPos_726_);
v___x_744_ = lean_string_is_valid_pos(v_str_725_, v_stopPos_727_);
if (v___x_744_ == 0)
{
v___y_743_ = v___x_744_;
goto v___jp_742_;
}
else
{
uint8_t v___x_745_; 
v___x_745_ = lean_nat_dec_le(v_startPos_726_, v_stopPos_727_);
v___y_743_ = v___x_745_;
goto v___jp_742_;
}
v___jp_732_:
{
if (v___y_733_ == 0)
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v_startInclusive_736_; lean_object* v_endExclusive_737_; 
lean_del_object(v___x_729_);
lean_dec(v_stopPos_727_);
lean_dec(v_startPos_726_);
lean_dec_ref(v_str_725_);
v___x_734_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_735_ = l_panic___redArg(v___x_731_, v___x_734_);
v_startInclusive_736_ = lean_ctor_get(v___x_735_, 1);
lean_inc(v_startInclusive_736_);
v_endExclusive_737_ = lean_ctor_get(v___x_735_, 2);
lean_inc(v_endExclusive_737_);
v___y_717_ = v___x_735_;
v_startInclusive_718_ = v_startInclusive_736_;
v_endExclusive_719_ = v_endExclusive_737_;
goto v___jp_716_;
}
else
{
lean_object* v___x_739_; 
lean_inc(v_stopPos_727_);
lean_inc(v_startPos_726_);
if (v_isShared_730_ == 0)
{
v___x_739_ = v___x_729_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_str_725_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v_startPos_726_);
lean_ctor_set(v_reuseFailAlloc_740_, 2, v_stopPos_727_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
v___y_717_ = v___x_739_;
v_startInclusive_718_ = v_startPos_726_;
v_endExclusive_719_ = v_stopPos_727_;
goto v___jp_716_;
}
}
}
v___jp_742_:
{
if (v___x_741_ == 0)
{
v___y_733_ = v___x_741_;
goto v___jp_732_;
}
else
{
v___y_733_ = v___y_743_;
goto v___jp_732_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_all___boxed(lean_object* v_s_747_, lean_object* v_p_748_){
_start:
{
uint8_t v_res_749_; lean_object* v_r_750_; 
v_res_749_ = l_Substring_Raw_all(v_s_747_, v_p_748_);
v_r_750_ = lean_box(v_res_749_);
return v_r_750_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(lean_object* v_msg_751_){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = l_String_instInhabitedSlice;
v___x_753_ = lean_panic_fn_borrowed(v___x_752_, v_msg_751_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0(lean_object* v_p_754_, lean_object* v_s_755_, lean_object* v_pos_756_){
_start:
{
lean_object* v_str_757_; lean_object* v_startInclusive_758_; lean_object* v_endExclusive_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; uint8_t v_decide_763_; 
v_str_757_ = lean_ctor_get(v_s_755_, 0);
v_startInclusive_758_ = lean_ctor_get(v_s_755_, 1);
v_endExclusive_759_ = lean_ctor_get(v_s_755_, 2);
v___x_760_ = lean_nat_add(v_startInclusive_758_, v_pos_756_);
v___x_761_ = lean_unsigned_to_nat(0u);
v___x_762_ = lean_nat_sub(v_endExclusive_759_, v___x_760_);
v_decide_763_ = lean_nat_dec_eq(v___x_761_, v___x_762_);
lean_dec(v___x_762_);
if (v_decide_763_ == 0)
{
uint32_t v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_764_ = lean_string_utf8_get_fast(v_str_757_, v___x_760_);
v___x_765_ = lean_box_uint32(v___x_764_);
lean_inc_ref(v_p_754_);
v___x_766_ = lean_apply_1(v_p_754_, v___x_765_);
v___x_767_ = lean_unbox(v___x_766_);
if (v___x_767_ == 0)
{
lean_dec(v___x_760_);
lean_dec_ref(v_p_754_);
return v_pos_756_;
}
else
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_768_ = lean_string_utf8_next_fast(v_str_757_, v___x_760_);
v___x_769_ = lean_nat_sub(v___x_768_, v___x_760_);
lean_dec(v___x_760_);
v___x_770_ = lean_nat_add(v_pos_756_, v___x_769_);
lean_dec(v___x_769_);
v___x_771_ = lean_unsigned_to_nat(1u);
v___x_772_ = lean_nat_add(v_pos_756_, v___x_771_);
v___x_773_ = lean_nat_dec_le(v___x_772_, v___x_770_);
lean_dec(v___x_772_);
if (v___x_773_ == 0)
{
lean_dec(v___x_770_);
lean_dec_ref(v_p_754_);
return v_pos_756_;
}
else
{
lean_dec(v_pos_756_);
v_pos_756_ = v___x_770_;
goto _start;
}
}
}
else
{
lean_dec(v___x_760_);
lean_dec_ref(v_p_754_);
return v_pos_756_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0___boxed(lean_object* v_p_775_, lean_object* v_s_776_, lean_object* v_pos_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0(v_p_775_, v_s_776_, v_pos_777_);
lean_dec_ref(v_s_776_);
return v_res_778_;
}
}
LEAN_EXPORT uint8_t lean_substring_all(lean_object* v_s_779_, lean_object* v_p_780_){
_start:
{
lean_object* v___y_782_; lean_object* v_startInclusive_783_; lean_object* v_endExclusive_784_; lean_object* v_str_789_; lean_object* v_startPos_790_; lean_object* v_stopPos_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_809_; 
v_str_789_ = lean_ctor_get(v_s_779_, 0);
v_startPos_790_ = lean_ctor_get(v_s_779_, 1);
v_stopPos_791_ = lean_ctor_get(v_s_779_, 2);
v_isSharedCheck_809_ = !lean_is_exclusive(v_s_779_);
if (v_isSharedCheck_809_ == 0)
{
v___x_793_ = v_s_779_;
v_isShared_794_ = v_isSharedCheck_809_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_stopPos_791_);
lean_inc(v_startPos_790_);
lean_inc(v_str_789_);
lean_dec(v_s_779_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_809_;
goto v_resetjp_792_;
}
v___jp_781_:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; uint8_t v_decide_788_; 
v___x_785_ = lean_unsigned_to_nat(0u);
v___x_786_ = l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0(v_p_780_, v___y_782_, v___x_785_);
lean_dec_ref(v___y_782_);
v___x_787_ = lean_nat_sub(v_endExclusive_784_, v_startInclusive_783_);
lean_dec(v_startInclusive_783_);
lean_dec(v_endExclusive_784_);
v_decide_788_ = lean_nat_dec_eq(v___x_786_, v___x_787_);
lean_dec(v___x_787_);
lean_dec(v___x_786_);
return v_decide_788_;
}
v_resetjp_792_:
{
uint8_t v___y_796_; uint8_t v___x_804_; uint8_t v___y_806_; uint8_t v___x_807_; 
v___x_804_ = lean_string_is_valid_pos(v_str_789_, v_startPos_790_);
v___x_807_ = lean_string_is_valid_pos(v_str_789_, v_stopPos_791_);
if (v___x_807_ == 0)
{
v___y_806_ = v___x_807_;
goto v___jp_805_;
}
else
{
uint8_t v___x_808_; 
v___x_808_ = lean_nat_dec_le(v_startPos_790_, v_stopPos_791_);
v___y_806_ = v___x_808_;
goto v___jp_805_;
}
v___jp_795_:
{
if (v___y_796_ == 0)
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v_startInclusive_799_; lean_object* v_endExclusive_800_; 
lean_del_object(v___x_793_);
lean_dec(v_stopPos_791_);
lean_dec(v_startPos_790_);
lean_dec_ref(v_str_789_);
v___x_797_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_798_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_797_);
v_startInclusive_799_ = lean_ctor_get(v___x_798_, 1);
lean_inc(v_startInclusive_799_);
v_endExclusive_800_ = lean_ctor_get(v___x_798_, 2);
lean_inc(v_endExclusive_800_);
v___y_782_ = v___x_798_;
v_startInclusive_783_ = v_startInclusive_799_;
v_endExclusive_784_ = v_endExclusive_800_;
goto v___jp_781_;
}
else
{
lean_object* v___x_802_; 
lean_inc(v_stopPos_791_);
lean_inc(v_startPos_790_);
if (v_isShared_794_ == 0)
{
v___x_802_ = v___x_793_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_str_789_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v_startPos_790_);
lean_ctor_set(v_reuseFailAlloc_803_, 2, v_stopPos_791_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
v___y_782_ = v___x_802_;
v_startInclusive_783_ = v_startPos_790_;
v_endExclusive_784_ = v_stopPos_791_;
goto v___jp_781_;
}
}
}
v___jp_805_:
{
if (v___x_804_ == 0)
{
v___y_796_ = v___x_804_;
goto v___jp_795_;
}
else
{
v___y_796_ = v___y_806_;
goto v___jp_795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_allImpl___boxed(lean_object* v_s_810_, lean_object* v_p_811_){
_start:
{
uint8_t v_res_812_; lean_object* v_r_813_; 
v_res_812_ = lean_substring_all(v_s_810_, v_p_811_);
v_r_813_ = lean_box(v_res_812_);
return v_r_813_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_contains___lam__0(uint32_t v_c_814_, uint32_t v_a_815_){
_start:
{
uint8_t v___x_816_; 
v___x_816_ = lean_uint32_dec_eq(v_a_815_, v_c_814_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_contains___lam__0___boxed(lean_object* v_c_817_, lean_object* v_a_818_){
_start:
{
uint32_t v_c_boxed_819_; uint32_t v_a_boxed_820_; uint8_t v_res_821_; lean_object* v_r_822_; 
v_c_boxed_819_ = lean_unbox_uint32(v_c_817_);
lean_dec(v_c_817_);
v_a_boxed_820_ = lean_unbox_uint32(v_a_818_);
lean_dec(v_a_818_);
v_res_821_ = l_Substring_Raw_contains___lam__0(v_c_boxed_819_, v_a_boxed_820_);
v_r_822_ = lean_box(v_res_821_);
return v_r_822_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_contains(lean_object* v_s_823_, uint32_t v_c_824_){
_start:
{
lean_object* v___x_825_; lean_object* v___f_826_; lean_object* v___x_827_; lean_object* v_str_828_; lean_object* v_startPos_829_; lean_object* v_stopPos_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_851_; 
v___x_825_ = lean_box_uint32(v_c_824_);
v___f_826_ = lean_alloc_closure((void*)(l_Substring_Raw_contains___lam__0___boxed), 2, 1);
lean_closure_set(v___f_826_, 0, v___x_825_);
lean_inc_ref(v___f_826_);
v___x_827_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___f_826_);
v_str_828_ = lean_ctor_get(v_s_823_, 0);
v_startPos_829_ = lean_ctor_get(v_s_823_, 1);
v_stopPos_830_ = lean_ctor_get(v_s_823_, 2);
v_isSharedCheck_851_ = !lean_is_exclusive(v_s_823_);
if (v_isSharedCheck_851_ == 0)
{
v___x_832_ = v_s_823_;
v_isShared_833_ = v_isSharedCheck_851_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_stopPos_830_);
lean_inc(v_startPos_829_);
lean_inc(v_str_828_);
lean_dec(v_s_823_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_851_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_834_; lean_object* v___f_835_; lean_object* v___x_836_; uint8_t v___y_838_; uint8_t v___x_846_; uint8_t v___y_848_; uint8_t v___x_849_; 
v___x_834_ = l_String_instInhabitedSlice;
v___f_835_ = lean_alloc_closure((void*)(l_Substring_Raw_any___lam__0), 8, 1);
lean_closure_set(v___f_835_, 0, v___x_827_);
v___x_836_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_836_, 0, lean_box(0));
lean_closure_set(v___x_836_, 1, v___f_826_);
v___x_846_ = lean_string_is_valid_pos(v_str_828_, v_startPos_829_);
v___x_849_ = lean_string_is_valid_pos(v_str_828_, v_stopPos_830_);
if (v___x_849_ == 0)
{
v___y_848_ = v___x_849_;
goto v___jp_847_;
}
else
{
uint8_t v___x_850_; 
v___x_850_ = lean_nat_dec_le(v_startPos_829_, v_stopPos_830_);
v___y_848_ = v___x_850_;
goto v___jp_847_;
}
v___jp_837_:
{
if (v___y_838_ == 0)
{
lean_object* v___x_839_; lean_object* v___x_840_; uint8_t v___x_841_; 
lean_del_object(v___x_832_);
lean_dec(v_stopPos_830_);
lean_dec(v_startPos_829_);
lean_dec_ref(v_str_828_);
v___x_839_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_840_ = l_panic___redArg(v___x_834_, v___x_839_);
v___x_841_ = l_String_Slice_contains___redArg(v___f_835_, v___x_840_, v___x_836_);
return v___x_841_;
}
else
{
lean_object* v___x_843_; 
if (v_isShared_833_ == 0)
{
v___x_843_ = v___x_832_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_str_828_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v_startPos_829_);
lean_ctor_set(v_reuseFailAlloc_845_, 2, v_stopPos_830_);
v___x_843_ = v_reuseFailAlloc_845_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
uint8_t v___x_844_; 
v___x_844_ = l_String_Slice_contains___redArg(v___f_835_, v___x_843_, v___x_836_);
return v___x_844_;
}
}
}
v___jp_847_:
{
if (v___x_846_ == 0)
{
v___y_838_ = v___x_846_;
goto v___jp_837_;
}
else
{
v___y_838_ = v___y_848_;
goto v___jp_837_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_contains___boxed(lean_object* v_s_852_, lean_object* v_c_853_){
_start:
{
uint32_t v_c_boxed_854_; uint8_t v_res_855_; lean_object* v_r_856_; 
v_c_boxed_854_ = lean_unbox_uint32(v_c_853_);
lean_dec(v_c_853_);
v_res_855_ = l_Substring_Raw_contains(v_s_852_, v_c_boxed_854_);
v_r_856_ = lean_box(v_res_855_);
return v_r_856_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux(lean_object* v_s_857_, lean_object* v_stopPos_858_, lean_object* v_p_859_, lean_object* v_i_860_){
_start:
{
uint8_t v___y_862_; lean_object* v___x_865_; lean_object* v___x_866_; uint8_t v___x_867_; 
v___x_865_ = lean_unsigned_to_nat(1u);
v___x_866_ = lean_nat_add(v_i_860_, v___x_865_);
v___x_867_ = lean_nat_dec_le(v___x_866_, v_stopPos_858_);
lean_dec(v___x_866_);
if (v___x_867_ == 0)
{
lean_dec_ref(v_p_859_);
return v_i_860_;
}
else
{
if (v___x_867_ == 0)
{
v___y_862_ = v___x_867_;
goto v___jp_861_;
}
else
{
uint32_t v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; uint8_t v___x_871_; 
v___x_868_ = lean_string_utf8_get(v_s_857_, v_i_860_);
v___x_869_ = lean_box_uint32(v___x_868_);
lean_inc_ref(v_p_859_);
v___x_870_ = lean_apply_1(v_p_859_, v___x_869_);
v___x_871_ = lean_unbox(v___x_870_);
v___y_862_ = v___x_871_;
goto v___jp_861_;
}
}
v___jp_861_:
{
if (v___y_862_ == 0)
{
lean_dec_ref(v_p_859_);
return v_i_860_;
}
else
{
lean_object* v___x_863_; 
v___x_863_ = lean_string_utf8_next(v_s_857_, v_i_860_);
lean_dec(v_i_860_);
v_i_860_ = v___x_863_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___boxed(lean_object* v_s_872_, lean_object* v_stopPos_873_, lean_object* v_p_874_, lean_object* v_i_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Substring_Raw_takeWhileAux(v_s_872_, v_stopPos_873_, v_p_874_, v_i_875_);
lean_dec(v_stopPos_873_);
lean_dec_ref(v_s_872_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhile(lean_object* v_x_877_, lean_object* v_x_878_){
_start:
{
lean_object* v_str_879_; lean_object* v_startPos_880_; lean_object* v_stopPos_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_889_; 
v_str_879_ = lean_ctor_get(v_x_877_, 0);
v_startPos_880_ = lean_ctor_get(v_x_877_, 1);
v_stopPos_881_ = lean_ctor_get(v_x_877_, 2);
v_isSharedCheck_889_ = !lean_is_exclusive(v_x_877_);
if (v_isSharedCheck_889_ == 0)
{
v___x_883_ = v_x_877_;
v_isShared_884_ = v_isSharedCheck_889_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_stopPos_881_);
lean_inc(v_startPos_880_);
lean_inc(v_str_879_);
lean_dec(v_x_877_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_889_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v_e_885_; lean_object* v___x_887_; 
lean_inc(v_startPos_880_);
v_e_885_ = l_Substring_Raw_takeWhileAux(v_str_879_, v_stopPos_881_, v_x_878_, v_startPos_880_);
lean_dec(v_stopPos_881_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 2, v_e_885_);
v___x_887_ = v___x_883_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_str_879_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_startPos_880_);
lean_ctor_set(v_reuseFailAlloc_888_, 2, v_e_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(lean_object* v_a_890_, lean_object* v_s_891_, lean_object* v_stopPos_892_, lean_object* v_i_893_){
_start:
{
uint8_t v___y_895_; lean_object* v___x_898_; lean_object* v___x_899_; uint8_t v___x_900_; 
v___x_898_ = lean_unsigned_to_nat(1u);
v___x_899_ = lean_nat_add(v_i_893_, v___x_898_);
v___x_900_ = lean_nat_dec_le(v___x_899_, v_stopPos_892_);
lean_dec(v___x_899_);
if (v___x_900_ == 0)
{
lean_dec_ref(v_a_890_);
return v_i_893_;
}
else
{
if (v___x_900_ == 0)
{
v___y_895_ = v___x_900_;
goto v___jp_894_;
}
else
{
uint32_t v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_901_ = lean_string_utf8_get(v_s_891_, v_i_893_);
v___x_902_ = lean_box_uint32(v___x_901_);
lean_inc_ref(v_a_890_);
v___x_903_ = lean_apply_1(v_a_890_, v___x_902_);
v___x_904_ = lean_unbox(v___x_903_);
v___y_895_ = v___x_904_;
goto v___jp_894_;
}
}
v___jp_894_:
{
if (v___y_895_ == 0)
{
lean_dec_ref(v_a_890_);
return v_i_893_;
}
else
{
lean_object* v___x_896_; 
v___x_896_ = lean_string_utf8_next(v_s_891_, v_i_893_);
lean_dec(v_i_893_);
v_i_893_ = v___x_896_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0___boxed(lean_object* v_a_905_, lean_object* v_s_906_, lean_object* v_stopPos_907_, lean_object* v_i_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(v_a_905_, v_s_906_, v_stopPos_907_, v_i_908_);
lean_dec(v_stopPos_907_);
lean_dec_ref(v_s_906_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* lean_substring_takewhile(lean_object* v_a_910_, lean_object* v_a_911_){
_start:
{
lean_object* v_str_912_; lean_object* v_startPos_913_; lean_object* v_stopPos_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_922_; 
v_str_912_ = lean_ctor_get(v_a_910_, 0);
v_startPos_913_ = lean_ctor_get(v_a_910_, 1);
v_stopPos_914_ = lean_ctor_get(v_a_910_, 2);
v_isSharedCheck_922_ = !lean_is_exclusive(v_a_910_);
if (v_isSharedCheck_922_ == 0)
{
v___x_916_ = v_a_910_;
v_isShared_917_ = v_isSharedCheck_922_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_stopPos_914_);
lean_inc(v_startPos_913_);
lean_inc(v_str_912_);
lean_dec(v_a_910_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_922_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v_e_918_; lean_object* v___x_920_; 
lean_inc(v_startPos_913_);
v_e_918_ = l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(v_a_911_, v_str_912_, v_stopPos_914_, v_startPos_913_);
lean_dec(v_stopPos_914_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 2, v_e_918_);
v___x_920_ = v___x_916_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_str_912_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_startPos_913_);
lean_ctor_set(v_reuseFailAlloc_921_, 2, v_e_918_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropWhile(lean_object* v_x_923_, lean_object* v_x_924_){
_start:
{
lean_object* v_str_925_; lean_object* v_startPos_926_; lean_object* v_stopPos_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_935_; 
v_str_925_ = lean_ctor_get(v_x_923_, 0);
v_startPos_926_ = lean_ctor_get(v_x_923_, 1);
v_stopPos_927_ = lean_ctor_get(v_x_923_, 2);
v_isSharedCheck_935_ = !lean_is_exclusive(v_x_923_);
if (v_isSharedCheck_935_ == 0)
{
v___x_929_ = v_x_923_;
v_isShared_930_ = v_isSharedCheck_935_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_stopPos_927_);
lean_inc(v_startPos_926_);
lean_inc(v_str_925_);
lean_dec(v_x_923_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_935_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v_b_931_; lean_object* v___x_933_; 
v_b_931_ = l_Substring_Raw_takeWhileAux(v_str_925_, v_stopPos_927_, v_x_924_, v_startPos_926_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 1, v_b_931_);
v___x_933_ = v___x_929_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_str_925_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v_b_931_);
lean_ctor_set(v_reuseFailAlloc_934_, 2, v_stopPos_927_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux(lean_object* v_s_936_, lean_object* v_begPos_937_, lean_object* v_p_938_, lean_object* v_i_939_){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; uint8_t v___x_942_; 
v___x_940_ = lean_unsigned_to_nat(1u);
v___x_941_ = lean_nat_add(v_begPos_937_, v___x_940_);
v___x_942_ = lean_nat_dec_le(v___x_941_, v_i_939_);
lean_dec(v___x_941_);
if (v___x_942_ == 0)
{
lean_dec_ref(v_p_938_);
return v_i_939_;
}
else
{
lean_object* v_i_x27_943_; uint8_t v___y_945_; uint8_t v___y_948_; uint32_t v_c_949_; lean_object* v___x_950_; lean_object* v___x_951_; uint8_t v___x_952_; 
v_i_x27_943_ = lean_string_utf8_prev(v_s_936_, v_i_939_);
v_c_949_ = lean_string_utf8_get(v_s_936_, v_i_x27_943_);
v___x_950_ = lean_box_uint32(v_c_949_);
lean_inc_ref(v_p_938_);
v___x_951_ = lean_apply_1(v_p_938_, v___x_950_);
v___x_952_ = lean_unbox(v___x_951_);
if (v___x_952_ == 0)
{
v___y_948_ = v___x_942_;
goto v___jp_947_;
}
else
{
uint8_t v___x_953_; 
v___x_953_ = 0;
v___y_948_ = v___x_953_;
goto v___jp_947_;
}
v___jp_944_:
{
if (v___y_945_ == 0)
{
lean_dec(v_i_939_);
v_i_939_ = v_i_x27_943_;
goto _start;
}
else
{
lean_dec(v_i_x27_943_);
lean_dec_ref(v_p_938_);
return v_i_939_;
}
}
v___jp_947_:
{
if (v___x_942_ == 0)
{
v___y_945_ = v___x_942_;
goto v___jp_944_;
}
else
{
v___y_945_ = v___y_948_;
goto v___jp_944_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux___boxed(lean_object* v_s_954_, lean_object* v_begPos_955_, lean_object* v_p_956_, lean_object* v_i_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Substring_Raw_takeRightWhileAux(v_s_954_, v_begPos_955_, v_p_956_, v_i_957_);
lean_dec(v_begPos_955_);
lean_dec_ref(v_s_954_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhile(lean_object* v_x_959_, lean_object* v_x_960_){
_start:
{
lean_object* v_str_961_; lean_object* v_startPos_962_; lean_object* v_stopPos_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_971_; 
v_str_961_ = lean_ctor_get(v_x_959_, 0);
v_startPos_962_ = lean_ctor_get(v_x_959_, 1);
v_stopPos_963_ = lean_ctor_get(v_x_959_, 2);
v_isSharedCheck_971_ = !lean_is_exclusive(v_x_959_);
if (v_isSharedCheck_971_ == 0)
{
v___x_965_ = v_x_959_;
v_isShared_966_ = v_isSharedCheck_971_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_stopPos_963_);
lean_inc(v_startPos_962_);
lean_inc(v_str_961_);
lean_dec(v_x_959_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_971_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v_b_967_; lean_object* v___x_969_; 
lean_inc(v_stopPos_963_);
v_b_967_ = l_Substring_Raw_takeRightWhileAux(v_str_961_, v_startPos_962_, v_x_960_, v_stopPos_963_);
lean_dec(v_startPos_962_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 1, v_b_967_);
v___x_969_ = v___x_965_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_str_961_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v_b_967_);
lean_ctor_set(v_reuseFailAlloc_970_, 2, v_stopPos_963_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropRightWhile(lean_object* v_x_972_, lean_object* v_x_973_){
_start:
{
lean_object* v_str_974_; lean_object* v_startPos_975_; lean_object* v_stopPos_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_984_; 
v_str_974_ = lean_ctor_get(v_x_972_, 0);
v_startPos_975_ = lean_ctor_get(v_x_972_, 1);
v_stopPos_976_ = lean_ctor_get(v_x_972_, 2);
v_isSharedCheck_984_ = !lean_is_exclusive(v_x_972_);
if (v_isSharedCheck_984_ == 0)
{
v___x_978_ = v_x_972_;
v_isShared_979_ = v_isSharedCheck_984_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_stopPos_976_);
lean_inc(v_startPos_975_);
lean_inc(v_str_974_);
lean_dec(v_x_972_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_984_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v_e_980_; lean_object* v___x_982_; 
v_e_980_ = l_Substring_Raw_takeRightWhileAux(v_str_974_, v_startPos_975_, v_x_973_, v_stopPos_976_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 2, v_e_980_);
v___x_982_ = v___x_978_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_str_974_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v_startPos_975_);
lean_ctor_set(v_reuseFailAlloc_983_, 2, v_e_980_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_trimLeft(lean_object* v_s_986_){
_start:
{
lean_object* v_str_987_; lean_object* v_startPos_988_; lean_object* v_stopPos_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_998_; 
v_str_987_ = lean_ctor_get(v_s_986_, 0);
v_startPos_988_ = lean_ctor_get(v_s_986_, 1);
v_stopPos_989_ = lean_ctor_get(v_s_986_, 2);
v_isSharedCheck_998_ = !lean_is_exclusive(v_s_986_);
if (v_isSharedCheck_998_ == 0)
{
v___x_991_ = v_s_986_;
v_isShared_992_ = v_isSharedCheck_998_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_stopPos_989_);
lean_inc(v_startPos_988_);
lean_inc(v_str_987_);
lean_dec(v_s_986_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_998_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_993_; lean_object* v_b_994_; lean_object* v___x_996_; 
v___x_993_ = ((lean_object*)(l_Substring_Raw_trimLeft___closed__0));
v_b_994_ = l_Substring_Raw_takeWhileAux(v_str_987_, v_stopPos_989_, v___x_993_, v_startPos_988_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 1, v_b_994_);
v___x_996_ = v___x_991_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_str_987_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_b_994_);
lean_ctor_set(v_reuseFailAlloc_997_, 2, v_stopPos_989_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_trimRight(lean_object* v_s_999_){
_start:
{
lean_object* v_str_1000_; lean_object* v_startPos_1001_; lean_object* v_stopPos_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1011_; 
v_str_1000_ = lean_ctor_get(v_s_999_, 0);
v_startPos_1001_ = lean_ctor_get(v_s_999_, 1);
v_stopPos_1002_ = lean_ctor_get(v_s_999_, 2);
v_isSharedCheck_1011_ = !lean_is_exclusive(v_s_999_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1004_ = v_s_999_;
v_isShared_1005_ = v_isSharedCheck_1011_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_stopPos_1002_);
lean_inc(v_startPos_1001_);
lean_inc(v_str_1000_);
lean_dec(v_s_999_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1011_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1006_; lean_object* v_e_1007_; lean_object* v___x_1009_; 
v___x_1006_ = ((lean_object*)(l_Substring_Raw_trimLeft___closed__0));
v_e_1007_ = l_Substring_Raw_takeRightWhileAux(v_str_1000_, v_startPos_1001_, v___x_1006_, v_stopPos_1002_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 2, v_e_1007_);
v___x_1009_ = v___x_1004_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_str_1000_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v_startPos_1001_);
lean_ctor_set(v_reuseFailAlloc_1010_, 2, v_e_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_trim(lean_object* v_x_1012_){
_start:
{
lean_object* v_str_1013_; lean_object* v_startPos_1014_; lean_object* v_stopPos_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1025_; 
v_str_1013_ = lean_ctor_get(v_x_1012_, 0);
v_startPos_1014_ = lean_ctor_get(v_x_1012_, 1);
v_stopPos_1015_ = lean_ctor_get(v_x_1012_, 2);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_x_1012_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1017_ = v_x_1012_;
v_isShared_1018_ = v_isSharedCheck_1025_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_stopPos_1015_);
lean_inc(v_startPos_1014_);
lean_inc(v_str_1013_);
lean_dec(v_x_1012_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1025_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1019_; lean_object* v_b_1020_; lean_object* v_e_1021_; lean_object* v___x_1023_; 
v___x_1019_ = ((lean_object*)(l_Substring_Raw_trimLeft___closed__0));
v_b_1020_ = l_Substring_Raw_takeWhileAux(v_str_1013_, v_stopPos_1015_, v___x_1019_, v_startPos_1014_);
v_e_1021_ = l_Substring_Raw_takeRightWhileAux(v_str_1013_, v_b_1020_, v___x_1019_, v_stopPos_1015_);
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 2, v_e_1021_);
lean_ctor_set(v___x_1017_, 1, v_b_1020_);
v___x_1023_ = v___x_1017_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_str_1013_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v_b_1020_);
lean_ctor_set(v_reuseFailAlloc_1024_, 2, v_e_1021_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___lam__0(lean_object* v___y_1026_, uint8_t v___x_1027_, uint8_t v___x_1028_, lean_object* v_it_1029_, lean_object* v_acc_1030_, lean_object* v_hP_1031_, lean_object* v_recur_1032_){
_start:
{
lean_object* v_str_1033_; lean_object* v_startInclusive_1034_; lean_object* v_endExclusive_1035_; lean_object* v___x_1036_; uint8_t v_decide_1037_; 
v_str_1033_ = lean_ctor_get(v___y_1026_, 0);
v_startInclusive_1034_ = lean_ctor_get(v___y_1026_, 1);
v_endExclusive_1035_ = lean_ctor_get(v___y_1026_, 2);
v___x_1036_ = lean_nat_sub(v_endExclusive_1035_, v_startInclusive_1034_);
v_decide_1037_ = lean_nat_dec_eq(v_it_1029_, v___x_1036_);
lean_dec(v___x_1036_);
if (v_decide_1037_ == 0)
{
lean_object* v_snd_1038_; lean_object* v_snd_1039_; lean_object* v_fst_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1100_; 
v_snd_1038_ = lean_ctor_get(v_acc_1030_, 1);
lean_inc(v_snd_1038_);
v_snd_1039_ = lean_ctor_get(v_snd_1038_, 1);
lean_inc(v_snd_1039_);
v_fst_1040_ = lean_ctor_get(v_acc_1030_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_acc_1030_);
if (v_isSharedCheck_1100_ == 0)
{
lean_object* v_unused_1101_; 
v_unused_1101_ = lean_ctor_get(v_acc_1030_, 1);
lean_dec(v_unused_1101_);
v___x_1042_ = v_acc_1030_;
v_isShared_1043_ = v_isSharedCheck_1100_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_fst_1040_);
lean_dec(v_acc_1030_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1100_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v_fst_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1098_; 
v_fst_1044_ = lean_ctor_get(v_snd_1038_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v_snd_1038_);
if (v_isSharedCheck_1098_ == 0)
{
lean_object* v_unused_1099_; 
v_unused_1099_ = lean_ctor_get(v_snd_1038_, 1);
lean_dec(v_unused_1099_);
v___x_1046_ = v_snd_1038_;
v_isShared_1047_ = v_isSharedCheck_1098_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_fst_1044_);
lean_dec(v_snd_1038_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1098_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v_snd_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1096_; 
v_snd_1048_ = lean_ctor_get(v_snd_1039_, 1);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_snd_1039_);
if (v_isSharedCheck_1096_ == 0)
{
lean_object* v_unused_1097_; 
v_unused_1097_ = lean_ctor_get(v_snd_1039_, 0);
lean_dec(v_unused_1097_);
v___x_1050_ = v_snd_1039_;
v_isShared_1051_ = v_isSharedCheck_1096_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_snd_1048_);
lean_dec(v_snd_1039_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1096_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1052_; uint32_t v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; uint8_t v___y_1057_; uint8_t v___y_1058_; uint8_t v___y_1076_; uint8_t v___y_1077_; uint8_t v___y_1082_; uint8_t v___y_1083_; uint8_t v___y_1088_; uint32_t v___x_1092_; uint8_t v___x_1093_; 
v___x_1052_ = lean_nat_add(v_startInclusive_1034_, v_it_1029_);
v___x_1053_ = lean_string_utf8_get_fast(v_str_1033_, v___x_1052_);
v___x_1054_ = lean_string_utf8_next_fast(v_str_1033_, v___x_1052_);
lean_dec(v___x_1052_);
v___x_1055_ = lean_nat_sub(v___x_1054_, v_startInclusive_1034_);
v___x_1092_ = 48;
v___x_1093_ = lean_uint32_dec_le(v___x_1092_, v___x_1053_);
if (v___x_1093_ == 0)
{
v___y_1088_ = v___x_1093_;
goto v___jp_1087_;
}
else
{
uint32_t v___x_1094_; uint8_t v___x_1095_; 
v___x_1094_ = 57;
v___x_1095_ = lean_uint32_dec_le(v___x_1053_, v___x_1094_);
v___y_1088_ = v___x_1095_;
goto v___jp_1087_;
}
v___jp_1056_:
{
uint32_t v___x_1059_; uint8_t v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1064_; 
v___x_1059_ = 95;
v___x_1060_ = lean_uint32_dec_eq(v___x_1053_, v___x_1059_);
v___x_1061_ = lean_box(v___y_1057_);
v___x_1062_ = lean_box(v___y_1058_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 1, v___x_1062_);
lean_ctor_set(v___x_1050_, 0, v___x_1061_);
v___x_1064_ = v___x_1050_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1061_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v___x_1062_);
v___x_1064_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
lean_object* v___x_1065_; lean_object* v___x_1067_; 
v___x_1065_ = lean_box(v___x_1060_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 1, v___x_1064_);
lean_ctor_set(v___x_1046_, 0, v___x_1065_);
v___x_1067_ = v___x_1046_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1065_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v___x_1064_);
v___x_1067_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v___x_1068_; lean_object* v___x_1070_; 
v___x_1068_ = lean_box(v___x_1027_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 1, v___x_1067_);
lean_ctor_set(v___x_1042_, 0, v___x_1068_);
v___x_1070_ = v___x_1042_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v___x_1067_);
v___x_1070_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
lean_object* v___x_1071_; 
v___x_1071_ = lean_apply_4(v_recur_1032_, v___x_1055_, v___x_1070_, lean_box(0), lean_box(0));
return v___x_1071_;
}
}
}
}
v___jp_1075_:
{
uint8_t v___x_1078_; 
v___x_1078_ = lean_unbox(v_fst_1044_);
lean_dec(v_fst_1044_);
if (v___x_1078_ == 0)
{
v___y_1057_ = v___y_1076_;
v___y_1058_ = v___y_1077_;
goto v___jp_1056_;
}
else
{
uint32_t v___x_1079_; uint8_t v___x_1080_; 
v___x_1079_ = 95;
v___x_1080_ = lean_uint32_dec_eq(v___x_1053_, v___x_1079_);
if (v___x_1080_ == 0)
{
v___y_1057_ = v___y_1076_;
v___y_1058_ = v___y_1077_;
goto v___jp_1056_;
}
else
{
v___y_1057_ = v___y_1076_;
v___y_1058_ = v___x_1027_;
goto v___jp_1056_;
}
}
}
v___jp_1081_:
{
uint8_t v___x_1084_; 
v___x_1084_ = lean_unbox(v_fst_1040_);
lean_dec(v_fst_1040_);
if (v___x_1084_ == 0)
{
v___y_1076_ = v___y_1082_;
v___y_1077_ = v___y_1083_;
goto v___jp_1075_;
}
else
{
uint32_t v___x_1085_; uint8_t v___x_1086_; 
v___x_1085_ = 95;
v___x_1086_ = lean_uint32_dec_eq(v___x_1053_, v___x_1085_);
if (v___x_1086_ == 0)
{
v___y_1076_ = v___y_1082_;
v___y_1077_ = v___y_1083_;
goto v___jp_1075_;
}
else
{
lean_dec(v_fst_1044_);
v___y_1057_ = v___y_1082_;
v___y_1058_ = v___x_1027_;
goto v___jp_1056_;
}
}
}
v___jp_1087_:
{
uint8_t v___x_1089_; 
v___x_1089_ = lean_unbox(v_snd_1048_);
lean_dec(v_snd_1048_);
if (v___x_1089_ == 0)
{
lean_dec(v_fst_1044_);
lean_dec(v_fst_1040_);
v___y_1057_ = v___y_1088_;
v___y_1058_ = v___x_1027_;
goto v___jp_1056_;
}
else
{
if (v___y_1088_ == 0)
{
uint32_t v___x_1090_; uint8_t v___x_1091_; 
v___x_1090_ = 95;
v___x_1091_ = lean_uint32_dec_eq(v___x_1053_, v___x_1090_);
if (v___x_1091_ == 0)
{
lean_dec(v_fst_1044_);
lean_dec(v_fst_1040_);
v___y_1057_ = v___y_1088_;
v___y_1058_ = v___x_1027_;
goto v___jp_1056_;
}
else
{
v___y_1082_ = v___y_1088_;
v___y_1083_ = v___x_1091_;
goto v___jp_1081_;
}
}
else
{
v___y_1082_ = v___y_1088_;
v___y_1083_ = v___x_1028_;
goto v___jp_1081_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_recur_1032_);
return v_acc_1030_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___lam__0___boxed(lean_object* v___y_1102_, lean_object* v___x_1103_, lean_object* v___x_1104_, lean_object* v_it_1105_, lean_object* v_acc_1106_, lean_object* v_hP_1107_, lean_object* v_recur_1108_){
_start:
{
uint8_t v___x_829__boxed_1109_; uint8_t v___x_830__boxed_1110_; lean_object* v_res_1111_; 
v___x_829__boxed_1109_ = lean_unbox(v___x_1103_);
v___x_830__boxed_1110_ = lean_unbox(v___x_1104_);
v_res_1111_ = l_Substring_Raw_isNat___lam__0(v___y_1102_, v___x_829__boxed_1109_, v___x_830__boxed_1110_, v_it_1105_, v_acc_1106_, v_hP_1107_, v_recur_1108_);
lean_dec(v_it_1105_);
lean_dec_ref(v___y_1102_);
return v_res_1111_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_isNat(lean_object* v_s_1112_){
_start:
{
lean_object* v_str_1113_; lean_object* v_startPos_1114_; lean_object* v_stopPos_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1156_; 
v_str_1113_ = lean_ctor_get(v_s_1112_, 0);
v_startPos_1114_ = lean_ctor_get(v_s_1112_, 1);
v_stopPos_1115_ = lean_ctor_get(v_s_1112_, 2);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_s_1112_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1117_ = v_s_1112_;
v_isShared_1118_ = v_isSharedCheck_1156_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_stopPos_1115_);
lean_inc(v_startPos_1114_);
lean_inc(v_str_1113_);
lean_dec(v_s_1112_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1156_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; uint8_t v___x_1121_; 
v___x_1119_ = lean_nat_sub(v_stopPos_1115_, v_startPos_1114_);
v___x_1120_ = lean_unsigned_to_nat(0u);
v___x_1121_ = lean_nat_dec_eq(v___x_1119_, v___x_1120_);
lean_dec(v___x_1119_);
if (v___x_1121_ == 0)
{
uint8_t v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___y_1131_; lean_object* v___x_1142_; uint8_t v___y_1144_; uint8_t v___x_1150_; uint8_t v___y_1152_; uint8_t v___x_1153_; 
v___x_1122_ = 1;
v___x_1123_ = lean_box(v___x_1121_);
v___x_1124_ = lean_box(v___x_1122_);
v___x_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1123_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
v___x_1126_ = lean_box(v___x_1121_);
v___x_1127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1126_);
lean_ctor_set(v___x_1127_, 1, v___x_1125_);
v___x_1128_ = lean_box(v___x_1122_);
v___x_1129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
lean_ctor_set(v___x_1129_, 1, v___x_1127_);
v___x_1142_ = l_String_instInhabitedSlice;
v___x_1150_ = lean_string_is_valid_pos(v_str_1113_, v_startPos_1114_);
v___x_1153_ = lean_string_is_valid_pos(v_str_1113_, v_stopPos_1115_);
if (v___x_1153_ == 0)
{
v___y_1152_ = v___x_1153_;
goto v___jp_1151_;
}
else
{
uint8_t v___x_1154_; 
v___x_1154_ = lean_nat_dec_le(v_startPos_1114_, v_stopPos_1115_);
v___y_1152_ = v___x_1154_;
goto v___jp_1151_;
}
v___jp_1130_:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___f_1134_; lean_object* v___x_1135_; lean_object* v_snd_1136_; lean_object* v_snd_1137_; lean_object* v_snd_1138_; uint8_t v___x_1139_; 
v___x_1132_ = lean_box(v___x_1121_);
v___x_1133_ = lean_box(v___x_1122_);
v___f_1134_ = lean_alloc_closure((void*)(l_Substring_Raw_isNat___lam__0___boxed), 7, 3);
lean_closure_set(v___f_1134_, 0, v___y_1131_);
lean_closure_set(v___f_1134_, 1, v___x_1132_);
lean_closure_set(v___f_1134_, 2, v___x_1133_);
v___x_1135_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1134_, v___x_1120_, v___x_1129_, lean_box(0));
v_snd_1136_ = lean_ctor_get(v___x_1135_, 1);
lean_inc(v_snd_1136_);
lean_dec(v___x_1135_);
v_snd_1137_ = lean_ctor_get(v_snd_1136_, 1);
lean_inc(v_snd_1137_);
lean_dec(v_snd_1136_);
v_snd_1138_ = lean_ctor_get(v_snd_1137_, 1);
v___x_1139_ = lean_unbox(v_snd_1138_);
if (v___x_1139_ == 0)
{
lean_dec(v_snd_1137_);
return v___x_1121_;
}
else
{
lean_object* v_fst_1140_; uint8_t v___x_1141_; 
v_fst_1140_ = lean_ctor_get(v_snd_1137_, 0);
lean_inc(v_fst_1140_);
lean_dec(v_snd_1137_);
v___x_1141_ = lean_unbox(v_fst_1140_);
lean_dec(v_fst_1140_);
return v___x_1141_;
}
}
v___jp_1143_:
{
if (v___y_1144_ == 0)
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
lean_del_object(v___x_1117_);
lean_dec(v_stopPos_1115_);
lean_dec(v_startPos_1114_);
lean_dec_ref(v_str_1113_);
v___x_1145_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_1146_ = l_panic___redArg(v___x_1142_, v___x_1145_);
v___y_1131_ = v___x_1146_;
goto v___jp_1130_;
}
else
{
lean_object* v___x_1148_; 
if (v_isShared_1118_ == 0)
{
v___x_1148_ = v___x_1117_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_str_1113_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_startPos_1114_);
lean_ctor_set(v_reuseFailAlloc_1149_, 2, v_stopPos_1115_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
v___y_1131_ = v___x_1148_;
goto v___jp_1130_;
}
}
}
v___jp_1151_:
{
if (v___x_1150_ == 0)
{
v___y_1144_ = v___x_1150_;
goto v___jp_1143_;
}
else
{
v___y_1144_ = v___y_1152_;
goto v___jp_1143_;
}
}
}
else
{
uint8_t v___x_1155_; 
lean_del_object(v___x_1117_);
lean_dec(v_stopPos_1115_);
lean_dec(v_startPos_1114_);
lean_dec_ref(v_str_1113_);
v___x_1155_ = 0;
return v___x_1155_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___boxed(lean_object* v_s_1157_){
_start:
{
uint8_t v_res_1158_; lean_object* v_r_1159_; 
v_res_1158_ = l_Substring_Raw_isNat(v_s_1157_);
v_r_1159_ = lean_box(v_res_1158_);
return v_r_1159_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(lean_object* v___y_1160_, lean_object* v_a_1161_, lean_object* v_b_1162_){
_start:
{
lean_object* v_str_1163_; lean_object* v_startInclusive_1164_; lean_object* v_endExclusive_1165_; lean_object* v___x_1166_; uint8_t v_decide_1167_; 
v_str_1163_ = lean_ctor_get(v___y_1160_, 0);
v_startInclusive_1164_ = lean_ctor_get(v___y_1160_, 1);
v_endExclusive_1165_ = lean_ctor_get(v___y_1160_, 2);
v___x_1166_ = lean_nat_sub(v_endExclusive_1165_, v_startInclusive_1164_);
v_decide_1167_ = lean_nat_dec_eq(v_a_1161_, v___x_1166_);
lean_dec(v___x_1166_);
if (v_decide_1167_ == 0)
{
lean_object* v___x_1168_; uint32_t v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; uint32_t v___x_1172_; uint8_t v___x_1173_; 
v___x_1168_ = lean_nat_add(v_startInclusive_1164_, v_a_1161_);
lean_dec(v_a_1161_);
v___x_1169_ = lean_string_utf8_get_fast(v_str_1163_, v___x_1168_);
v___x_1170_ = lean_string_utf8_next_fast(v_str_1163_, v___x_1168_);
lean_dec(v___x_1168_);
v___x_1171_ = lean_nat_sub(v___x_1170_, v_startInclusive_1164_);
v___x_1172_ = 95;
v___x_1173_ = lean_uint32_dec_eq(v___x_1169_, v___x_1172_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1174_ = lean_unsigned_to_nat(10u);
v___x_1175_ = lean_nat_mul(v_b_1162_, v___x_1174_);
lean_dec(v_b_1162_);
v___x_1176_ = lean_uint32_to_nat(v___x_1169_);
v___x_1177_ = lean_unsigned_to_nat(48u);
v___x_1178_ = lean_nat_sub(v___x_1176_, v___x_1177_);
lean_dec(v___x_1176_);
v___x_1179_ = lean_nat_add(v___x_1175_, v___x_1178_);
lean_dec(v___x_1178_);
lean_dec(v___x_1175_);
v_a_1161_ = v___x_1171_;
v_b_1162_ = v___x_1179_;
goto _start;
}
else
{
v_a_1161_ = v___x_1171_;
goto _start;
}
}
else
{
lean_dec(v_a_1161_);
return v_b_1162_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg___boxed(lean_object* v___y_1182_, lean_object* v_a_1183_, lean_object* v_b_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(v___y_1182_, v_a_1183_, v_b_1184_);
lean_dec_ref(v___y_1182_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(lean_object* v___x_1186_, lean_object* v___y_1187_, lean_object* v_a_1188_, lean_object* v_b_1189_){
_start:
{
lean_object* v_str_1190_; lean_object* v_startInclusive_1191_; lean_object* v_endExclusive_1192_; lean_object* v___x_1193_; uint8_t v_decide_1194_; 
v_str_1190_ = lean_ctor_get(v___y_1187_, 0);
v_startInclusive_1191_ = lean_ctor_get(v___y_1187_, 1);
v_endExclusive_1192_ = lean_ctor_get(v___y_1187_, 2);
v___x_1193_ = lean_nat_sub(v_endExclusive_1192_, v_startInclusive_1191_);
v_decide_1194_ = lean_nat_dec_eq(v_a_1188_, v___x_1193_);
lean_dec(v___x_1193_);
if (v_decide_1194_ == 0)
{
lean_object* v_snd_1195_; lean_object* v_snd_1196_; lean_object* v_fst_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1260_; 
v_snd_1195_ = lean_ctor_get(v_b_1189_, 1);
lean_inc(v_snd_1195_);
v_snd_1196_ = lean_ctor_get(v_snd_1195_, 1);
lean_inc(v_snd_1196_);
v_fst_1197_ = lean_ctor_get(v_b_1189_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v_b_1189_);
if (v_isSharedCheck_1260_ == 0)
{
lean_object* v_unused_1261_; 
v_unused_1261_ = lean_ctor_get(v_b_1189_, 1);
lean_dec(v_unused_1261_);
v___x_1199_ = v_b_1189_;
v_isShared_1200_ = v_isSharedCheck_1260_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_fst_1197_);
lean_dec(v_b_1189_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1260_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v_fst_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1258_; 
v_fst_1201_ = lean_ctor_get(v_snd_1195_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v_snd_1195_);
if (v_isSharedCheck_1258_ == 0)
{
lean_object* v_unused_1259_; 
v_unused_1259_ = lean_ctor_get(v_snd_1195_, 1);
lean_dec(v_unused_1259_);
v___x_1203_ = v_snd_1195_;
v_isShared_1204_ = v_isSharedCheck_1258_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_fst_1201_);
lean_dec(v_snd_1195_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1258_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v_snd_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1256_; 
v_snd_1205_ = lean_ctor_get(v_snd_1196_, 1);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_snd_1196_);
if (v_isSharedCheck_1256_ == 0)
{
lean_object* v_unused_1257_; 
v_unused_1257_ = lean_ctor_get(v_snd_1196_, 0);
lean_dec(v_unused_1257_);
v___x_1207_ = v_snd_1196_;
v_isShared_1208_ = v_isSharedCheck_1256_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_snd_1205_);
lean_dec(v_snd_1196_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1256_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1209_; uint8_t v___x_1210_; uint8_t v___x_1211_; lean_object* v___x_1212_; uint32_t v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; uint8_t v___y_1217_; uint8_t v___y_1218_; uint8_t v___y_1236_; uint8_t v___y_1237_; uint8_t v___y_1242_; uint8_t v___y_1243_; uint8_t v___y_1248_; uint32_t v___x_1252_; uint8_t v___x_1253_; 
v___x_1209_ = lean_unsigned_to_nat(0u);
v___x_1210_ = lean_nat_dec_eq(v___x_1186_, v___x_1209_);
v___x_1211_ = 1;
v___x_1212_ = lean_nat_add(v_startInclusive_1191_, v_a_1188_);
lean_dec(v_a_1188_);
v___x_1213_ = lean_string_utf8_get_fast(v_str_1190_, v___x_1212_);
v___x_1214_ = lean_string_utf8_next_fast(v_str_1190_, v___x_1212_);
lean_dec(v___x_1212_);
v___x_1215_ = lean_nat_sub(v___x_1214_, v_startInclusive_1191_);
v___x_1252_ = 48;
v___x_1253_ = lean_uint32_dec_le(v___x_1252_, v___x_1213_);
if (v___x_1253_ == 0)
{
v___y_1248_ = v___x_1253_;
goto v___jp_1247_;
}
else
{
uint32_t v___x_1254_; uint8_t v___x_1255_; 
v___x_1254_ = 57;
v___x_1255_ = lean_uint32_dec_le(v___x_1213_, v___x_1254_);
v___y_1248_ = v___x_1255_;
goto v___jp_1247_;
}
v___jp_1216_:
{
uint32_t v___x_1219_; uint8_t v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1224_; 
v___x_1219_ = 95;
v___x_1220_ = lean_uint32_dec_eq(v___x_1213_, v___x_1219_);
v___x_1221_ = lean_box(v___y_1217_);
v___x_1222_ = lean_box(v___y_1218_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 1, v___x_1222_);
lean_ctor_set(v___x_1207_, 0, v___x_1221_);
v___x_1224_ = v___x_1207_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1221_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v___x_1222_);
v___x_1224_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
lean_object* v___x_1225_; lean_object* v___x_1227_; 
v___x_1225_ = lean_box(v___x_1220_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 1, v___x_1224_);
lean_ctor_set(v___x_1203_, 0, v___x_1225_);
v___x_1227_ = v___x_1203_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___x_1225_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v___x_1224_);
v___x_1227_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
lean_object* v___x_1228_; lean_object* v___x_1230_; 
v___x_1228_ = lean_box(v___x_1210_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 1, v___x_1227_);
lean_ctor_set(v___x_1199_, 0, v___x_1228_);
v___x_1230_ = v___x_1199_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1228_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v___x_1227_);
v___x_1230_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
v_a_1188_ = v___x_1215_;
v_b_1189_ = v___x_1230_;
goto _start;
}
}
}
}
v___jp_1235_:
{
uint8_t v___x_1238_; 
v___x_1238_ = lean_unbox(v_fst_1201_);
lean_dec(v_fst_1201_);
if (v___x_1238_ == 0)
{
v___y_1217_ = v___y_1236_;
v___y_1218_ = v___y_1237_;
goto v___jp_1216_;
}
else
{
uint32_t v___x_1239_; uint8_t v___x_1240_; 
v___x_1239_ = 95;
v___x_1240_ = lean_uint32_dec_eq(v___x_1213_, v___x_1239_);
if (v___x_1240_ == 0)
{
v___y_1217_ = v___y_1236_;
v___y_1218_ = v___y_1237_;
goto v___jp_1216_;
}
else
{
v___y_1217_ = v___y_1236_;
v___y_1218_ = v___x_1210_;
goto v___jp_1216_;
}
}
}
v___jp_1241_:
{
uint8_t v___x_1244_; 
v___x_1244_ = lean_unbox(v_fst_1197_);
lean_dec(v_fst_1197_);
if (v___x_1244_ == 0)
{
v___y_1236_ = v___y_1242_;
v___y_1237_ = v___y_1243_;
goto v___jp_1235_;
}
else
{
uint32_t v___x_1245_; uint8_t v___x_1246_; 
v___x_1245_ = 95;
v___x_1246_ = lean_uint32_dec_eq(v___x_1213_, v___x_1245_);
if (v___x_1246_ == 0)
{
v___y_1236_ = v___y_1242_;
v___y_1237_ = v___y_1243_;
goto v___jp_1235_;
}
else
{
lean_dec(v_fst_1201_);
v___y_1217_ = v___y_1242_;
v___y_1218_ = v___x_1210_;
goto v___jp_1216_;
}
}
}
v___jp_1247_:
{
uint8_t v___x_1249_; 
v___x_1249_ = lean_unbox(v_snd_1205_);
lean_dec(v_snd_1205_);
if (v___x_1249_ == 0)
{
lean_dec(v_fst_1201_);
lean_dec(v_fst_1197_);
v___y_1217_ = v___y_1248_;
v___y_1218_ = v___x_1210_;
goto v___jp_1216_;
}
else
{
if (v___y_1248_ == 0)
{
uint32_t v___x_1250_; uint8_t v___x_1251_; 
v___x_1250_ = 95;
v___x_1251_ = lean_uint32_dec_eq(v___x_1213_, v___x_1250_);
if (v___x_1251_ == 0)
{
lean_dec(v_fst_1201_);
lean_dec(v_fst_1197_);
v___y_1217_ = v___y_1248_;
v___y_1218_ = v___x_1210_;
goto v___jp_1216_;
}
else
{
v___y_1242_ = v___y_1248_;
v___y_1243_ = v___x_1251_;
goto v___jp_1241_;
}
}
else
{
v___y_1242_ = v___y_1248_;
v___y_1243_ = v___x_1211_;
goto v___jp_1241_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1188_);
return v_b_1189_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg___boxed(lean_object* v___x_1262_, lean_object* v___y_1263_, lean_object* v_a_1264_, lean_object* v_b_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(v___x_1262_, v___y_1263_, v_a_1264_, v_b_1265_);
lean_dec_ref(v___y_1263_);
lean_dec(v___x_1262_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toNat_x3f(lean_object* v_s_1267_){
_start:
{
lean_object* v_str_1268_; lean_object* v_startPos_1269_; lean_object* v_stopPos_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1323_; 
v_str_1268_ = lean_ctor_get(v_s_1267_, 0);
v_startPos_1269_ = lean_ctor_get(v_s_1267_, 1);
v_stopPos_1270_ = lean_ctor_get(v_s_1267_, 2);
v_isSharedCheck_1323_ = !lean_is_exclusive(v_s_1267_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1272_ = v_s_1267_;
v_isShared_1273_ = v_isSharedCheck_1323_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_stopPos_1270_);
lean_inc(v_startPos_1269_);
lean_inc(v_str_1268_);
lean_dec(v_s_1267_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1323_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___y_1277_; uint8_t v___y_1284_; uint8_t v___y_1285_; uint8_t v___x_1289_; 
v___x_1274_ = lean_nat_sub(v_stopPos_1270_, v_startPos_1269_);
v___x_1275_ = lean_unsigned_to_nat(0u);
v___x_1289_ = lean_nat_dec_eq(v___x_1274_, v___x_1275_);
if (v___x_1289_ == 0)
{
uint8_t v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___y_1299_; uint8_t v___y_1313_; uint8_t v___x_1317_; uint8_t v___y_1319_; uint8_t v___x_1320_; 
v___x_1290_ = 1;
v___x_1291_ = lean_box(v___x_1289_);
v___x_1292_ = lean_box(v___x_1290_);
v___x_1293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1291_);
lean_ctor_set(v___x_1293_, 1, v___x_1292_);
v___x_1294_ = lean_box(v___x_1289_);
v___x_1295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
lean_ctor_set(v___x_1295_, 1, v___x_1293_);
v___x_1296_ = lean_box(v___x_1290_);
v___x_1297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1296_);
lean_ctor_set(v___x_1297_, 1, v___x_1295_);
v___x_1317_ = lean_string_is_valid_pos(v_str_1268_, v_startPos_1269_);
v___x_1320_ = lean_string_is_valid_pos(v_str_1268_, v_stopPos_1270_);
if (v___x_1320_ == 0)
{
v___y_1319_ = v___x_1320_;
goto v___jp_1318_;
}
else
{
uint8_t v___x_1321_; 
v___x_1321_ = lean_nat_dec_le(v_startPos_1269_, v_stopPos_1270_);
v___y_1319_ = v___x_1321_;
goto v___jp_1318_;
}
v___jp_1298_:
{
lean_object* v___x_1300_; lean_object* v_snd_1301_; lean_object* v_snd_1302_; lean_object* v_snd_1303_; uint8_t v___x_1304_; 
v___x_1300_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(v___x_1274_, v___y_1299_, v___x_1275_, v___x_1297_);
lean_dec_ref(v___y_1299_);
lean_dec(v___x_1274_);
v_snd_1301_ = lean_ctor_get(v___x_1300_, 1);
lean_inc(v_snd_1301_);
lean_dec_ref(v___x_1300_);
v_snd_1302_ = lean_ctor_get(v_snd_1301_, 1);
lean_inc(v_snd_1302_);
lean_dec(v_snd_1301_);
v_snd_1303_ = lean_ctor_get(v_snd_1302_, 1);
v___x_1304_ = lean_unbox(v_snd_1303_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; 
lean_dec(v_snd_1302_);
lean_del_object(v___x_1272_);
lean_dec(v_stopPos_1270_);
lean_dec(v_startPos_1269_);
lean_dec_ref(v_str_1268_);
v___x_1305_ = lean_box(0);
return v___x_1305_;
}
else
{
lean_object* v_fst_1306_; uint8_t v___x_1307_; 
v_fst_1306_ = lean_ctor_get(v_snd_1302_, 0);
lean_inc(v_fst_1306_);
lean_dec(v_snd_1302_);
v___x_1307_ = lean_unbox(v_fst_1306_);
lean_dec(v_fst_1306_);
if (v___x_1307_ == 0)
{
lean_object* v___x_1308_; 
lean_del_object(v___x_1272_);
lean_dec(v_stopPos_1270_);
lean_dec(v_startPos_1269_);
lean_dec_ref(v_str_1268_);
v___x_1308_ = lean_box(0);
return v___x_1308_;
}
else
{
uint8_t v___x_1309_; uint8_t v___x_1310_; 
v___x_1309_ = lean_string_is_valid_pos(v_str_1268_, v_startPos_1269_);
v___x_1310_ = lean_string_is_valid_pos(v_str_1268_, v_stopPos_1270_);
if (v___x_1310_ == 0)
{
v___y_1284_ = v___x_1309_;
v___y_1285_ = v___x_1310_;
goto v___jp_1283_;
}
else
{
uint8_t v___x_1311_; 
v___x_1311_ = lean_nat_dec_le(v_startPos_1269_, v_stopPos_1270_);
v___y_1284_ = v___x_1309_;
v___y_1285_ = v___x_1311_;
goto v___jp_1283_;
}
}
}
}
v___jp_1312_:
{
if (v___y_1313_ == 0)
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_1315_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_1314_);
v___y_1299_ = v___x_1315_;
goto v___jp_1298_;
}
else
{
lean_object* v___x_1316_; 
lean_inc(v_stopPos_1270_);
lean_inc(v_startPos_1269_);
lean_inc_ref(v_str_1268_);
v___x_1316_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1316_, 0, v_str_1268_);
lean_ctor_set(v___x_1316_, 1, v_startPos_1269_);
lean_ctor_set(v___x_1316_, 2, v_stopPos_1270_);
v___y_1299_ = v___x_1316_;
goto v___jp_1298_;
}
}
v___jp_1318_:
{
if (v___x_1317_ == 0)
{
v___y_1313_ = v___x_1317_;
goto v___jp_1312_;
}
else
{
v___y_1313_ = v___y_1319_;
goto v___jp_1312_;
}
}
}
else
{
lean_object* v___x_1322_; 
lean_dec(v___x_1274_);
lean_del_object(v___x_1272_);
lean_dec(v_stopPos_1270_);
lean_dec(v_startPos_1269_);
lean_dec_ref(v_str_1268_);
v___x_1322_ = lean_box(0);
return v___x_1322_;
}
v___jp_1276_:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(v___y_1277_, v___x_1275_, v___x_1275_);
lean_dec_ref(v___y_1277_);
v___x_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
return v___x_1279_;
}
v___jp_1280_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_1282_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_1281_);
v___y_1277_ = v___x_1282_;
goto v___jp_1276_;
}
v___jp_1283_:
{
if (v___y_1284_ == 0)
{
lean_del_object(v___x_1272_);
lean_dec(v_stopPos_1270_);
lean_dec(v_startPos_1269_);
lean_dec_ref(v_str_1268_);
goto v___jp_1280_;
}
else
{
if (v___y_1285_ == 0)
{
lean_del_object(v___x_1272_);
lean_dec(v_stopPos_1270_);
lean_dec(v_startPos_1269_);
lean_dec_ref(v_str_1268_);
goto v___jp_1280_;
}
else
{
lean_object* v___x_1287_; 
if (v_isShared_1273_ == 0)
{
v___x_1287_ = v___x_1272_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_str_1268_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v_startPos_1269_);
lean_ctor_set(v_reuseFailAlloc_1288_, 2, v_stopPos_1270_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
v___y_1277_ = v___x_1287_;
goto v___jp_1276_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0(lean_object* v___x_1324_, lean_object* v___y_1325_, lean_object* v_inst_1326_, lean_object* v_R_1327_, lean_object* v_a_1328_, lean_object* v_b_1329_, lean_object* v_c_1330_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(v___x_1324_, v___y_1325_, v_a_1328_, v_b_1329_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___boxed(lean_object* v___x_1332_, lean_object* v___y_1333_, lean_object* v_inst_1334_, lean_object* v_R_1335_, lean_object* v_a_1336_, lean_object* v_b_1337_, lean_object* v_c_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0(v___x_1332_, v___y_1333_, v_inst_1334_, v_R_1335_, v_a_1336_, v_b_1337_, v_c_1338_);
lean_dec_ref(v___y_1333_);
lean_dec(v___x_1332_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1(lean_object* v___y_1340_, lean_object* v_inst_1341_, lean_object* v_R_1342_, lean_object* v_a_1343_, lean_object* v_b_1344_, lean_object* v_c_1345_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(v___y_1340_, v_a_1343_, v_b_1344_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___boxed(lean_object* v___y_1347_, lean_object* v_inst_1348_, lean_object* v_R_1349_, lean_object* v_a_1350_, lean_object* v_b_1351_, lean_object* v_c_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1(v___y_1347_, v_inst_1348_, v_R_1349_, v_a_1350_, v_b_1351_, v_c_1352_);
lean_dec_ref(v___y_1347_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_repair(lean_object* v_x_1354_){
_start:
{
lean_object* v_str_1355_; lean_object* v_startPos_1356_; lean_object* v_stopPos_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1373_; 
v_str_1355_ = lean_ctor_get(v_x_1354_, 0);
v_startPos_1356_ = lean_ctor_get(v_x_1354_, 1);
v_stopPos_1357_ = lean_ctor_get(v_x_1354_, 2);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_x_1354_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1359_ = v_x_1354_;
v_isShared_1360_ = v_isSharedCheck_1373_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_stopPos_1357_);
lean_inc(v_startPos_1356_);
lean_inc(v_str_1355_);
lean_dec(v_x_1354_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1373_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___y_1362_; uint8_t v___x_1371_; 
v___x_1371_ = lean_string_is_valid_pos(v_str_1355_, v_startPos_1356_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; 
lean_dec(v_startPos_1356_);
v___x_1372_ = lean_string_utf8_byte_size(v_str_1355_);
v___y_1362_ = v___x_1372_;
goto v___jp_1361_;
}
else
{
v___y_1362_ = v_startPos_1356_;
goto v___jp_1361_;
}
v___jp_1361_:
{
uint8_t v___x_1363_; 
v___x_1363_ = lean_string_is_valid_pos(v_str_1355_, v_stopPos_1357_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; lean_object* v___x_1366_; 
lean_dec(v_stopPos_1357_);
v___x_1364_ = lean_string_utf8_byte_size(v_str_1355_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 2, v___x_1364_);
lean_ctor_set(v___x_1359_, 1, v___y_1362_);
v___x_1366_ = v___x_1359_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_str_1355_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v___y_1362_);
lean_ctor_set(v_reuseFailAlloc_1367_, 2, v___x_1364_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
else
{
lean_object* v___x_1369_; 
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 1, v___y_1362_);
v___x_1369_ = v___x_1359_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_str_1355_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v___y_1362_);
lean_ctor_set(v_reuseFailAlloc_1370_, 2, v_stopPos_1357_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_beq(lean_object* v_ss1_1374_, lean_object* v_ss2_1375_){
_start:
{
lean_object* v_ss1_1376_; lean_object* v_str_1377_; lean_object* v_startPos_1378_; lean_object* v_stopPos_1379_; lean_object* v_ss2_1380_; lean_object* v_str_1381_; lean_object* v_startPos_1382_; lean_object* v_stopPos_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; 
v_ss1_1376_ = l_Substring_Raw_repair(v_ss1_1374_);
v_str_1377_ = lean_ctor_get(v_ss1_1376_, 0);
lean_inc_ref(v_str_1377_);
v_startPos_1378_ = lean_ctor_get(v_ss1_1376_, 1);
lean_inc(v_startPos_1378_);
v_stopPos_1379_ = lean_ctor_get(v_ss1_1376_, 2);
lean_inc(v_stopPos_1379_);
lean_dec_ref(v_ss1_1376_);
v_ss2_1380_ = l_Substring_Raw_repair(v_ss2_1375_);
v_str_1381_ = lean_ctor_get(v_ss2_1380_, 0);
lean_inc_ref(v_str_1381_);
v_startPos_1382_ = lean_ctor_get(v_ss2_1380_, 1);
lean_inc(v_startPos_1382_);
v_stopPos_1383_ = lean_ctor_get(v_ss2_1380_, 2);
lean_inc(v_stopPos_1383_);
lean_dec_ref(v_ss2_1380_);
v___x_1384_ = lean_nat_sub(v_stopPos_1379_, v_startPos_1378_);
lean_dec(v_stopPos_1379_);
v___x_1385_ = lean_nat_sub(v_stopPos_1383_, v_startPos_1382_);
lean_dec(v_stopPos_1383_);
v___x_1386_ = lean_nat_dec_eq(v___x_1384_, v___x_1385_);
lean_dec(v___x_1385_);
if (v___x_1386_ == 0)
{
lean_dec(v___x_1384_);
lean_dec(v_startPos_1382_);
lean_dec_ref(v_str_1381_);
lean_dec(v_startPos_1378_);
lean_dec_ref(v_str_1377_);
return v___x_1386_;
}
else
{
uint8_t v___x_1387_; 
v___x_1387_ = l_String_Pos_Raw_substrEq(v_str_1377_, v_startPos_1378_, v_str_1381_, v_startPos_1382_, v___x_1384_);
lean_dec(v___x_1384_);
lean_dec_ref(v_str_1381_);
lean_dec_ref(v_str_1377_);
return v___x_1387_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_beq___boxed(lean_object* v_ss1_1388_, lean_object* v_ss2_1389_){
_start:
{
uint8_t v_res_1390_; lean_object* v_r_1391_; 
v_res_1390_ = l_Substring_Raw_beq(v_ss1_1388_, v_ss2_1389_);
v_r_1391_ = lean_box(v_res_1390_);
return v_r_1391_;
}
}
LEAN_EXPORT uint8_t lean_substring_beq(lean_object* v_ss1_1392_, lean_object* v_ss2_1393_){
_start:
{
uint8_t v___x_1394_; 
v___x_1394_ = l_Substring_Raw_beq(v_ss1_1392_, v_ss2_1393_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_beqImpl___boxed(lean_object* v_ss1_1395_, lean_object* v_ss2_1396_){
_start:
{
uint8_t v_res_1397_; lean_object* v_r_1398_; 
v_res_1397_ = lean_substring_beq(v_ss1_1395_, v_ss2_1396_);
v_r_1398_ = lean_box(v_res_1397_);
return v_r_1398_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_sameAs(lean_object* v_ss1_1401_, lean_object* v_ss2_1402_){
_start:
{
lean_object* v_startPos_1403_; lean_object* v_startPos_1404_; uint8_t v_decide_1405_; 
v_startPos_1403_ = lean_ctor_get(v_ss1_1401_, 1);
v_startPos_1404_ = lean_ctor_get(v_ss2_1402_, 1);
v_decide_1405_ = lean_nat_dec_eq(v_startPos_1403_, v_startPos_1404_);
if (v_decide_1405_ == 0)
{
lean_dec_ref(v_ss2_1402_);
lean_dec_ref(v_ss1_1401_);
return v_decide_1405_;
}
else
{
uint8_t v___x_1406_; 
v___x_1406_ = l_Substring_Raw_beq(v_ss1_1401_, v_ss2_1402_);
return v___x_1406_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_sameAs___boxed(lean_object* v_ss1_1407_, lean_object* v_ss2_1408_){
_start:
{
uint8_t v_res_1409_; lean_object* v_r_1410_; 
v_res_1409_ = l_Substring_Raw_sameAs(v_ss1_1407_, v_ss2_1408_);
v_r_1410_ = lean_box(v_res_1409_);
return v_r_1410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(lean_object* v_s_1411_, lean_object* v_t_1412_, lean_object* v_spos_1413_, lean_object* v_tpos_1414_){
_start:
{
lean_object* v_str_1415_; lean_object* v_stopPos_1416_; lean_object* v_str_1417_; lean_object* v_stopPos_1418_; uint8_t v___y_1420_; uint8_t v___x_1427_; 
v_str_1415_ = lean_ctor_get(v_s_1411_, 0);
v_stopPos_1416_ = lean_ctor_get(v_s_1411_, 2);
v_str_1417_ = lean_ctor_get(v_t_1412_, 0);
v_stopPos_1418_ = lean_ctor_get(v_t_1412_, 2);
v___x_1427_ = l_String_instDecidableLtRaw(v_spos_1413_, v_stopPos_1416_);
if (v___x_1427_ == 0)
{
v___y_1420_ = v___x_1427_;
goto v___jp_1419_;
}
else
{
uint8_t v___x_1428_; 
v___x_1428_ = l_String_instDecidableLtRaw(v_tpos_1414_, v_stopPos_1418_);
v___y_1420_ = v___x_1428_;
goto v___jp_1419_;
}
v___jp_1419_:
{
if (v___y_1420_ == 0)
{
lean_dec(v_tpos_1414_);
return v_spos_1413_;
}
else
{
uint32_t v___x_1421_; uint32_t v___x_1422_; uint8_t v___x_1423_; 
v___x_1421_ = lean_string_utf8_get(v_str_1415_, v_spos_1413_);
v___x_1422_ = lean_string_utf8_get(v_str_1417_, v_tpos_1414_);
v___x_1423_ = lean_uint32_dec_eq(v___x_1421_, v___x_1422_);
if (v___x_1423_ == 0)
{
lean_dec(v_tpos_1414_);
return v_spos_1413_;
}
else
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1424_ = lean_string_utf8_next(v_str_1415_, v_spos_1413_);
lean_dec(v_spos_1413_);
v___x_1425_ = lean_string_utf8_next(v_str_1417_, v_tpos_1414_);
lean_dec(v_tpos_1414_);
v_spos_1413_ = v___x_1424_;
v_tpos_1414_ = v___x_1425_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop___boxed(lean_object* v_s_1429_, lean_object* v_t_1430_, lean_object* v_spos_1431_, lean_object* v_tpos_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(v_s_1429_, v_t_1430_, v_spos_1431_, v_tpos_1432_);
lean_dec_ref(v_t_1430_);
lean_dec_ref(v_s_1429_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_commonPrefix(lean_object* v_s_1434_, lean_object* v_t_1435_){
_start:
{
lean_object* v_str_1436_; lean_object* v_startPos_1437_; lean_object* v_startPos_1438_; lean_object* v___x_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
v_str_1436_ = lean_ctor_get(v_s_1434_, 0);
lean_inc_ref(v_str_1436_);
v_startPos_1437_ = lean_ctor_get(v_s_1434_, 1);
lean_inc_n(v_startPos_1437_, 2);
v_startPos_1438_ = lean_ctor_get(v_t_1435_, 1);
lean_inc(v_startPos_1438_);
v___x_1439_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(v_s_1434_, v_t_1435_, v_startPos_1437_, v_startPos_1438_);
lean_dec_ref(v_s_1434_);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_t_1435_);
if (v_isSharedCheck_1446_ == 0)
{
lean_object* v_unused_1447_; lean_object* v_unused_1448_; lean_object* v_unused_1449_; 
v_unused_1447_ = lean_ctor_get(v_t_1435_, 2);
lean_dec(v_unused_1447_);
v_unused_1448_ = lean_ctor_get(v_t_1435_, 1);
lean_dec(v_unused_1448_);
v_unused_1449_ = lean_ctor_get(v_t_1435_, 0);
lean_dec(v_unused_1449_);
v___x_1441_ = v_t_1435_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_dec(v_t_1435_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 2, v___x_1439_);
lean_ctor_set(v___x_1441_, 1, v_startPos_1437_);
lean_ctor_set(v___x_1441_, 0, v_str_1436_);
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_str_1436_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_startPos_1437_);
lean_ctor_set(v_reuseFailAlloc_1445_, 2, v___x_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(lean_object* v_s_1450_, lean_object* v_t_1451_, lean_object* v_spos_1452_, lean_object* v_tpos_1453_){
_start:
{
lean_object* v_str_1454_; lean_object* v_startPos_1455_; lean_object* v_str_1456_; lean_object* v_startPos_1457_; uint8_t v___y_1459_; uint8_t v___x_1466_; 
v_str_1454_ = lean_ctor_get(v_s_1450_, 0);
v_startPos_1455_ = lean_ctor_get(v_s_1450_, 1);
v_str_1456_ = lean_ctor_get(v_t_1451_, 0);
v_startPos_1457_ = lean_ctor_get(v_t_1451_, 1);
v___x_1466_ = l_String_instDecidableLtRaw(v_startPos_1455_, v_spos_1452_);
if (v___x_1466_ == 0)
{
v___y_1459_ = v___x_1466_;
goto v___jp_1458_;
}
else
{
uint8_t v___x_1467_; 
v___x_1467_ = l_String_instDecidableLtRaw(v_startPos_1457_, v_tpos_1453_);
v___y_1459_ = v___x_1467_;
goto v___jp_1458_;
}
v___jp_1458_:
{
if (v___y_1459_ == 0)
{
lean_dec(v_tpos_1453_);
return v_spos_1452_;
}
else
{
lean_object* v_spos_x27_1460_; lean_object* v_tpos_x27_1461_; uint32_t v___x_1462_; uint32_t v___x_1463_; uint8_t v___x_1464_; 
v_spos_x27_1460_ = lean_string_utf8_prev(v_str_1454_, v_spos_1452_);
v_tpos_x27_1461_ = lean_string_utf8_prev(v_str_1456_, v_tpos_1453_);
lean_dec(v_tpos_1453_);
v___x_1462_ = lean_string_utf8_get(v_str_1454_, v_spos_x27_1460_);
v___x_1463_ = lean_string_utf8_get(v_str_1456_, v_tpos_x27_1461_);
v___x_1464_ = lean_uint32_dec_eq(v___x_1462_, v___x_1463_);
if (v___x_1464_ == 0)
{
lean_dec(v_tpos_x27_1461_);
lean_dec(v_spos_x27_1460_);
return v_spos_1452_;
}
else
{
lean_dec(v_spos_1452_);
v_spos_1452_ = v_spos_x27_1460_;
v_tpos_1453_ = v_tpos_x27_1461_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop___boxed(lean_object* v_s_1468_, lean_object* v_t_1469_, lean_object* v_spos_1470_, lean_object* v_tpos_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(v_s_1468_, v_t_1469_, v_spos_1470_, v_tpos_1471_);
lean_dec_ref(v_t_1469_);
lean_dec_ref(v_s_1468_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_commonSuffix(lean_object* v_s_1473_, lean_object* v_t_1474_){
_start:
{
lean_object* v_str_1475_; lean_object* v_stopPos_1476_; lean_object* v_stopPos_1477_; lean_object* v___x_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
v_str_1475_ = lean_ctor_get(v_s_1473_, 0);
lean_inc_ref(v_str_1475_);
v_stopPos_1476_ = lean_ctor_get(v_s_1473_, 2);
lean_inc_n(v_stopPos_1476_, 2);
v_stopPos_1477_ = lean_ctor_get(v_t_1474_, 2);
lean_inc(v_stopPos_1477_);
v___x_1478_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(v_s_1473_, v_t_1474_, v_stopPos_1476_, v_stopPos_1477_);
lean_dec_ref(v_s_1473_);
v_isSharedCheck_1485_ = !lean_is_exclusive(v_t_1474_);
if (v_isSharedCheck_1485_ == 0)
{
lean_object* v_unused_1486_; lean_object* v_unused_1487_; lean_object* v_unused_1488_; 
v_unused_1486_ = lean_ctor_get(v_t_1474_, 2);
lean_dec(v_unused_1486_);
v_unused_1487_ = lean_ctor_get(v_t_1474_, 1);
lean_dec(v_unused_1487_);
v_unused_1488_ = lean_ctor_get(v_t_1474_, 0);
lean_dec(v_unused_1488_);
v___x_1480_ = v_t_1474_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_dec(v_t_1474_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 2, v_stopPos_1476_);
lean_ctor_set(v___x_1480_, 1, v___x_1478_);
lean_ctor_set(v___x_1480_, 0, v_str_1475_);
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_str_1475_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v___x_1478_);
lean_ctor_set(v_reuseFailAlloc_1484_, 2, v_stopPos_1476_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropPrefix_x3f(lean_object* v_s_1489_, lean_object* v_pre_1490_){
_start:
{
lean_object* v_t_1491_; lean_object* v_startPos_1492_; lean_object* v_stopPos_1493_; lean_object* v_startPos_1494_; lean_object* v_stopPos_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; uint8_t v___x_1498_; 
lean_inc_ref(v_pre_1490_);
lean_inc_ref(v_s_1489_);
v_t_1491_ = l_Substring_Raw_commonPrefix(v_s_1489_, v_pre_1490_);
v_startPos_1492_ = lean_ctor_get(v_t_1491_, 1);
lean_inc(v_startPos_1492_);
v_stopPos_1493_ = lean_ctor_get(v_t_1491_, 2);
lean_inc(v_stopPos_1493_);
lean_dec_ref(v_t_1491_);
v_startPos_1494_ = lean_ctor_get(v_pre_1490_, 1);
lean_inc(v_startPos_1494_);
v_stopPos_1495_ = lean_ctor_get(v_pre_1490_, 2);
lean_inc(v_stopPos_1495_);
lean_dec_ref(v_pre_1490_);
v___x_1496_ = lean_nat_sub(v_stopPos_1493_, v_startPos_1492_);
lean_dec(v_startPos_1492_);
v___x_1497_ = lean_nat_sub(v_stopPos_1495_, v_startPos_1494_);
lean_dec(v_startPos_1494_);
lean_dec(v_stopPos_1495_);
v___x_1498_ = lean_nat_dec_eq(v___x_1496_, v___x_1497_);
lean_dec(v___x_1497_);
lean_dec(v___x_1496_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; 
lean_dec(v_stopPos_1493_);
lean_dec_ref(v_s_1489_);
v___x_1499_ = lean_box(0);
return v___x_1499_;
}
else
{
lean_object* v_str_1500_; lean_object* v_stopPos_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1509_; 
v_str_1500_ = lean_ctor_get(v_s_1489_, 0);
v_stopPos_1501_ = lean_ctor_get(v_s_1489_, 2);
v_isSharedCheck_1509_ = !lean_is_exclusive(v_s_1489_);
if (v_isSharedCheck_1509_ == 0)
{
lean_object* v_unused_1510_; 
v_unused_1510_ = lean_ctor_get(v_s_1489_, 1);
lean_dec(v_unused_1510_);
v___x_1503_ = v_s_1489_;
v_isShared_1504_ = v_isSharedCheck_1509_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_stopPos_1501_);
lean_inc(v_str_1500_);
lean_dec(v_s_1489_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1509_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 1, v_stopPos_1493_);
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_str_1500_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_stopPos_1493_);
lean_ctor_set(v_reuseFailAlloc_1508_, 2, v_stopPos_1501_);
v___x_1506_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
lean_object* v___x_1507_; 
v___x_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1506_);
return v___x_1507_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropSuffix_x3f(lean_object* v_s_1511_, lean_object* v_suff_1512_){
_start:
{
lean_object* v_t_1513_; lean_object* v_startPos_1514_; lean_object* v_stopPos_1515_; lean_object* v_startPos_1516_; lean_object* v_stopPos_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; uint8_t v___x_1520_; 
lean_inc_ref(v_suff_1512_);
lean_inc_ref(v_s_1511_);
v_t_1513_ = l_Substring_Raw_commonSuffix(v_s_1511_, v_suff_1512_);
v_startPos_1514_ = lean_ctor_get(v_t_1513_, 1);
lean_inc(v_startPos_1514_);
v_stopPos_1515_ = lean_ctor_get(v_t_1513_, 2);
lean_inc(v_stopPos_1515_);
lean_dec_ref(v_t_1513_);
v_startPos_1516_ = lean_ctor_get(v_suff_1512_, 1);
lean_inc(v_startPos_1516_);
v_stopPos_1517_ = lean_ctor_get(v_suff_1512_, 2);
lean_inc(v_stopPos_1517_);
lean_dec_ref(v_suff_1512_);
v___x_1518_ = lean_nat_sub(v_stopPos_1515_, v_startPos_1514_);
lean_dec(v_stopPos_1515_);
v___x_1519_ = lean_nat_sub(v_stopPos_1517_, v_startPos_1516_);
lean_dec(v_startPos_1516_);
lean_dec(v_stopPos_1517_);
v___x_1520_ = lean_nat_dec_eq(v___x_1518_, v___x_1519_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1521_; 
lean_dec(v_startPos_1514_);
lean_dec_ref(v_s_1511_);
v___x_1521_ = lean_box(0);
return v___x_1521_;
}
else
{
lean_object* v_str_1522_; lean_object* v_startPos_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1531_; 
v_str_1522_ = lean_ctor_get(v_s_1511_, 0);
v_startPos_1523_ = lean_ctor_get(v_s_1511_, 1);
v_isSharedCheck_1531_ = !lean_is_exclusive(v_s_1511_);
if (v_isSharedCheck_1531_ == 0)
{
lean_object* v_unused_1532_; 
v_unused_1532_ = lean_ctor_get(v_s_1511_, 2);
lean_dec(v_unused_1532_);
v___x_1525_ = v_s_1511_;
v_isShared_1526_ = v_isSharedCheck_1531_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_startPos_1523_);
lean_inc(v_str_1522_);
lean_dec(v_s_1511_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1531_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 2, v_startPos_1514_);
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_str_1522_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_startPos_1523_);
lean_ctor_set(v_reuseFailAlloc_1530_, 2, v_startPos_1514_);
v___x_1528_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
lean_object* v___x_1529_; 
v___x_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
return v___x_1529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg(lean_object* v_x_1533_, lean_object* v_x_1534_, lean_object* v_x_1535_, lean_object* v_h__1_1536_, lean_object* v_h__2_1537_){
_start:
{
lean_object* v_zero_1538_; uint8_t v_isZero_1539_; 
v_zero_1538_ = lean_unsigned_to_nat(0u);
v_isZero_1539_ = lean_nat_dec_eq(v_x_1534_, v_zero_1538_);
if (v_isZero_1539_ == 1)
{
lean_object* v___x_1540_; 
lean_dec(v_h__2_1537_);
v___x_1540_ = lean_apply_2(v_h__1_1536_, v_x_1533_, v_x_1535_);
return v___x_1540_;
}
else
{
lean_object* v_one_1541_; lean_object* v_n_1542_; lean_object* v___x_1543_; 
lean_dec(v_h__1_1536_);
v_one_1541_ = lean_unsigned_to_nat(1u);
v_n_1542_ = lean_nat_sub(v_x_1534_, v_one_1541_);
v___x_1543_ = lean_apply_3(v_h__2_1537_, v_x_1533_, v_n_1542_, v_x_1535_);
return v___x_1543_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg___boxed(lean_object* v_x_1544_, lean_object* v_x_1545_, lean_object* v_x_1546_, lean_object* v_h__1_1547_, lean_object* v_h__2_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg(v_x_1544_, v_x_1545_, v_x_1546_, v_h__1_1547_, v_h__2_1548_);
lean_dec(v_x_1545_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter(lean_object* v_motive_1550_, lean_object* v_x_1551_, lean_object* v_x_1552_, lean_object* v_x_1553_, lean_object* v_h__1_1554_, lean_object* v_h__2_1555_){
_start:
{
lean_object* v_zero_1556_; uint8_t v_isZero_1557_; 
v_zero_1556_ = lean_unsigned_to_nat(0u);
v_isZero_1557_ = lean_nat_dec_eq(v_x_1552_, v_zero_1556_);
if (v_isZero_1557_ == 1)
{
lean_object* v___x_1558_; 
lean_dec(v_h__2_1555_);
v___x_1558_ = lean_apply_2(v_h__1_1554_, v_x_1551_, v_x_1553_);
return v___x_1558_;
}
else
{
lean_object* v_one_1559_; lean_object* v_n_1560_; lean_object* v___x_1561_; 
lean_dec(v_h__1_1554_);
v_one_1559_ = lean_unsigned_to_nat(1u);
v_n_1560_ = lean_nat_sub(v_x_1552_, v_one_1559_);
v___x_1561_ = lean_apply_3(v_h__2_1555_, v_x_1551_, v_n_1560_, v_x_1553_);
return v___x_1561_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___boxed(lean_object* v_motive_1562_, lean_object* v_x_1563_, lean_object* v_x_1564_, lean_object* v_x_1565_, lean_object* v_h__1_1566_, lean_object* v_h__2_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter(v_motive_1562_, v_x_1563_, v_x_1564_, v_x_1565_, v_h__1_1566_, v_h__2_1567_);
lean_dec(v_x_1564_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_Substring_bsize(lean_object* v_a_1569_){
_start:
{
lean_object* v_startPos_1570_; lean_object* v_stopPos_1571_; lean_object* v___x_1572_; 
v_startPos_1570_ = lean_ctor_get(v_a_1569_, 1);
v_stopPos_1571_ = lean_ctor_get(v_a_1569_, 2);
v___x_1572_ = lean_nat_sub(v_stopPos_1571_, v_startPos_1570_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Substring_bsize___boxed(lean_object* v_a_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_Substring_bsize(v_a_1573_);
lean_dec_ref(v_a_1573_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_Substring_toString(lean_object* v_a_1575_){
_start:
{
lean_object* v_str_1576_; lean_object* v_startPos_1577_; lean_object* v_stopPos_1578_; lean_object* v___x_1579_; 
v_str_1576_ = lean_ctor_get(v_a_1575_, 0);
v_startPos_1577_ = lean_ctor_get(v_a_1575_, 1);
v_stopPos_1578_ = lean_ctor_get(v_a_1575_, 2);
v___x_1579_ = lean_string_utf8_extract(v_str_1576_, v_startPos_1577_, v_stopPos_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Substring_toString___boxed(lean_object* v_a_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_Substring_toString(v_a_1580_);
lean_dec_ref(v_a_1580_);
return v_res_1581_;
}
}
LEAN_EXPORT uint8_t l_Substring_isEmpty(lean_object* v_ss_1582_){
_start:
{
lean_object* v_startPos_1583_; lean_object* v_stopPos_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; uint8_t v___x_1587_; 
v_startPos_1583_ = lean_ctor_get(v_ss_1582_, 1);
v_stopPos_1584_ = lean_ctor_get(v_ss_1582_, 2);
v___x_1585_ = lean_nat_sub(v_stopPos_1584_, v_startPos_1583_);
v___x_1586_ = lean_unsigned_to_nat(0u);
v___x_1587_ = lean_nat_dec_eq(v___x_1585_, v___x_1586_);
lean_dec(v___x_1585_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Substring_isEmpty___boxed(lean_object* v_ss_1588_){
_start:
{
uint8_t v_res_1589_; lean_object* v_r_1590_; 
v_res_1589_ = l_Substring_isEmpty(v_ss_1588_);
lean_dec_ref(v_ss_1588_);
v_r_1590_ = lean_box(v_res_1589_);
return v_r_1590_;
}
}
LEAN_EXPORT lean_object* l_Substring_next(lean_object* v_a_1591_, lean_object* v_a_1592_){
_start:
{
lean_object* v_str_1593_; lean_object* v_startPos_1594_; lean_object* v_stopPos_1595_; lean_object* v_absP_1596_; uint8_t v_decide_1597_; 
v_str_1593_ = lean_ctor_get(v_a_1591_, 0);
v_startPos_1594_ = lean_ctor_get(v_a_1591_, 1);
v_stopPos_1595_ = lean_ctor_get(v_a_1591_, 2);
v_absP_1596_ = lean_nat_add(v_startPos_1594_, v_a_1592_);
v_decide_1597_ = lean_nat_dec_eq(v_absP_1596_, v_stopPos_1595_);
if (v_decide_1597_ == 0)
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = lean_string_utf8_next(v_str_1593_, v_absP_1596_);
lean_dec(v_absP_1596_);
v___x_1599_ = lean_nat_sub(v___x_1598_, v_startPos_1594_);
lean_dec(v___x_1598_);
return v___x_1599_;
}
else
{
lean_dec(v_absP_1596_);
lean_inc(v_a_1592_);
return v_a_1592_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_next___boxed(lean_object* v_a_1600_, lean_object* v_a_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Substring_next(v_a_1600_, v_a_1601_);
lean_dec(v_a_1601_);
lean_dec_ref(v_a_1600_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l_Substring_prev(lean_object* v_a_1603_, lean_object* v_a_1604_){
_start:
{
lean_object* v_str_1605_; lean_object* v_startPos_1606_; lean_object* v_absP_1607_; uint8_t v_decide_1608_; 
v_str_1605_ = lean_ctor_get(v_a_1603_, 0);
v_startPos_1606_ = lean_ctor_get(v_a_1603_, 1);
v_absP_1607_ = lean_nat_add(v_startPos_1606_, v_a_1604_);
v_decide_1608_ = lean_nat_dec_eq(v_absP_1607_, v_startPos_1606_);
if (v_decide_1608_ == 0)
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = lean_string_utf8_prev(v_str_1605_, v_absP_1607_);
lean_dec(v_absP_1607_);
v___x_1610_ = lean_nat_sub(v___x_1609_, v_startPos_1606_);
lean_dec(v___x_1609_);
return v___x_1610_;
}
else
{
lean_dec(v_absP_1607_);
lean_inc(v_a_1604_);
return v_a_1604_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_prev___boxed(lean_object* v_a_1611_, lean_object* v_a_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Substring_prev(v_a_1611_, v_a_1612_);
lean_dec(v_a_1612_);
lean_dec_ref(v_a_1611_);
return v_res_1613_;
}
}
LEAN_EXPORT uint8_t l_Substring_atEnd(lean_object* v_a_1614_, lean_object* v_a_1615_){
_start:
{
lean_object* v_startPos_1616_; lean_object* v_stopPos_1617_; lean_object* v___x_1618_; uint8_t v_decide_1619_; 
v_startPos_1616_ = lean_ctor_get(v_a_1614_, 1);
v_stopPos_1617_ = lean_ctor_get(v_a_1614_, 2);
v___x_1618_ = lean_nat_add(v_startPos_1616_, v_a_1615_);
v_decide_1619_ = lean_nat_dec_eq(v___x_1618_, v_stopPos_1617_);
lean_dec(v___x_1618_);
return v_decide_1619_;
}
}
LEAN_EXPORT lean_object* l_Substring_atEnd___boxed(lean_object* v_a_1620_, lean_object* v_a_1621_){
_start:
{
uint8_t v_res_1622_; lean_object* v_r_1623_; 
v_res_1622_ = l_Substring_atEnd(v_a_1620_, v_a_1621_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
v_r_1623_ = lean_box(v_res_1622_);
return v_r_1623_;
}
}
LEAN_EXPORT uint8_t l_Substring_beq(lean_object* v_ss1_1624_, lean_object* v_ss2_1625_){
_start:
{
uint8_t v___x_1626_; 
v___x_1626_ = l_Substring_Raw_beq(v_ss1_1624_, v_ss2_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Substring_beq___boxed(lean_object* v_ss1_1627_, lean_object* v_ss2_1628_){
_start:
{
uint8_t v_res_1629_; lean_object* v_r_1630_; 
v_res_1629_ = l_Substring_beq(v_ss1_1627_, v_ss2_1628_);
v_r_1630_ = lean_box(v_res_1629_);
return v_r_1630_;
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

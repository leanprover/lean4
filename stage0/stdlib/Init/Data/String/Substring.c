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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_instInhabitedSlice;
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t l_String_Pos_Raw_substrEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(lean_object*);
lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
uint8_t l_String_Slice_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
lean_object* l_String_Slice_revPositions(lean_object*);
lean_object* l_String_Slice_positions(lean_object*);
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
static lean_once_cell_t l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__0;
static lean_once_cell_t l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__1;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_toNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_str_82_; lean_object* v_startPos_83_; lean_object* v_stopPos_84_; lean_object* v_absP_85_; uint8_t v___x_86_; 
v_str_82_ = lean_ctor_get(v_x_80_, 0);
v_startPos_83_ = lean_ctor_get(v_x_80_, 1);
v_stopPos_84_ = lean_ctor_get(v_x_80_, 2);
v_absP_85_ = lean_nat_add(v_startPos_83_, v_x_81_);
v___x_86_ = lean_nat_dec_eq(v_absP_85_, v_stopPos_84_);
if (v___x_86_ == 0)
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
lean_object* v___x_103_; 
v___x_103_ = l___private_Init_Data_String_Substring_0__Substring_Raw_get_match__1_splitter___redArg(v_x_100_, v_x_101_, v_h__1_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_prev(lean_object* v_x_104_, lean_object* v_x_105_){
_start:
{
lean_object* v_str_106_; lean_object* v_startPos_107_; lean_object* v_absP_108_; uint8_t v___x_109_; 
v_str_106_ = lean_ctor_get(v_x_104_, 0);
v_startPos_107_ = lean_ctor_get(v_x_104_, 1);
v_absP_108_ = lean_nat_add(v_startPos_107_, v_x_105_);
v___x_109_ = lean_nat_dec_eq(v_absP_108_, v_startPos_107_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_string_utf8_prev(v_str_106_, v_absP_108_);
lean_dec(v_absP_108_);
v___x_111_ = lean_nat_sub(v___x_110_, v_startPos_107_);
lean_dec(v___x_110_);
return v___x_111_;
}
else
{
lean_dec(v_absP_108_);
lean_inc(v_x_105_);
return v_x_105_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_prev___boxed(lean_object* v_x_112_, lean_object* v_x_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Substring_Raw_prev(v_x_112_, v_x_113_);
lean_dec(v_x_113_);
lean_dec_ref(v_x_112_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* lean_substring_prev(lean_object* v_a_115_, lean_object* v_a_116_){
_start:
{
lean_object* v_str_117_; lean_object* v_startPos_118_; lean_object* v_absP_119_; uint8_t v___x_120_; 
v_str_117_ = lean_ctor_get(v_a_115_, 0);
lean_inc_ref(v_str_117_);
v_startPos_118_ = lean_ctor_get(v_a_115_, 1);
lean_inc(v_startPos_118_);
lean_dec_ref(v_a_115_);
v_absP_119_ = lean_nat_add(v_startPos_118_, v_a_116_);
v___x_120_ = lean_nat_dec_eq(v_absP_119_, v_startPos_118_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; lean_object* v___x_122_; 
lean_dec(v_a_116_);
v___x_121_ = lean_string_utf8_prev(v_str_117_, v_absP_119_);
lean_dec(v_absP_119_);
lean_dec_ref(v_str_117_);
v___x_122_ = lean_nat_sub(v___x_121_, v_startPos_118_);
lean_dec(v_startPos_118_);
lean_dec(v___x_121_);
return v___x_122_;
}
else
{
lean_dec(v_absP_119_);
lean_dec(v_startPos_118_);
lean_dec_ref(v_str_117_);
return v_a_116_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_nextn(lean_object* v_x_123_, lean_object* v_x_124_, lean_object* v_x_125_){
_start:
{
lean_object* v_zero_126_; uint8_t v_isZero_127_; 
v_zero_126_ = lean_unsigned_to_nat(0u);
v_isZero_127_ = lean_nat_dec_eq(v_x_124_, v_zero_126_);
if (v_isZero_127_ == 1)
{
lean_dec(v_x_124_);
return v_x_125_;
}
else
{
lean_object* v_str_128_; lean_object* v_startPos_129_; lean_object* v_stopPos_130_; lean_object* v_one_131_; lean_object* v_n_132_; lean_object* v_absP_133_; uint8_t v___x_134_; 
v_str_128_ = lean_ctor_get(v_x_123_, 0);
v_startPos_129_ = lean_ctor_get(v_x_123_, 1);
v_stopPos_130_ = lean_ctor_get(v_x_123_, 2);
v_one_131_ = lean_unsigned_to_nat(1u);
v_n_132_ = lean_nat_sub(v_x_124_, v_one_131_);
lean_dec(v_x_124_);
v_absP_133_ = lean_nat_add(v_startPos_129_, v_x_125_);
v___x_134_ = lean_nat_dec_eq(v_absP_133_, v_stopPos_130_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; lean_object* v___x_136_; 
lean_dec(v_x_125_);
v___x_135_ = lean_string_utf8_next(v_str_128_, v_absP_133_);
lean_dec(v_absP_133_);
v___x_136_ = lean_nat_sub(v___x_135_, v_startPos_129_);
lean_dec(v___x_135_);
v_x_124_ = v_n_132_;
v_x_125_ = v___x_136_;
goto _start;
}
else
{
lean_dec(v_absP_133_);
v_x_124_ = v_n_132_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_nextn___boxed(lean_object* v_x_139_, lean_object* v_x_140_, lean_object* v_x_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Substring_Raw_nextn(v_x_139_, v_x_140_, v_x_141_);
lean_dec_ref(v_x_139_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_prevn(lean_object* v_x_143_, lean_object* v_x_144_, lean_object* v_x_145_){
_start:
{
lean_object* v_zero_146_; uint8_t v_isZero_147_; 
v_zero_146_ = lean_unsigned_to_nat(0u);
v_isZero_147_ = lean_nat_dec_eq(v_x_144_, v_zero_146_);
if (v_isZero_147_ == 1)
{
lean_dec(v_x_144_);
return v_x_145_;
}
else
{
lean_object* v_str_148_; lean_object* v_startPos_149_; lean_object* v_one_150_; lean_object* v_n_151_; lean_object* v_absP_152_; uint8_t v___x_153_; 
v_str_148_ = lean_ctor_get(v_x_143_, 0);
v_startPos_149_ = lean_ctor_get(v_x_143_, 1);
v_one_150_ = lean_unsigned_to_nat(1u);
v_n_151_ = lean_nat_sub(v_x_144_, v_one_150_);
lean_dec(v_x_144_);
v_absP_152_ = lean_nat_add(v_startPos_149_, v_x_145_);
v___x_153_ = lean_nat_dec_eq(v_absP_152_, v_startPos_149_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; 
lean_dec(v_x_145_);
v___x_154_ = lean_string_utf8_prev(v_str_148_, v_absP_152_);
lean_dec(v_absP_152_);
v___x_155_ = lean_nat_sub(v___x_154_, v_startPos_149_);
lean_dec(v___x_154_);
v_x_144_ = v_n_151_;
v_x_145_ = v___x_155_;
goto _start;
}
else
{
lean_dec(v_absP_152_);
v_x_144_ = v_n_151_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_prevn___boxed(lean_object* v_x_158_, lean_object* v_x_159_, lean_object* v_x_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Substring_Raw_prevn(v_x_158_, v_x_159_, v_x_160_);
lean_dec_ref(v_x_158_);
return v_res_161_;
}
}
LEAN_EXPORT uint32_t l_Substring_Raw_front(lean_object* v_s_162_){
_start:
{
lean_object* v_str_163_; lean_object* v_startPos_164_; uint32_t v___x_165_; 
v_str_163_ = lean_ctor_get(v_s_162_, 0);
v_startPos_164_ = lean_ctor_get(v_s_162_, 1);
v___x_165_ = lean_string_utf8_get(v_str_163_, v_startPos_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_front___boxed(lean_object* v_s_166_){
_start:
{
uint32_t v_res_167_; lean_object* v_r_168_; 
v_res_167_ = l_Substring_Raw_front(v_s_166_);
lean_dec_ref(v_s_166_);
v_r_168_ = lean_box_uint32(v_res_167_);
return v_r_168_;
}
}
LEAN_EXPORT uint32_t lean_substring_front(lean_object* v_s_169_){
_start:
{
lean_object* v_str_170_; lean_object* v_startPos_171_; uint32_t v___x_172_; 
v_str_170_ = lean_ctor_get(v_s_169_, 0);
lean_inc_ref(v_str_170_);
v_startPos_171_ = lean_ctor_get(v_s_169_, 1);
lean_inc(v_startPos_171_);
lean_dec_ref(v_s_169_);
v___x_172_ = lean_string_utf8_get(v_str_170_, v_startPos_171_);
lean_dec(v_startPos_171_);
lean_dec_ref(v_str_170_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_frontImpl___boxed(lean_object* v_s_173_){
_start:
{
uint32_t v_res_174_; lean_object* v_r_175_; 
v_res_174_ = lean_substring_front(v_s_173_);
v_r_175_ = lean_box_uint32(v_res_174_);
return v_r_175_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_posOf___lam__0(lean_object* v_stopPos_176_, lean_object* v_startPos_177_, lean_object* v_str_178_, uint32_t v_c_179_, lean_object* v___x_180_, lean_object* v_it_181_, lean_object* v_acc_182_, lean_object* v_hP_183_, lean_object* v_recur_184_){
_start:
{
lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_185_ = lean_nat_sub(v_stopPos_176_, v_startPos_177_);
v___x_186_ = lean_nat_dec_eq(v_it_181_, v___x_185_);
lean_dec(v___x_185_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; uint32_t v___x_188_; uint8_t v___x_189_; 
v___x_187_ = lean_nat_add(v_startPos_177_, v_it_181_);
v___x_188_ = lean_string_utf8_get_fast(v_str_178_, v___x_187_);
v___x_189_ = lean_uint32_dec_eq(v___x_188_, v_c_179_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
lean_dec(v_it_181_);
v___x_190_ = lean_string_utf8_next_fast(v_str_178_, v___x_187_);
lean_dec(v___x_187_);
v___x_191_ = lean_nat_sub(v___x_190_, v_startPos_177_);
v___x_192_ = lean_apply_4(v_recur_184_, v___x_191_, v___x_180_, lean_box(0), lean_box(0));
return v___x_192_;
}
else
{
lean_object* v___x_193_; 
lean_dec(v___x_187_);
lean_dec_ref(v_recur_184_);
lean_dec(v___x_180_);
v___x_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_193_, 0, v_it_181_);
return v___x_193_;
}
}
else
{
lean_dec_ref(v_recur_184_);
lean_dec(v_it_181_);
lean_dec(v___x_180_);
lean_inc(v_acc_182_);
return v_acc_182_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_posOf___lam__0___boxed(lean_object* v_stopPos_194_, lean_object* v_startPos_195_, lean_object* v_str_196_, lean_object* v_c_197_, lean_object* v___x_198_, lean_object* v_it_199_, lean_object* v_acc_200_, lean_object* v_hP_201_, lean_object* v_recur_202_){
_start:
{
uint32_t v_c_boxed_203_; lean_object* v_res_204_; 
v_c_boxed_203_ = lean_unbox_uint32(v_c_197_);
lean_dec(v_c_197_);
v_res_204_ = l_Substring_Raw_posOf___lam__0(v_stopPos_194_, v_startPos_195_, v_str_196_, v_c_boxed_203_, v___x_198_, v_it_199_, v_acc_200_, v_hP_201_, v_recur_202_);
lean_dec(v_acc_200_);
lean_dec_ref(v_str_196_);
lean_dec(v_startPos_195_);
lean_dec(v_stopPos_194_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_posOf(lean_object* v_s_205_, uint32_t v_c_206_){
_start:
{
lean_object* v_str_207_; lean_object* v_startPos_208_; lean_object* v_stopPos_209_; uint8_t v___x_210_; 
v_str_207_ = lean_ctor_get(v_s_205_, 0);
lean_inc_ref(v_str_207_);
v_startPos_208_ = lean_ctor_get(v_s_205_, 1);
lean_inc(v_startPos_208_);
v_stopPos_209_ = lean_ctor_get(v_s_205_, 2);
lean_inc(v_stopPos_209_);
lean_dec_ref(v_s_205_);
v___x_210_ = lean_string_is_valid_pos(v_str_207_, v_startPos_208_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; 
lean_dec_ref(v_str_207_);
v___x_211_ = lean_nat_sub(v_stopPos_209_, v_startPos_208_);
lean_dec(v_startPos_208_);
lean_dec(v_stopPos_209_);
return v___x_211_;
}
else
{
uint8_t v___x_212_; 
v___x_212_ = lean_string_is_valid_pos(v_str_207_, v_stopPos_209_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; 
lean_dec_ref(v_str_207_);
v___x_213_ = lean_nat_sub(v_stopPos_209_, v_startPos_208_);
lean_dec(v_startPos_208_);
lean_dec(v_stopPos_209_);
return v___x_213_;
}
else
{
uint8_t v___x_214_; 
v___x_214_ = lean_nat_dec_le(v_startPos_208_, v_stopPos_209_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; 
lean_dec_ref(v_str_207_);
v___x_215_ = lean_nat_sub(v_stopPos_209_, v_startPos_208_);
lean_dec(v_startPos_208_);
lean_dec(v_stopPos_209_);
return v___x_215_;
}
else
{
lean_object* v_searcher_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___f_219_; lean_object* v___x_220_; 
v_searcher_216_ = lean_unsigned_to_nat(0u);
v___x_217_ = lean_box(0);
v___x_218_ = lean_box_uint32(v_c_206_);
lean_inc(v_startPos_208_);
lean_inc(v_stopPos_209_);
v___f_219_ = lean_alloc_closure((void*)(l_Substring_Raw_posOf___lam__0___boxed), 9, 5);
lean_closure_set(v___f_219_, 0, v_stopPos_209_);
lean_closure_set(v___f_219_, 1, v_startPos_208_);
lean_closure_set(v___f_219_, 2, v_str_207_);
lean_closure_set(v___f_219_, 3, v___x_218_);
lean_closure_set(v___f_219_, 4, v___x_217_);
v___x_220_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_219_, v_searcher_216_, v___x_217_, lean_box(0));
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v___x_221_; 
v___x_221_ = lean_nat_sub(v_stopPos_209_, v_startPos_208_);
lean_dec(v_startPos_208_);
lean_dec(v_stopPos_209_);
return v___x_221_;
}
else
{
lean_object* v_val_222_; 
lean_dec(v_stopPos_209_);
lean_dec(v_startPos_208_);
v_val_222_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_val_222_);
lean_dec_ref(v___x_220_);
return v_val_222_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_posOf___boxed(lean_object* v_s_223_, lean_object* v_c_224_){
_start:
{
uint32_t v_c_boxed_225_; lean_object* v_res_226_; 
v_c_boxed_225_ = lean_unbox_uint32(v_c_224_);
lean_dec(v_c_224_);
v_res_226_ = l_Substring_Raw_posOf(v_s_223_, v_c_boxed_225_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_drop(lean_object* v_x_227_, lean_object* v_x_228_){
_start:
{
lean_object* v_str_229_; lean_object* v_startPos_230_; lean_object* v_stopPos_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_241_; 
v_str_229_ = lean_ctor_get(v_x_227_, 0);
lean_inc_ref(v_str_229_);
v_startPos_230_ = lean_ctor_get(v_x_227_, 1);
lean_inc(v_startPos_230_);
v_stopPos_231_ = lean_ctor_get(v_x_227_, 2);
lean_inc(v_stopPos_231_);
v___x_232_ = lean_unsigned_to_nat(0u);
v___x_233_ = l_Substring_Raw_nextn(v_x_227_, v_x_228_, v___x_232_);
v_isSharedCheck_241_ = !lean_is_exclusive(v_x_227_);
if (v_isSharedCheck_241_ == 0)
{
lean_object* v_unused_242_; lean_object* v_unused_243_; lean_object* v_unused_244_; 
v_unused_242_ = lean_ctor_get(v_x_227_, 2);
lean_dec(v_unused_242_);
v_unused_243_ = lean_ctor_get(v_x_227_, 1);
lean_dec(v_unused_243_);
v_unused_244_ = lean_ctor_get(v_x_227_, 0);
lean_dec(v_unused_244_);
v___x_235_ = v_x_227_;
v_isShared_236_ = v_isSharedCheck_241_;
goto v_resetjp_234_;
}
else
{
lean_dec(v_x_227_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_241_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_237_ = lean_nat_add(v_startPos_230_, v___x_233_);
lean_dec(v___x_233_);
lean_dec(v_startPos_230_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 1, v___x_237_);
v___x_239_ = v___x_235_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_str_229_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v___x_237_);
lean_ctor_set(v_reuseFailAlloc_240_, 2, v_stopPos_231_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
LEAN_EXPORT lean_object* lean_substring_drop(lean_object* v_a_245_, lean_object* v_a_246_){
_start:
{
lean_object* v_str_247_; lean_object* v_startPos_248_; lean_object* v_stopPos_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_259_; 
v_str_247_ = lean_ctor_get(v_a_245_, 0);
lean_inc_ref(v_str_247_);
v_startPos_248_ = lean_ctor_get(v_a_245_, 1);
lean_inc(v_startPos_248_);
v_stopPos_249_ = lean_ctor_get(v_a_245_, 2);
lean_inc(v_stopPos_249_);
v___x_250_ = lean_unsigned_to_nat(0u);
v___x_251_ = l_Substring_Raw_nextn(v_a_245_, v_a_246_, v___x_250_);
v_isSharedCheck_259_ = !lean_is_exclusive(v_a_245_);
if (v_isSharedCheck_259_ == 0)
{
lean_object* v_unused_260_; lean_object* v_unused_261_; lean_object* v_unused_262_; 
v_unused_260_ = lean_ctor_get(v_a_245_, 2);
lean_dec(v_unused_260_);
v_unused_261_ = lean_ctor_get(v_a_245_, 1);
lean_dec(v_unused_261_);
v_unused_262_ = lean_ctor_get(v_a_245_, 0);
lean_dec(v_unused_262_);
v___x_253_ = v_a_245_;
v_isShared_254_ = v_isSharedCheck_259_;
goto v_resetjp_252_;
}
else
{
lean_dec(v_a_245_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_259_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_255_; lean_object* v___x_257_; 
v___x_255_ = lean_nat_add(v_startPos_248_, v___x_251_);
lean_dec(v___x_251_);
lean_dec(v_startPos_248_);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 1, v___x_255_);
v___x_257_ = v___x_253_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_str_247_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v___x_255_);
lean_ctor_set(v_reuseFailAlloc_258_, 2, v_stopPos_249_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropRight(lean_object* v_x_263_, lean_object* v_x_264_){
_start:
{
lean_object* v_str_265_; lean_object* v_startPos_266_; lean_object* v_stopPos_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_277_; 
v_str_265_ = lean_ctor_get(v_x_263_, 0);
lean_inc_ref(v_str_265_);
v_startPos_266_ = lean_ctor_get(v_x_263_, 1);
lean_inc(v_startPos_266_);
v_stopPos_267_ = lean_ctor_get(v_x_263_, 2);
v___x_268_ = lean_nat_sub(v_stopPos_267_, v_startPos_266_);
v___x_269_ = l_Substring_Raw_prevn(v_x_263_, v_x_264_, v___x_268_);
v_isSharedCheck_277_ = !lean_is_exclusive(v_x_263_);
if (v_isSharedCheck_277_ == 0)
{
lean_object* v_unused_278_; lean_object* v_unused_279_; lean_object* v_unused_280_; 
v_unused_278_ = lean_ctor_get(v_x_263_, 2);
lean_dec(v_unused_278_);
v_unused_279_ = lean_ctor_get(v_x_263_, 1);
lean_dec(v_unused_279_);
v_unused_280_ = lean_ctor_get(v_x_263_, 0);
lean_dec(v_unused_280_);
v___x_271_ = v_x_263_;
v_isShared_272_ = v_isSharedCheck_277_;
goto v_resetjp_270_;
}
else
{
lean_dec(v_x_263_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_277_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_273_ = lean_nat_add(v_startPos_266_, v___x_269_);
lean_dec(v___x_269_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 2, v___x_273_);
v___x_275_ = v___x_271_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_str_265_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v_startPos_266_);
lean_ctor_set(v_reuseFailAlloc_276_, 2, v___x_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_take(lean_object* v_x_281_, lean_object* v_x_282_){
_start:
{
lean_object* v_str_283_; lean_object* v_startPos_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_294_; 
v_str_283_ = lean_ctor_get(v_x_281_, 0);
lean_inc_ref(v_str_283_);
v_startPos_284_ = lean_ctor_get(v_x_281_, 1);
lean_inc(v_startPos_284_);
v___x_285_ = lean_unsigned_to_nat(0u);
v___x_286_ = l_Substring_Raw_nextn(v_x_281_, v_x_282_, v___x_285_);
v_isSharedCheck_294_ = !lean_is_exclusive(v_x_281_);
if (v_isSharedCheck_294_ == 0)
{
lean_object* v_unused_295_; lean_object* v_unused_296_; lean_object* v_unused_297_; 
v_unused_295_ = lean_ctor_get(v_x_281_, 2);
lean_dec(v_unused_295_);
v_unused_296_ = lean_ctor_get(v_x_281_, 1);
lean_dec(v_unused_296_);
v_unused_297_ = lean_ctor_get(v_x_281_, 0);
lean_dec(v_unused_297_);
v___x_288_ = v_x_281_;
v_isShared_289_ = v_isSharedCheck_294_;
goto v_resetjp_287_;
}
else
{
lean_dec(v_x_281_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_294_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_290_; lean_object* v___x_292_; 
v___x_290_ = lean_nat_add(v_startPos_284_, v___x_286_);
lean_dec(v___x_286_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 2, v___x_290_);
v___x_292_ = v___x_288_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_str_283_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v_startPos_284_);
lean_ctor_set(v_reuseFailAlloc_293_, 2, v___x_290_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRight(lean_object* v_x_298_, lean_object* v_x_299_){
_start:
{
lean_object* v_str_300_; lean_object* v_startPos_301_; lean_object* v_stopPos_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_312_; 
v_str_300_ = lean_ctor_get(v_x_298_, 0);
lean_inc_ref(v_str_300_);
v_startPos_301_ = lean_ctor_get(v_x_298_, 1);
lean_inc(v_startPos_301_);
v_stopPos_302_ = lean_ctor_get(v_x_298_, 2);
lean_inc(v_stopPos_302_);
v___x_303_ = lean_nat_sub(v_stopPos_302_, v_startPos_301_);
v___x_304_ = l_Substring_Raw_prevn(v_x_298_, v_x_299_, v___x_303_);
v_isSharedCheck_312_ = !lean_is_exclusive(v_x_298_);
if (v_isSharedCheck_312_ == 0)
{
lean_object* v_unused_313_; lean_object* v_unused_314_; lean_object* v_unused_315_; 
v_unused_313_ = lean_ctor_get(v_x_298_, 2);
lean_dec(v_unused_313_);
v_unused_314_ = lean_ctor_get(v_x_298_, 1);
lean_dec(v_unused_314_);
v_unused_315_ = lean_ctor_get(v_x_298_, 0);
lean_dec(v_unused_315_);
v___x_306_ = v_x_298_;
v_isShared_307_ = v_isSharedCheck_312_;
goto v_resetjp_305_;
}
else
{
lean_dec(v_x_298_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_312_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_308_; lean_object* v___x_310_; 
v___x_308_ = lean_nat_add(v_startPos_301_, v___x_304_);
lean_dec(v___x_304_);
lean_dec(v_startPos_301_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 1, v___x_308_);
v___x_310_ = v___x_306_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_str_300_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v___x_308_);
lean_ctor_set(v_reuseFailAlloc_311_, 2, v_stopPos_302_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_atEnd(lean_object* v_x_316_, lean_object* v_x_317_){
_start:
{
lean_object* v_startPos_318_; lean_object* v_stopPos_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v_startPos_318_ = lean_ctor_get(v_x_316_, 1);
v_stopPos_319_ = lean_ctor_get(v_x_316_, 2);
v___x_320_ = lean_nat_add(v_startPos_318_, v_x_317_);
v___x_321_ = lean_nat_dec_eq(v___x_320_, v_stopPos_319_);
lean_dec(v___x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_atEnd___boxed(lean_object* v_x_322_, lean_object* v_x_323_){
_start:
{
uint8_t v_res_324_; lean_object* v_r_325_; 
v_res_324_ = l_Substring_Raw_atEnd(v_x_322_, v_x_323_);
lean_dec(v_x_323_);
lean_dec_ref(v_x_322_);
v_r_325_ = lean_box(v_res_324_);
return v_r_325_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_extract(lean_object* v_x_330_, lean_object* v_x_331_, lean_object* v_x_332_){
_start:
{
lean_object* v_str_333_; lean_object* v_startPos_334_; lean_object* v_stopPos_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_353_; 
v_str_333_ = lean_ctor_get(v_x_330_, 0);
v_startPos_334_ = lean_ctor_get(v_x_330_, 1);
v_stopPos_335_ = lean_ctor_get(v_x_330_, 2);
v_isSharedCheck_353_ = !lean_is_exclusive(v_x_330_);
if (v_isSharedCheck_353_ == 0)
{
v___x_337_ = v_x_330_;
v_isShared_338_ = v_isSharedCheck_353_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_stopPos_335_);
lean_inc(v_startPos_334_);
lean_inc(v_str_333_);
lean_dec(v_x_330_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_353_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___y_340_; uint8_t v___x_349_; 
v___x_349_ = lean_nat_dec_le(v_x_332_, v_x_331_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = lean_nat_add(v_startPos_334_, v_x_331_);
v___x_351_ = lean_nat_dec_le(v_stopPos_335_, v___x_350_);
if (v___x_351_ == 0)
{
v___y_340_ = v___x_350_;
goto v___jp_339_;
}
else
{
lean_dec(v___x_350_);
lean_inc(v_stopPos_335_);
v___y_340_ = v_stopPos_335_;
goto v___jp_339_;
}
}
else
{
lean_object* v___x_352_; 
lean_del_object(v___x_337_);
lean_dec(v_stopPos_335_);
lean_dec(v_startPos_334_);
lean_dec_ref(v_str_333_);
v___x_352_ = ((lean_object*)(l_Substring_Raw_extract___closed__1));
return v___x_352_;
}
v___jp_339_:
{
lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_341_ = lean_nat_add(v_startPos_334_, v_x_332_);
lean_dec(v_startPos_334_);
v___x_342_ = lean_nat_dec_le(v_stopPos_335_, v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_344_; 
lean_dec(v_stopPos_335_);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 2, v___x_341_);
lean_ctor_set(v___x_337_, 1, v___y_340_);
v___x_344_ = v___x_337_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_str_333_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v___y_340_);
lean_ctor_set(v_reuseFailAlloc_345_, 2, v___x_341_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
else
{
lean_object* v___x_347_; 
lean_dec(v___x_341_);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 1, v___y_340_);
v___x_347_ = v___x_337_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_str_333_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v___y_340_);
lean_ctor_set(v_reuseFailAlloc_348_, 2, v_stopPos_335_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_extract___boxed(lean_object* v_x_354_, lean_object* v_x_355_, lean_object* v_x_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Substring_Raw_extract(v_x_354_, v_x_355_, v_x_356_);
lean_dec(v_x_356_);
lean_dec(v_x_355_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* lean_substring_extract(lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v_str_361_; lean_object* v_startPos_362_; lean_object* v_stopPos_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_381_; 
v_str_361_ = lean_ctor_get(v_a_358_, 0);
v_startPos_362_ = lean_ctor_get(v_a_358_, 1);
v_stopPos_363_ = lean_ctor_get(v_a_358_, 2);
v_isSharedCheck_381_ = !lean_is_exclusive(v_a_358_);
if (v_isSharedCheck_381_ == 0)
{
v___x_365_ = v_a_358_;
v_isShared_366_ = v_isSharedCheck_381_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_stopPos_363_);
lean_inc(v_startPos_362_);
lean_inc(v_str_361_);
lean_dec(v_a_358_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_381_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___y_368_; uint8_t v___x_377_; 
v___x_377_ = lean_nat_dec_le(v_a_360_, v_a_359_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_378_ = lean_nat_add(v_startPos_362_, v_a_359_);
lean_dec(v_a_359_);
v___x_379_ = lean_nat_dec_le(v_stopPos_363_, v___x_378_);
if (v___x_379_ == 0)
{
v___y_368_ = v___x_378_;
goto v___jp_367_;
}
else
{
lean_dec(v___x_378_);
lean_inc(v_stopPos_363_);
v___y_368_ = v_stopPos_363_;
goto v___jp_367_;
}
}
else
{
lean_object* v___x_380_; 
lean_del_object(v___x_365_);
lean_dec(v_stopPos_363_);
lean_dec(v_startPos_362_);
lean_dec_ref(v_str_361_);
lean_dec(v_a_360_);
lean_dec(v_a_359_);
v___x_380_ = ((lean_object*)(l_Substring_Raw_extract___closed__1));
return v___x_380_;
}
v___jp_367_:
{
lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_369_ = lean_nat_add(v_startPos_362_, v_a_360_);
lean_dec(v_a_360_);
lean_dec(v_startPos_362_);
v___x_370_ = lean_nat_dec_le(v_stopPos_363_, v___x_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_372_; 
lean_dec(v_stopPos_363_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 2, v___x_369_);
lean_ctor_set(v___x_365_, 1, v___y_368_);
v___x_372_ = v___x_365_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_str_361_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v___y_368_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v___x_369_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
else
{
lean_object* v___x_375_; 
lean_dec(v___x_369_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 1, v___y_368_);
v___x_375_ = v___x_365_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_str_361_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v___y_368_);
lean_ctor_set(v_reuseFailAlloc_376_, 2, v_stopPos_363_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__0(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = ((lean_object*)(l_Substring_Raw_extract___closed__0));
v___x_383_ = lean_string_utf8_byte_size(v___x_382_);
return v___x_383_;
}
}
static lean_object* _init_l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__1(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_384_ = lean_obj_once(&l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__0, &l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__0_once, _init_l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__0);
v___x_385_ = lean_unsigned_to_nat(0u);
v___x_386_ = ((lean_object*)(l_Substring_Raw_extract___closed__0));
v___x_387_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
lean_ctor_set(v___x_387_, 1, v___x_385_);
lean_ctor_set(v___x_387_, 2, v___x_384_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop(lean_object* v_s_388_, lean_object* v_sep_389_, lean_object* v_b_390_, lean_object* v_i_391_, lean_object* v_j_392_, lean_object* v_r_393_){
_start:
{
lean_object* v___y_395_; lean_object* v___y_399_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v_str_408_; lean_object* v_startPos_409_; lean_object* v_stopPos_410_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___y_414_; lean_object* v___y_415_; lean_object* v___y_421_; lean_object* v___y_432_; lean_object* v___x_437_; uint8_t v___x_438_; 
v_str_408_ = lean_ctor_get(v_s_388_, 0);
v_startPos_409_ = lean_ctor_get(v_s_388_, 1);
v_stopPos_410_ = lean_ctor_get(v_s_388_, 2);
v___x_437_ = lean_nat_sub(v_stopPos_410_, v_startPos_409_);
v___x_438_ = lean_nat_dec_lt(v_i_391_, v___x_437_);
lean_dec(v___x_437_);
if (v___x_438_ == 0)
{
lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_468_; 
lean_inc(v_stopPos_410_);
lean_inc(v_startPos_409_);
lean_inc_ref(v_str_408_);
v_isSharedCheck_468_ = !lean_is_exclusive(v_s_388_);
if (v_isSharedCheck_468_ == 0)
{
lean_object* v_unused_469_; lean_object* v_unused_470_; lean_object* v_unused_471_; 
v_unused_469_ = lean_ctor_get(v_s_388_, 2);
lean_dec(v_unused_469_);
v_unused_470_ = lean_ctor_get(v_s_388_, 1);
lean_dec(v_unused_470_);
v_unused_471_ = lean_ctor_get(v_s_388_, 0);
lean_dec(v_unused_471_);
v___x_440_ = v_s_388_;
v_isShared_441_ = v_isSharedCheck_468_;
goto v_resetjp_439_;
}
else
{
lean_dec(v_s_388_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_468_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
uint8_t v___x_442_; 
v___x_442_ = lean_string_utf8_at_end(v_sep_389_, v_j_392_);
if (v___x_442_ == 0)
{
uint8_t v___x_443_; 
lean_del_object(v___x_440_);
lean_dec(v_j_392_);
v___x_443_ = lean_nat_dec_le(v_i_391_, v_b_390_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_444_ = lean_nat_add(v_startPos_409_, v_b_390_);
lean_dec(v_b_390_);
v___x_445_ = lean_nat_dec_le(v_stopPos_410_, v___x_444_);
if (v___x_445_ == 0)
{
v___y_432_ = v___x_444_;
goto v___jp_431_;
}
else
{
lean_dec(v___x_444_);
lean_inc(v_stopPos_410_);
v___y_432_ = v_stopPos_410_;
goto v___jp_431_;
}
}
else
{
lean_object* v___x_446_; 
lean_dec(v_stopPos_410_);
lean_dec(v_startPos_409_);
lean_dec_ref(v_str_408_);
lean_dec(v_i_391_);
lean_dec(v_b_390_);
v___x_446_ = ((lean_object*)(l_Substring_Raw_extract___closed__1));
v___y_395_ = v___x_446_;
goto v___jp_394_;
}
}
else
{
lean_object* v___x_447_; lean_object* v___y_449_; lean_object* v___x_453_; lean_object* v___y_455_; uint8_t v___x_464_; 
v___x_447_ = lean_obj_once(&l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__1, &l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__1_once, _init_l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__1);
v___x_453_ = lean_nat_sub(v_i_391_, v_j_392_);
lean_dec(v_j_392_);
lean_dec(v_i_391_);
v___x_464_ = lean_nat_dec_le(v___x_453_, v_b_390_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; uint8_t v___x_466_; 
v___x_465_ = lean_nat_add(v_startPos_409_, v_b_390_);
lean_dec(v_b_390_);
v___x_466_ = lean_nat_dec_le(v_stopPos_410_, v___x_465_);
if (v___x_466_ == 0)
{
v___y_455_ = v___x_465_;
goto v___jp_454_;
}
else
{
lean_dec(v___x_465_);
lean_inc(v_stopPos_410_);
v___y_455_ = v_stopPos_410_;
goto v___jp_454_;
}
}
else
{
lean_object* v___x_467_; 
lean_dec(v___x_453_);
lean_del_object(v___x_440_);
lean_dec(v_stopPos_410_);
lean_dec(v_startPos_409_);
lean_dec_ref(v_str_408_);
lean_dec(v_b_390_);
v___x_467_ = ((lean_object*)(l_Substring_Raw_extract___closed__1));
v___y_449_ = v___x_467_;
goto v___jp_448_;
}
v___jp_448_:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_450_, 0, v___y_449_);
lean_ctor_set(v___x_450_, 1, v_r_393_);
v___x_451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_447_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
v___x_452_ = l_List_reverse___redArg(v___x_451_);
return v___x_452_;
}
v___jp_454_:
{
lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_456_ = lean_nat_add(v_startPos_409_, v___x_453_);
lean_dec(v___x_453_);
lean_dec(v_startPos_409_);
v___x_457_ = lean_nat_dec_le(v_stopPos_410_, v___x_456_);
if (v___x_457_ == 0)
{
lean_object* v___x_459_; 
lean_dec(v_stopPos_410_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 2, v___x_456_);
lean_ctor_set(v___x_440_, 1, v___y_455_);
v___x_459_ = v___x_440_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_str_408_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v___y_455_);
lean_ctor_set(v_reuseFailAlloc_460_, 2, v___x_456_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
v___y_449_ = v___x_459_;
goto v___jp_448_;
}
}
else
{
lean_object* v___x_462_; 
lean_dec(v___x_456_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 1, v___y_455_);
v___x_462_ = v___x_440_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_str_408_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v___y_455_);
lean_ctor_set(v_reuseFailAlloc_463_, 2, v_stopPos_410_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
v___y_449_ = v___x_462_;
goto v___jp_448_;
}
}
}
}
}
}
else
{
lean_object* v___x_472_; uint32_t v___x_473_; uint32_t v___x_474_; uint8_t v___x_475_; 
v___x_472_ = lean_nat_add(v_startPos_409_, v_i_391_);
v___x_473_ = lean_string_utf8_get(v_str_408_, v___x_472_);
v___x_474_ = lean_string_utf8_get(v_sep_389_, v_j_392_);
v___x_475_ = lean_uint32_dec_eq(v___x_473_, v___x_474_);
if (v___x_475_ == 0)
{
uint8_t v___x_476_; 
lean_dec(v_j_392_);
v___x_476_ = lean_nat_dec_eq(v___x_472_, v_stopPos_410_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec(v_i_391_);
v___x_477_ = lean_string_utf8_next(v_str_408_, v___x_472_);
lean_dec(v___x_472_);
v___x_478_ = lean_nat_sub(v___x_477_, v_startPos_409_);
lean_dec(v___x_477_);
v___y_399_ = v___x_478_;
goto v___jp_398_;
}
else
{
lean_dec(v___x_472_);
v___y_399_ = v_i_391_;
goto v___jp_398_;
}
}
else
{
uint8_t v___x_479_; 
v___x_479_ = lean_nat_dec_eq(v___x_472_, v_stopPos_410_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; lean_object* v___x_481_; 
lean_dec(v_i_391_);
v___x_480_ = lean_string_utf8_next(v_str_408_, v___x_472_);
lean_dec(v___x_472_);
v___x_481_ = lean_nat_sub(v___x_480_, v_startPos_409_);
lean_dec(v___x_480_);
v___y_421_ = v___x_481_;
goto v___jp_420_;
}
else
{
lean_dec(v___x_472_);
v___y_421_ = v_i_391_;
goto v___jp_420_;
}
}
}
v___jp_394_:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_396_, 0, v___y_395_);
lean_ctor_set(v___x_396_, 1, v_r_393_);
v___x_397_ = l_List_reverse___redArg(v___x_396_);
return v___x_397_;
}
v___jp_398_:
{
lean_object* v___x_400_; 
v___x_400_ = lean_unsigned_to_nat(0u);
v_i_391_ = v___y_399_;
v_j_392_ = v___x_400_;
goto _start;
}
v___jp_402_:
{
lean_object* v___x_406_; 
v___x_406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_406_, 0, v___y_405_);
lean_ctor_set(v___x_406_, 1, v_r_393_);
lean_inc(v___y_403_);
v_b_390_ = v___y_403_;
v_i_391_ = v___y_403_;
v_j_392_ = v___y_404_;
v_r_393_ = v___x_406_;
goto _start;
}
v___jp_411_:
{
lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_416_ = lean_nat_add(v_startPos_409_, v___y_413_);
lean_dec(v___y_413_);
v___x_417_ = lean_nat_dec_le(v_stopPos_410_, v___x_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; 
lean_inc_ref(v_str_408_);
v___x_418_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_418_, 0, v_str_408_);
lean_ctor_set(v___x_418_, 1, v___y_415_);
lean_ctor_set(v___x_418_, 2, v___x_416_);
v___y_403_ = v___y_412_;
v___y_404_ = v___y_414_;
v___y_405_ = v___x_418_;
goto v___jp_402_;
}
else
{
lean_object* v___x_419_; 
lean_dec(v___x_416_);
lean_inc(v_stopPos_410_);
lean_inc_ref(v_str_408_);
v___x_419_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_419_, 0, v_str_408_);
lean_ctor_set(v___x_419_, 1, v___y_415_);
lean_ctor_set(v___x_419_, 2, v_stopPos_410_);
v___y_403_ = v___y_412_;
v___y_404_ = v___y_414_;
v___y_405_ = v___x_419_;
goto v___jp_402_;
}
}
v___jp_420_:
{
lean_object* v_j_422_; uint8_t v___x_423_; 
v_j_422_ = lean_string_utf8_next(v_sep_389_, v_j_392_);
lean_dec(v_j_392_);
v___x_423_ = lean_string_utf8_at_end(v_sep_389_, v_j_422_);
if (v___x_423_ == 0)
{
v_i_391_ = v___y_421_;
v_j_392_ = v_j_422_;
goto _start;
}
else
{
lean_object* v___x_425_; lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_425_ = lean_unsigned_to_nat(0u);
v___x_426_ = lean_nat_sub(v___y_421_, v_j_422_);
lean_dec(v_j_422_);
v___x_427_ = lean_nat_dec_le(v___x_426_, v_b_390_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_428_ = lean_nat_add(v_startPos_409_, v_b_390_);
lean_dec(v_b_390_);
v___x_429_ = lean_nat_dec_le(v_stopPos_410_, v___x_428_);
if (v___x_429_ == 0)
{
v___y_412_ = v___y_421_;
v___y_413_ = v___x_426_;
v___y_414_ = v___x_425_;
v___y_415_ = v___x_428_;
goto v___jp_411_;
}
else
{
lean_dec(v___x_428_);
lean_inc(v_stopPos_410_);
v___y_412_ = v___y_421_;
v___y_413_ = v___x_426_;
v___y_414_ = v___x_425_;
v___y_415_ = v_stopPos_410_;
goto v___jp_411_;
}
}
else
{
lean_object* v___x_430_; 
lean_dec(v___x_426_);
lean_dec(v_b_390_);
v___x_430_ = ((lean_object*)(l_Substring_Raw_extract___closed__1));
v___y_403_ = v___y_421_;
v___y_404_ = v___x_425_;
v___y_405_ = v___x_430_;
goto v___jp_402_;
}
}
}
v___jp_431_:
{
lean_object* v___x_433_; uint8_t v___x_434_; 
v___x_433_ = lean_nat_add(v_startPos_409_, v_i_391_);
lean_dec(v_i_391_);
lean_dec(v_startPos_409_);
v___x_434_ = lean_nat_dec_le(v_stopPos_410_, v___x_433_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; 
lean_dec(v_stopPos_410_);
v___x_435_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_435_, 0, v_str_408_);
lean_ctor_set(v___x_435_, 1, v___y_432_);
lean_ctor_set(v___x_435_, 2, v___x_433_);
v___y_395_ = v___x_435_;
goto v___jp_394_;
}
else
{
lean_object* v___x_436_; 
lean_dec(v___x_433_);
v___x_436_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_436_, 0, v_str_408_);
lean_ctor_set(v___x_436_, 1, v___y_432_);
lean_ctor_set(v___x_436_, 2, v_stopPos_410_);
v___y_395_ = v___x_436_;
goto v___jp_394_;
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
lean_object* v_str_507_; lean_object* v_startInclusive_508_; lean_object* v_endExclusive_509_; lean_object* v___x_510_; uint8_t v___x_511_; 
v_str_507_ = lean_ctor_get(v___y_501_, 0);
v_startInclusive_508_ = lean_ctor_get(v___y_501_, 1);
v_endExclusive_509_ = lean_ctor_get(v___y_501_, 2);
v___x_510_ = lean_nat_sub(v_endExclusive_509_, v_startInclusive_508_);
v___x_511_ = lean_nat_dec_eq(v_it_503_, v___x_510_);
lean_dec(v___x_510_);
if (v___x_511_ == 0)
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
lean_object* v___y_539_; lean_object* v_str_543_; lean_object* v_startPos_544_; lean_object* v_stopPos_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_559_; 
v_str_543_ = lean_ctor_get(v_s_537_, 0);
v_startPos_544_ = lean_ctor_get(v_s_537_, 1);
v_stopPos_545_ = lean_ctor_get(v_s_537_, 2);
v_isSharedCheck_559_ = !lean_is_exclusive(v_s_537_);
if (v_isSharedCheck_559_ == 0)
{
v___x_547_ = v_s_537_;
v_isShared_548_ = v_isSharedCheck_559_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_stopPos_545_);
lean_inc(v_startPos_544_);
lean_inc(v_str_543_);
lean_dec(v_s_537_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_559_;
goto v_resetjp_546_;
}
v___jp_538_:
{
lean_object* v___f_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
lean_inc_ref(v___y_539_);
v___f_540_ = lean_alloc_closure((void*)(l_Substring_Raw_foldl___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_540_, 0, v___y_539_);
lean_closure_set(v___f_540_, 1, v_f_535_);
v___x_541_ = l_String_Slice_positions(v___y_539_);
lean_dec_ref(v___y_539_);
v___x_542_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_540_, v___x_541_, v_init_536_, lean_box(0));
return v___x_542_;
}
v_resetjp_546_:
{
lean_object* v___x_549_; uint8_t v___x_553_; 
v___x_549_ = l_String_instInhabitedSlice;
v___x_553_ = lean_string_is_valid_pos(v_str_543_, v_startPos_544_);
if (v___x_553_ == 0)
{
lean_del_object(v___x_547_);
lean_dec(v_stopPos_545_);
lean_dec(v_startPos_544_);
lean_dec_ref(v_str_543_);
goto v___jp_550_;
}
else
{
uint8_t v___x_554_; 
v___x_554_ = lean_string_is_valid_pos(v_str_543_, v_stopPos_545_);
if (v___x_554_ == 0)
{
lean_del_object(v___x_547_);
lean_dec(v_stopPos_545_);
lean_dec(v_startPos_544_);
lean_dec_ref(v_str_543_);
goto v___jp_550_;
}
else
{
uint8_t v___x_555_; 
v___x_555_ = lean_nat_dec_le(v_startPos_544_, v_stopPos_545_);
if (v___x_555_ == 0)
{
lean_del_object(v___x_547_);
lean_dec(v_stopPos_545_);
lean_dec(v_startPos_544_);
lean_dec_ref(v_str_543_);
goto v___jp_550_;
}
else
{
lean_object* v___x_557_; 
if (v_isShared_548_ == 0)
{
v___x_557_ = v___x_547_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_str_543_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_startPos_544_);
lean_ctor_set(v_reuseFailAlloc_558_, 2, v_stopPos_545_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
v___y_539_ = v___x_557_;
goto v___jp_538_;
}
}
}
}
v___jp_550_:
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_552_ = l_panic___redArg(v___x_549_, v___x_551_);
v___y_539_ = v___x_552_;
goto v___jp_538_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldl(lean_object* v_00_u03b1_560_, lean_object* v_f_561_, lean_object* v_init_562_, lean_object* v_s_563_){
_start:
{
lean_object* v___y_565_; lean_object* v_str_569_; lean_object* v_startPos_570_; lean_object* v_stopPos_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_585_; 
v_str_569_ = lean_ctor_get(v_s_563_, 0);
v_startPos_570_ = lean_ctor_get(v_s_563_, 1);
v_stopPos_571_ = lean_ctor_get(v_s_563_, 2);
v_isSharedCheck_585_ = !lean_is_exclusive(v_s_563_);
if (v_isSharedCheck_585_ == 0)
{
v___x_573_ = v_s_563_;
v_isShared_574_ = v_isSharedCheck_585_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_stopPos_571_);
lean_inc(v_startPos_570_);
lean_inc(v_str_569_);
lean_dec(v_s_563_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_585_;
goto v_resetjp_572_;
}
v___jp_564_:
{
lean_object* v___f_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
lean_inc_ref(v___y_565_);
v___f_566_ = lean_alloc_closure((void*)(l_Substring_Raw_foldl___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_566_, 0, v___y_565_);
lean_closure_set(v___f_566_, 1, v_f_561_);
v___x_567_ = l_String_Slice_positions(v___y_565_);
lean_dec_ref(v___y_565_);
v___x_568_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_566_, v___x_567_, v_init_562_, lean_box(0));
return v___x_568_;
}
v_resetjp_572_:
{
lean_object* v___x_575_; uint8_t v___x_579_; 
v___x_575_ = l_String_instInhabitedSlice;
v___x_579_ = lean_string_is_valid_pos(v_str_569_, v_startPos_570_);
if (v___x_579_ == 0)
{
lean_del_object(v___x_573_);
lean_dec(v_stopPos_571_);
lean_dec(v_startPos_570_);
lean_dec_ref(v_str_569_);
goto v___jp_576_;
}
else
{
uint8_t v___x_580_; 
v___x_580_ = lean_string_is_valid_pos(v_str_569_, v_stopPos_571_);
if (v___x_580_ == 0)
{
lean_del_object(v___x_573_);
lean_dec(v_stopPos_571_);
lean_dec(v_startPos_570_);
lean_dec_ref(v_str_569_);
goto v___jp_576_;
}
else
{
uint8_t v___x_581_; 
v___x_581_ = lean_nat_dec_le(v_startPos_570_, v_stopPos_571_);
if (v___x_581_ == 0)
{
lean_del_object(v___x_573_);
lean_dec(v_stopPos_571_);
lean_dec(v_startPos_570_);
lean_dec_ref(v_str_569_);
goto v___jp_576_;
}
else
{
lean_object* v___x_583_; 
if (v_isShared_574_ == 0)
{
v___x_583_ = v___x_573_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_str_569_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v_startPos_570_);
lean_ctor_set(v_reuseFailAlloc_584_, 2, v_stopPos_571_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
v___y_565_ = v___x_583_;
goto v___jp_564_;
}
}
}
}
v___jp_576_:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_578_ = l_panic___redArg(v___x_575_, v___x_577_);
v___y_565_ = v___x_578_;
goto v___jp_564_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr___redArg___lam__0(lean_object* v___y_586_, lean_object* v_f_587_, lean_object* v_it_588_, lean_object* v_acc_589_, lean_object* v_hP_590_, lean_object* v_recur_591_){
_start:
{
lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_592_ = lean_unsigned_to_nat(0u);
v___x_593_ = lean_nat_dec_eq(v_it_588_, v___x_592_);
if (v___x_593_ == 0)
{
lean_object* v_str_594_; lean_object* v_startInclusive_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v_prevPos_598_; lean_object* v___x_599_; uint32_t v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v_str_594_ = lean_ctor_get(v___y_586_, 0);
v_startInclusive_595_ = lean_ctor_get(v___y_586_, 1);
v___x_596_ = lean_unsigned_to_nat(1u);
v___x_597_ = lean_nat_sub(v_it_588_, v___x_596_);
v_prevPos_598_ = l_String_Slice_posLE(v___y_586_, v___x_597_);
v___x_599_ = lean_nat_add(v_startInclusive_595_, v_prevPos_598_);
v___x_600_ = lean_string_utf8_get_fast(v_str_594_, v___x_599_);
lean_dec(v___x_599_);
v___x_601_ = lean_box_uint32(v___x_600_);
v___x_602_ = lean_apply_2(v_f_587_, v___x_601_, v_acc_589_);
v___x_603_ = lean_apply_4(v_recur_591_, v_prevPos_598_, v___x_602_, lean_box(0), lean_box(0));
return v___x_603_;
}
else
{
lean_dec(v_recur_591_);
lean_dec(v_f_587_);
return v_acc_589_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr___redArg___lam__0___boxed(lean_object* v___y_604_, lean_object* v_f_605_, lean_object* v_it_606_, lean_object* v_acc_607_, lean_object* v_hP_608_, lean_object* v_recur_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Substring_Raw_foldr___redArg___lam__0(v___y_604_, v_f_605_, v_it_606_, v_acc_607_, v_hP_608_, v_recur_609_);
lean_dec(v_it_606_);
lean_dec_ref(v___y_604_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr___redArg(lean_object* v_f_611_, lean_object* v_init_612_, lean_object* v_s_613_){
_start:
{
lean_object* v___y_615_; lean_object* v_str_619_; lean_object* v_startPos_620_; lean_object* v_stopPos_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_635_; 
v_str_619_ = lean_ctor_get(v_s_613_, 0);
v_startPos_620_ = lean_ctor_get(v_s_613_, 1);
v_stopPos_621_ = lean_ctor_get(v_s_613_, 2);
v_isSharedCheck_635_ = !lean_is_exclusive(v_s_613_);
if (v_isSharedCheck_635_ == 0)
{
v___x_623_ = v_s_613_;
v_isShared_624_ = v_isSharedCheck_635_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_stopPos_621_);
lean_inc(v_startPos_620_);
lean_inc(v_str_619_);
lean_dec(v_s_613_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_635_;
goto v_resetjp_622_;
}
v___jp_614_:
{
lean_object* v___f_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
lean_inc_ref(v___y_615_);
v___f_616_ = lean_alloc_closure((void*)(l_Substring_Raw_foldr___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_616_, 0, v___y_615_);
lean_closure_set(v___f_616_, 1, v_f_611_);
v___x_617_ = l_String_Slice_revPositions(v___y_615_);
lean_dec_ref(v___y_615_);
v___x_618_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_616_, v___x_617_, v_init_612_, lean_box(0));
return v___x_618_;
}
v_resetjp_622_:
{
lean_object* v___x_625_; uint8_t v___x_629_; 
v___x_625_ = l_String_instInhabitedSlice;
v___x_629_ = lean_string_is_valid_pos(v_str_619_, v_startPos_620_);
if (v___x_629_ == 0)
{
lean_del_object(v___x_623_);
lean_dec(v_stopPos_621_);
lean_dec(v_startPos_620_);
lean_dec_ref(v_str_619_);
goto v___jp_626_;
}
else
{
uint8_t v___x_630_; 
v___x_630_ = lean_string_is_valid_pos(v_str_619_, v_stopPos_621_);
if (v___x_630_ == 0)
{
lean_del_object(v___x_623_);
lean_dec(v_stopPos_621_);
lean_dec(v_startPos_620_);
lean_dec_ref(v_str_619_);
goto v___jp_626_;
}
else
{
uint8_t v___x_631_; 
v___x_631_ = lean_nat_dec_le(v_startPos_620_, v_stopPos_621_);
if (v___x_631_ == 0)
{
lean_del_object(v___x_623_);
lean_dec(v_stopPos_621_);
lean_dec(v_startPos_620_);
lean_dec_ref(v_str_619_);
goto v___jp_626_;
}
else
{
lean_object* v___x_633_; 
if (v_isShared_624_ == 0)
{
v___x_633_ = v___x_623_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_str_619_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_startPos_620_);
lean_ctor_set(v_reuseFailAlloc_634_, 2, v_stopPos_621_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
v___y_615_ = v___x_633_;
goto v___jp_614_;
}
}
}
}
v___jp_626_:
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_628_ = l_panic___redArg(v___x_625_, v___x_627_);
v___y_615_ = v___x_628_;
goto v___jp_614_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr(lean_object* v_00_u03b1_636_, lean_object* v_f_637_, lean_object* v_init_638_, lean_object* v_s_639_){
_start:
{
lean_object* v___y_641_; lean_object* v_str_645_; lean_object* v_startPos_646_; lean_object* v_stopPos_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_661_; 
v_str_645_ = lean_ctor_get(v_s_639_, 0);
v_startPos_646_ = lean_ctor_get(v_s_639_, 1);
v_stopPos_647_ = lean_ctor_get(v_s_639_, 2);
v_isSharedCheck_661_ = !lean_is_exclusive(v_s_639_);
if (v_isSharedCheck_661_ == 0)
{
v___x_649_ = v_s_639_;
v_isShared_650_ = v_isSharedCheck_661_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_stopPos_647_);
lean_inc(v_startPos_646_);
lean_inc(v_str_645_);
lean_dec(v_s_639_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_661_;
goto v_resetjp_648_;
}
v___jp_640_:
{
lean_object* v___f_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
lean_inc_ref(v___y_641_);
v___f_642_ = lean_alloc_closure((void*)(l_Substring_Raw_foldr___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_642_, 0, v___y_641_);
lean_closure_set(v___f_642_, 1, v_f_637_);
v___x_643_ = l_String_Slice_revPositions(v___y_641_);
lean_dec_ref(v___y_641_);
v___x_644_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_642_, v___x_643_, v_init_638_, lean_box(0));
return v___x_644_;
}
v_resetjp_648_:
{
lean_object* v___x_651_; uint8_t v___x_655_; 
v___x_651_ = l_String_instInhabitedSlice;
v___x_655_ = lean_string_is_valid_pos(v_str_645_, v_startPos_646_);
if (v___x_655_ == 0)
{
lean_del_object(v___x_649_);
lean_dec(v_stopPos_647_);
lean_dec(v_startPos_646_);
lean_dec_ref(v_str_645_);
goto v___jp_652_;
}
else
{
uint8_t v___x_656_; 
v___x_656_ = lean_string_is_valid_pos(v_str_645_, v_stopPos_647_);
if (v___x_656_ == 0)
{
lean_del_object(v___x_649_);
lean_dec(v_stopPos_647_);
lean_dec(v_startPos_646_);
lean_dec_ref(v_str_645_);
goto v___jp_652_;
}
else
{
uint8_t v___x_657_; 
v___x_657_ = lean_nat_dec_le(v_startPos_646_, v_stopPos_647_);
if (v___x_657_ == 0)
{
lean_del_object(v___x_649_);
lean_dec(v_stopPos_647_);
lean_dec(v_startPos_646_);
lean_dec_ref(v_str_645_);
goto v___jp_652_;
}
else
{
lean_object* v___x_659_; 
if (v_isShared_650_ == 0)
{
v___x_659_ = v___x_649_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_str_645_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v_startPos_646_);
lean_ctor_set(v_reuseFailAlloc_660_, 2, v_stopPos_647_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
v___y_641_ = v___x_659_;
goto v___jp_640_;
}
}
}
}
v___jp_652_:
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_654_ = l_panic___redArg(v___x_651_, v___x_653_);
v___y_641_ = v___x_654_;
goto v___jp_640_;
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
lean_object* v___x_673_; lean_object* v_str_674_; lean_object* v_startPos_675_; lean_object* v_stopPos_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_694_; 
lean_inc_ref(v_p_672_);
v___x_673_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v_p_672_);
v_str_674_ = lean_ctor_get(v_s_671_, 0);
v_startPos_675_ = lean_ctor_get(v_s_671_, 1);
v_stopPos_676_ = lean_ctor_get(v_s_671_, 2);
v_isSharedCheck_694_ = !lean_is_exclusive(v_s_671_);
if (v_isSharedCheck_694_ == 0)
{
v___x_678_ = v_s_671_;
v_isShared_679_ = v_isSharedCheck_694_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_stopPos_676_);
lean_inc(v_startPos_675_);
lean_inc(v_str_674_);
lean_dec(v_s_671_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_694_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_680_; lean_object* v___f_681_; lean_object* v___x_682_; uint8_t v___x_687_; 
v___x_680_ = l_String_instInhabitedSlice;
v___f_681_ = lean_alloc_closure((void*)(l_Substring_Raw_any___lam__0), 8, 1);
lean_closure_set(v___f_681_, 0, v___x_673_);
v___x_682_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_682_, 0, lean_box(0));
lean_closure_set(v___x_682_, 1, v_p_672_);
v___x_687_ = lean_string_is_valid_pos(v_str_674_, v_startPos_675_);
if (v___x_687_ == 0)
{
lean_del_object(v___x_678_);
lean_dec(v_stopPos_676_);
lean_dec(v_startPos_675_);
lean_dec_ref(v_str_674_);
goto v___jp_683_;
}
else
{
uint8_t v___x_688_; 
v___x_688_ = lean_string_is_valid_pos(v_str_674_, v_stopPos_676_);
if (v___x_688_ == 0)
{
lean_del_object(v___x_678_);
lean_dec(v_stopPos_676_);
lean_dec(v_startPos_675_);
lean_dec_ref(v_str_674_);
goto v___jp_683_;
}
else
{
uint8_t v___x_689_; 
v___x_689_ = lean_nat_dec_le(v_startPos_675_, v_stopPos_676_);
if (v___x_689_ == 0)
{
lean_del_object(v___x_678_);
lean_dec(v_stopPos_676_);
lean_dec(v_startPos_675_);
lean_dec_ref(v_str_674_);
goto v___jp_683_;
}
else
{
lean_object* v___x_691_; 
if (v_isShared_679_ == 0)
{
v___x_691_ = v___x_678_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_str_674_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_startPos_675_);
lean_ctor_set(v_reuseFailAlloc_693_, 2, v_stopPos_676_);
v___x_691_ = v_reuseFailAlloc_693_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
uint8_t v___x_692_; 
v___x_692_ = l_String_Slice_contains___redArg(v___f_681_, v___x_691_, v___x_682_);
return v___x_692_;
}
}
}
}
v___jp_683_:
{
lean_object* v___x_684_; lean_object* v___x_685_; uint8_t v___x_686_; 
v___x_684_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_685_ = l_panic___redArg(v___x_680_, v___x_684_);
v___x_686_ = l_String_Slice_contains___redArg(v___f_681_, v___x_685_, v___x_682_);
return v___x_686_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_any___boxed(lean_object* v_s_695_, lean_object* v_p_696_){
_start:
{
uint8_t v_res_697_; lean_object* v_r_698_; 
v_res_697_ = l_Substring_Raw_any(v_s_695_, v_p_696_);
v_r_698_ = lean_box(v_res_697_);
return v_r_698_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_all(lean_object* v_s_699_, lean_object* v_p_700_){
_start:
{
lean_object* v___y_702_; lean_object* v_startInclusive_703_; lean_object* v_endExclusive_704_; lean_object* v_str_711_; lean_object* v_startPos_712_; lean_object* v_stopPos_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_729_; 
v_str_711_ = lean_ctor_get(v_s_699_, 0);
v_startPos_712_ = lean_ctor_get(v_s_699_, 1);
v_stopPos_713_ = lean_ctor_get(v_s_699_, 2);
v_isSharedCheck_729_ = !lean_is_exclusive(v_s_699_);
if (v_isSharedCheck_729_ == 0)
{
v___x_715_ = v_s_699_;
v_isShared_716_ = v_isSharedCheck_729_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_stopPos_713_);
lean_inc(v_startPos_712_);
lean_inc(v_str_711_);
lean_dec(v_s_699_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_729_;
goto v_resetjp_714_;
}
v___jp_701_:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; uint8_t v___x_710_; 
v___x_705_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v_p_700_);
v___x_706_ = lean_unsigned_to_nat(0u);
v___x_707_ = l_String_Slice_Pos_skipWhile___redArg(v___y_702_, v___x_706_, v___x_705_);
lean_dec_ref(v___y_702_);
v___x_708_ = lean_nat_add(v_startInclusive_703_, v___x_707_);
lean_dec(v___x_707_);
lean_dec(v_startInclusive_703_);
v___x_709_ = lean_nat_sub(v_endExclusive_704_, v___x_708_);
lean_dec(v___x_708_);
lean_dec(v_endExclusive_704_);
v___x_710_ = lean_nat_dec_eq(v___x_709_, v___x_706_);
lean_dec(v___x_709_);
return v___x_710_;
}
v_resetjp_714_:
{
lean_object* v___x_717_; uint8_t v___x_723_; 
v___x_717_ = l_String_instInhabitedSlice;
v___x_723_ = lean_string_is_valid_pos(v_str_711_, v_startPos_712_);
if (v___x_723_ == 0)
{
lean_del_object(v___x_715_);
lean_dec(v_stopPos_713_);
lean_dec(v_startPos_712_);
lean_dec_ref(v_str_711_);
goto v___jp_718_;
}
else
{
uint8_t v___x_724_; 
v___x_724_ = lean_string_is_valid_pos(v_str_711_, v_stopPos_713_);
if (v___x_724_ == 0)
{
lean_del_object(v___x_715_);
lean_dec(v_stopPos_713_);
lean_dec(v_startPos_712_);
lean_dec_ref(v_str_711_);
goto v___jp_718_;
}
else
{
uint8_t v___x_725_; 
v___x_725_ = lean_nat_dec_le(v_startPos_712_, v_stopPos_713_);
if (v___x_725_ == 0)
{
lean_del_object(v___x_715_);
lean_dec(v_stopPos_713_);
lean_dec(v_startPos_712_);
lean_dec_ref(v_str_711_);
goto v___jp_718_;
}
else
{
lean_object* v___x_727_; 
lean_inc(v_stopPos_713_);
lean_inc(v_startPos_712_);
if (v_isShared_716_ == 0)
{
v___x_727_ = v___x_715_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_str_711_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_startPos_712_);
lean_ctor_set(v_reuseFailAlloc_728_, 2, v_stopPos_713_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
v___y_702_ = v___x_727_;
v_startInclusive_703_ = v_startPos_712_;
v_endExclusive_704_ = v_stopPos_713_;
goto v___jp_701_;
}
}
}
}
v___jp_718_:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v_startInclusive_721_; lean_object* v_endExclusive_722_; 
v___x_719_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_720_ = l_panic___redArg(v___x_717_, v___x_719_);
v_startInclusive_721_ = lean_ctor_get(v___x_720_, 1);
lean_inc(v_startInclusive_721_);
v_endExclusive_722_ = lean_ctor_get(v___x_720_, 2);
lean_inc(v_endExclusive_722_);
v___y_702_ = v___x_720_;
v_startInclusive_703_ = v_startInclusive_721_;
v_endExclusive_704_ = v_endExclusive_722_;
goto v___jp_701_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_all___boxed(lean_object* v_s_730_, lean_object* v_p_731_){
_start:
{
uint8_t v_res_732_; lean_object* v_r_733_; 
v_res_732_ = l_Substring_Raw_all(v_s_730_, v_p_731_);
v_r_733_ = lean_box(v_res_732_);
return v_r_733_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(lean_object* v_msg_734_){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = l_String_instInhabitedSlice;
v___x_736_ = lean_panic_fn(v___x_735_, v_msg_734_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0(lean_object* v_p_737_, lean_object* v_s_738_, lean_object* v_pos_739_){
_start:
{
lean_object* v_str_740_; lean_object* v_startInclusive_741_; lean_object* v_endExclusive_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; uint8_t v___x_746_; 
v_str_740_ = lean_ctor_get(v_s_738_, 0);
v_startInclusive_741_ = lean_ctor_get(v_s_738_, 1);
v_endExclusive_742_ = lean_ctor_get(v_s_738_, 2);
v___x_743_ = lean_nat_add(v_startInclusive_741_, v_pos_739_);
v___x_744_ = lean_unsigned_to_nat(0u);
v___x_745_ = lean_nat_sub(v_endExclusive_742_, v___x_743_);
v___x_746_ = lean_nat_dec_eq(v___x_744_, v___x_745_);
lean_dec(v___x_745_);
if (v___x_746_ == 0)
{
uint32_t v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_747_ = lean_string_utf8_get_fast(v_str_740_, v___x_743_);
v___x_748_ = lean_box_uint32(v___x_747_);
lean_inc_ref(v_p_737_);
v___x_749_ = lean_apply_1(v_p_737_, v___x_748_);
v___x_750_ = lean_unbox(v___x_749_);
if (v___x_750_ == 0)
{
lean_dec(v___x_743_);
lean_dec_ref(v_p_737_);
return v_pos_739_;
}
else
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; uint8_t v___x_754_; 
v___x_751_ = lean_string_utf8_next_fast(v_str_740_, v___x_743_);
v___x_752_ = lean_nat_sub(v___x_751_, v___x_743_);
lean_dec(v___x_743_);
v___x_753_ = lean_nat_add(v_pos_739_, v___x_752_);
lean_dec(v___x_752_);
v___x_754_ = lean_nat_dec_lt(v_pos_739_, v___x_753_);
if (v___x_754_ == 0)
{
lean_dec(v___x_753_);
lean_dec_ref(v_p_737_);
return v_pos_739_;
}
else
{
lean_dec(v_pos_739_);
v_pos_739_ = v___x_753_;
goto _start;
}
}
}
else
{
lean_dec(v___x_743_);
lean_dec_ref(v_p_737_);
return v_pos_739_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0___boxed(lean_object* v_p_756_, lean_object* v_s_757_, lean_object* v_pos_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0(v_p_756_, v_s_757_, v_pos_758_);
lean_dec_ref(v_s_757_);
return v_res_759_;
}
}
LEAN_EXPORT uint8_t lean_substring_all(lean_object* v_s_760_, lean_object* v_p_761_){
_start:
{
lean_object* v___y_763_; lean_object* v_startInclusive_764_; lean_object* v_endExclusive_765_; lean_object* v_str_776_; lean_object* v_startPos_777_; lean_object* v_stopPos_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_788_; 
v_str_776_ = lean_ctor_get(v_s_760_, 0);
v_startPos_777_ = lean_ctor_get(v_s_760_, 1);
v_stopPos_778_ = lean_ctor_get(v_s_760_, 2);
v_isSharedCheck_788_ = !lean_is_exclusive(v_s_760_);
if (v_isSharedCheck_788_ == 0)
{
v___x_780_ = v_s_760_;
v_isShared_781_ = v_isSharedCheck_788_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_stopPos_778_);
lean_inc(v_startPos_777_);
lean_inc(v_str_776_);
lean_dec(v_s_760_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_788_;
goto v_resetjp_779_;
}
v___jp_762_:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_766_ = lean_unsigned_to_nat(0u);
v___x_767_ = l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0(v_p_761_, v___y_763_, v___x_766_);
lean_dec_ref(v___y_763_);
v___x_768_ = lean_nat_add(v_startInclusive_764_, v___x_767_);
lean_dec(v___x_767_);
lean_dec(v_startInclusive_764_);
v___x_769_ = lean_nat_sub(v_endExclusive_765_, v___x_768_);
lean_dec(v___x_768_);
lean_dec(v_endExclusive_765_);
v___x_770_ = lean_nat_dec_eq(v___x_769_, v___x_766_);
lean_dec(v___x_769_);
return v___x_770_;
}
v___jp_771_:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v_startInclusive_774_; lean_object* v_endExclusive_775_; 
v___x_772_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_773_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_772_);
v_startInclusive_774_ = lean_ctor_get(v___x_773_, 1);
lean_inc(v_startInclusive_774_);
v_endExclusive_775_ = lean_ctor_get(v___x_773_, 2);
lean_inc(v_endExclusive_775_);
v___y_763_ = v___x_773_;
v_startInclusive_764_ = v_startInclusive_774_;
v_endExclusive_765_ = v_endExclusive_775_;
goto v___jp_762_;
}
v_resetjp_779_:
{
uint8_t v___x_782_; 
v___x_782_ = lean_string_is_valid_pos(v_str_776_, v_startPos_777_);
if (v___x_782_ == 0)
{
lean_del_object(v___x_780_);
lean_dec(v_stopPos_778_);
lean_dec(v_startPos_777_);
lean_dec_ref(v_str_776_);
goto v___jp_771_;
}
else
{
uint8_t v___x_783_; 
v___x_783_ = lean_string_is_valid_pos(v_str_776_, v_stopPos_778_);
if (v___x_783_ == 0)
{
lean_del_object(v___x_780_);
lean_dec(v_stopPos_778_);
lean_dec(v_startPos_777_);
lean_dec_ref(v_str_776_);
goto v___jp_771_;
}
else
{
uint8_t v___x_784_; 
v___x_784_ = lean_nat_dec_le(v_startPos_777_, v_stopPos_778_);
if (v___x_784_ == 0)
{
lean_del_object(v___x_780_);
lean_dec(v_stopPos_778_);
lean_dec(v_startPos_777_);
lean_dec_ref(v_str_776_);
goto v___jp_771_;
}
else
{
lean_object* v___x_786_; 
lean_inc(v_stopPos_778_);
lean_inc(v_startPos_777_);
if (v_isShared_781_ == 0)
{
v___x_786_ = v___x_780_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_str_776_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_startPos_777_);
lean_ctor_set(v_reuseFailAlloc_787_, 2, v_stopPos_778_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
v___y_763_ = v___x_786_;
v_startInclusive_764_ = v_startPos_777_;
v_endExclusive_765_ = v_stopPos_778_;
goto v___jp_762_;
}
}
}
}
}
}
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
LEAN_EXPORT uint8_t l_Substring_Raw_contains___lam__0(uint32_t v_c_793_, uint32_t v_a_794_){
_start:
{
uint8_t v___x_795_; 
v___x_795_ = lean_uint32_dec_eq(v_a_794_, v_c_793_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_contains___lam__0___boxed(lean_object* v_c_796_, lean_object* v_a_797_){
_start:
{
uint32_t v_c_boxed_798_; uint32_t v_a_boxed_799_; uint8_t v_res_800_; lean_object* v_r_801_; 
v_c_boxed_798_ = lean_unbox_uint32(v_c_796_);
lean_dec(v_c_796_);
v_a_boxed_799_ = lean_unbox_uint32(v_a_797_);
lean_dec(v_a_797_);
v_res_800_ = l_Substring_Raw_contains___lam__0(v_c_boxed_798_, v_a_boxed_799_);
v_r_801_ = lean_box(v_res_800_);
return v_r_801_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_contains(lean_object* v_s_802_, uint32_t v_c_803_){
_start:
{
lean_object* v___x_804_; lean_object* v___f_805_; lean_object* v___x_806_; lean_object* v_str_807_; lean_object* v_startPos_808_; lean_object* v_stopPos_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_827_; 
v___x_804_ = lean_box_uint32(v_c_803_);
v___f_805_ = lean_alloc_closure((void*)(l_Substring_Raw_contains___lam__0___boxed), 2, 1);
lean_closure_set(v___f_805_, 0, v___x_804_);
lean_inc_ref(v___f_805_);
v___x_806_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___f_805_);
v_str_807_ = lean_ctor_get(v_s_802_, 0);
v_startPos_808_ = lean_ctor_get(v_s_802_, 1);
v_stopPos_809_ = lean_ctor_get(v_s_802_, 2);
v_isSharedCheck_827_ = !lean_is_exclusive(v_s_802_);
if (v_isSharedCheck_827_ == 0)
{
v___x_811_ = v_s_802_;
v_isShared_812_ = v_isSharedCheck_827_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_stopPos_809_);
lean_inc(v_startPos_808_);
lean_inc(v_str_807_);
lean_dec(v_s_802_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_827_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_813_; lean_object* v___f_814_; lean_object* v___x_815_; uint8_t v___x_820_; 
v___x_813_ = l_String_instInhabitedSlice;
v___f_814_ = lean_alloc_closure((void*)(l_Substring_Raw_any___lam__0), 8, 1);
lean_closure_set(v___f_814_, 0, v___x_806_);
v___x_815_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_815_, 0, lean_box(0));
lean_closure_set(v___x_815_, 1, v___f_805_);
v___x_820_ = lean_string_is_valid_pos(v_str_807_, v_startPos_808_);
if (v___x_820_ == 0)
{
lean_del_object(v___x_811_);
lean_dec(v_stopPos_809_);
lean_dec(v_startPos_808_);
lean_dec_ref(v_str_807_);
goto v___jp_816_;
}
else
{
uint8_t v___x_821_; 
v___x_821_ = lean_string_is_valid_pos(v_str_807_, v_stopPos_809_);
if (v___x_821_ == 0)
{
lean_del_object(v___x_811_);
lean_dec(v_stopPos_809_);
lean_dec(v_startPos_808_);
lean_dec_ref(v_str_807_);
goto v___jp_816_;
}
else
{
uint8_t v___x_822_; 
v___x_822_ = lean_nat_dec_le(v_startPos_808_, v_stopPos_809_);
if (v___x_822_ == 0)
{
lean_del_object(v___x_811_);
lean_dec(v_stopPos_809_);
lean_dec(v_startPos_808_);
lean_dec_ref(v_str_807_);
goto v___jp_816_;
}
else
{
lean_object* v___x_824_; 
if (v_isShared_812_ == 0)
{
v___x_824_ = v___x_811_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_str_807_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v_startPos_808_);
lean_ctor_set(v_reuseFailAlloc_826_, 2, v_stopPos_809_);
v___x_824_ = v_reuseFailAlloc_826_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
uint8_t v___x_825_; 
v___x_825_ = l_String_Slice_contains___redArg(v___f_814_, v___x_824_, v___x_815_);
return v___x_825_;
}
}
}
}
v___jp_816_:
{
lean_object* v___x_817_; lean_object* v___x_818_; uint8_t v___x_819_; 
v___x_817_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_818_ = l_panic___redArg(v___x_813_, v___x_817_);
v___x_819_ = l_String_Slice_contains___redArg(v___f_814_, v___x_818_, v___x_815_);
return v___x_819_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_contains___boxed(lean_object* v_s_828_, lean_object* v_c_829_){
_start:
{
uint32_t v_c_boxed_830_; uint8_t v_res_831_; lean_object* v_r_832_; 
v_c_boxed_830_ = lean_unbox_uint32(v_c_829_);
lean_dec(v_c_829_);
v_res_831_ = l_Substring_Raw_contains(v_s_828_, v_c_boxed_830_);
v_r_832_ = lean_box(v_res_831_);
return v_r_832_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux(lean_object* v_s_833_, lean_object* v_stopPos_834_, lean_object* v_p_835_, lean_object* v_i_836_){
_start:
{
uint8_t v___x_837_; 
v___x_837_ = lean_nat_dec_lt(v_i_836_, v_stopPos_834_);
if (v___x_837_ == 0)
{
lean_dec_ref(v_p_835_);
return v_i_836_;
}
else
{
uint32_t v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; uint8_t v___x_841_; 
v___x_838_ = lean_string_utf8_get(v_s_833_, v_i_836_);
v___x_839_ = lean_box_uint32(v___x_838_);
lean_inc_ref(v_p_835_);
v___x_840_ = lean_apply_1(v_p_835_, v___x_839_);
v___x_841_ = lean_unbox(v___x_840_);
if (v___x_841_ == 0)
{
lean_dec_ref(v_p_835_);
return v_i_836_;
}
else
{
lean_object* v___x_842_; 
v___x_842_ = lean_string_utf8_next(v_s_833_, v_i_836_);
lean_dec(v_i_836_);
v_i_836_ = v___x_842_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___boxed(lean_object* v_s_844_, lean_object* v_stopPos_845_, lean_object* v_p_846_, lean_object* v_i_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Substring_Raw_takeWhileAux(v_s_844_, v_stopPos_845_, v_p_846_, v_i_847_);
lean_dec(v_stopPos_845_);
lean_dec_ref(v_s_844_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhile(lean_object* v_x_849_, lean_object* v_x_850_){
_start:
{
lean_object* v_str_851_; lean_object* v_startPos_852_; lean_object* v_stopPos_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_861_; 
v_str_851_ = lean_ctor_get(v_x_849_, 0);
v_startPos_852_ = lean_ctor_get(v_x_849_, 1);
v_stopPos_853_ = lean_ctor_get(v_x_849_, 2);
v_isSharedCheck_861_ = !lean_is_exclusive(v_x_849_);
if (v_isSharedCheck_861_ == 0)
{
v___x_855_ = v_x_849_;
v_isShared_856_ = v_isSharedCheck_861_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_stopPos_853_);
lean_inc(v_startPos_852_);
lean_inc(v_str_851_);
lean_dec(v_x_849_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_861_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v_e_857_; lean_object* v___x_859_; 
lean_inc(v_startPos_852_);
v_e_857_ = l_Substring_Raw_takeWhileAux(v_str_851_, v_stopPos_853_, v_x_850_, v_startPos_852_);
lean_dec(v_stopPos_853_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 2, v_e_857_);
v___x_859_ = v___x_855_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_str_851_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v_startPos_852_);
lean_ctor_set(v_reuseFailAlloc_860_, 2, v_e_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(lean_object* v_a_862_, lean_object* v_s_863_, lean_object* v_stopPos_864_, lean_object* v_i_865_){
_start:
{
uint8_t v___x_866_; 
v___x_866_ = lean_nat_dec_lt(v_i_865_, v_stopPos_864_);
if (v___x_866_ == 0)
{
lean_dec_ref(v_a_862_);
return v_i_865_;
}
else
{
uint32_t v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; uint8_t v___x_870_; 
v___x_867_ = lean_string_utf8_get(v_s_863_, v_i_865_);
v___x_868_ = lean_box_uint32(v___x_867_);
lean_inc_ref(v_a_862_);
v___x_869_ = lean_apply_1(v_a_862_, v___x_868_);
v___x_870_ = lean_unbox(v___x_869_);
if (v___x_870_ == 0)
{
lean_dec_ref(v_a_862_);
return v_i_865_;
}
else
{
lean_object* v___x_871_; 
v___x_871_ = lean_string_utf8_next(v_s_863_, v_i_865_);
lean_dec(v_i_865_);
v_i_865_ = v___x_871_;
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
uint8_t v___x_908_; 
v___x_908_ = lean_nat_dec_lt(v_begPos_905_, v_i_907_);
if (v___x_908_ == 0)
{
lean_dec_ref(v_p_906_);
return v_i_907_;
}
else
{
lean_object* v_i_x27_909_; uint32_t v_c_910_; lean_object* v___x_911_; lean_object* v___x_912_; uint8_t v___x_913_; 
v_i_x27_909_ = lean_string_utf8_prev(v_s_904_, v_i_907_);
v_c_910_ = lean_string_utf8_get(v_s_904_, v_i_x27_909_);
v___x_911_ = lean_box_uint32(v_c_910_);
lean_inc_ref(v_p_906_);
v___x_912_ = lean_apply_1(v_p_906_, v___x_911_);
v___x_913_ = lean_unbox(v___x_912_);
if (v___x_913_ == 0)
{
lean_dec(v_i_x27_909_);
lean_dec_ref(v_p_906_);
return v_i_907_;
}
else
{
lean_dec(v_i_907_);
v_i_907_ = v_i_x27_909_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux___boxed(lean_object* v_s_915_, lean_object* v_begPos_916_, lean_object* v_p_917_, lean_object* v_i_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Substring_Raw_takeRightWhileAux(v_s_915_, v_begPos_916_, v_p_917_, v_i_918_);
lean_dec(v_begPos_916_);
lean_dec_ref(v_s_915_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhile(lean_object* v_x_920_, lean_object* v_x_921_){
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
lean_object* v_b_928_; lean_object* v___x_930_; 
lean_inc(v_stopPos_924_);
v_b_928_ = l_Substring_Raw_takeRightWhileAux(v_str_922_, v_startPos_923_, v_x_921_, v_stopPos_924_);
lean_dec(v_startPos_923_);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 1, v_b_928_);
v___x_930_ = v___x_926_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_str_922_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v_b_928_);
lean_ctor_set(v_reuseFailAlloc_931_, 2, v_stopPos_924_);
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
LEAN_EXPORT lean_object* l_Substring_Raw_dropRightWhile(lean_object* v_x_933_, lean_object* v_x_934_){
_start:
{
lean_object* v_str_935_; lean_object* v_startPos_936_; lean_object* v_stopPos_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_945_; 
v_str_935_ = lean_ctor_get(v_x_933_, 0);
v_startPos_936_ = lean_ctor_get(v_x_933_, 1);
v_stopPos_937_ = lean_ctor_get(v_x_933_, 2);
v_isSharedCheck_945_ = !lean_is_exclusive(v_x_933_);
if (v_isSharedCheck_945_ == 0)
{
v___x_939_ = v_x_933_;
v_isShared_940_ = v_isSharedCheck_945_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_stopPos_937_);
lean_inc(v_startPos_936_);
lean_inc(v_str_935_);
lean_dec(v_x_933_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_945_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v_e_941_; lean_object* v___x_943_; 
v_e_941_ = l_Substring_Raw_takeRightWhileAux(v_str_935_, v_startPos_936_, v_x_934_, v_stopPos_937_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 2, v_e_941_);
v___x_943_ = v___x_939_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_str_935_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v_startPos_936_);
lean_ctor_set(v_reuseFailAlloc_944_, 2, v_e_941_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_trimLeft(lean_object* v_s_947_){
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
lean_object* v___x_954_; lean_object* v_b_955_; lean_object* v___x_957_; 
v___x_954_ = ((lean_object*)(l_Substring_Raw_trimLeft___closed__0));
v_b_955_ = l_Substring_Raw_takeWhileAux(v_str_948_, v_stopPos_950_, v___x_954_, v_startPos_949_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 1, v_b_955_);
v___x_957_ = v___x_952_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_str_948_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_b_955_);
lean_ctor_set(v_reuseFailAlloc_958_, 2, v_stopPos_950_);
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
LEAN_EXPORT lean_object* l_Substring_Raw_trimRight(lean_object* v_s_960_){
_start:
{
lean_object* v_str_961_; lean_object* v_startPos_962_; lean_object* v_stopPos_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_972_; 
v_str_961_ = lean_ctor_get(v_s_960_, 0);
v_startPos_962_ = lean_ctor_get(v_s_960_, 1);
v_stopPos_963_ = lean_ctor_get(v_s_960_, 2);
v_isSharedCheck_972_ = !lean_is_exclusive(v_s_960_);
if (v_isSharedCheck_972_ == 0)
{
v___x_965_ = v_s_960_;
v_isShared_966_ = v_isSharedCheck_972_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_stopPos_963_);
lean_inc(v_startPos_962_);
lean_inc(v_str_961_);
lean_dec(v_s_960_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_972_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_967_; lean_object* v_e_968_; lean_object* v___x_970_; 
v___x_967_ = ((lean_object*)(l_Substring_Raw_trimLeft___closed__0));
v_e_968_ = l_Substring_Raw_takeRightWhileAux(v_str_961_, v_startPos_962_, v___x_967_, v_stopPos_963_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 2, v_e_968_);
v___x_970_ = v___x_965_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_str_961_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v_startPos_962_);
lean_ctor_set(v_reuseFailAlloc_971_, 2, v_e_968_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_trim(lean_object* v_x_973_){
_start:
{
lean_object* v_str_974_; lean_object* v_startPos_975_; lean_object* v_stopPos_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_986_; 
v_str_974_ = lean_ctor_get(v_x_973_, 0);
v_startPos_975_ = lean_ctor_get(v_x_973_, 1);
v_stopPos_976_ = lean_ctor_get(v_x_973_, 2);
v_isSharedCheck_986_ = !lean_is_exclusive(v_x_973_);
if (v_isSharedCheck_986_ == 0)
{
v___x_978_ = v_x_973_;
v_isShared_979_ = v_isSharedCheck_986_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_stopPos_976_);
lean_inc(v_startPos_975_);
lean_inc(v_str_974_);
lean_dec(v_x_973_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_986_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_980_; lean_object* v_b_981_; lean_object* v_e_982_; lean_object* v___x_984_; 
v___x_980_ = ((lean_object*)(l_Substring_Raw_trimLeft___closed__0));
v_b_981_ = l_Substring_Raw_takeWhileAux(v_str_974_, v_stopPos_976_, v___x_980_, v_startPos_975_);
v_e_982_ = l_Substring_Raw_takeRightWhileAux(v_str_974_, v_b_981_, v___x_980_, v_stopPos_976_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 2, v_e_982_);
lean_ctor_set(v___x_978_, 1, v_b_981_);
v___x_984_ = v___x_978_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_str_974_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_b_981_);
lean_ctor_set(v_reuseFailAlloc_985_, 2, v_e_982_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___lam__0(lean_object* v___y_987_, uint8_t v___x_988_, uint8_t v___x_989_, lean_object* v_it_990_, lean_object* v_acc_991_, lean_object* v_hP_992_, lean_object* v_recur_993_){
_start:
{
lean_object* v_str_994_; lean_object* v_startInclusive_995_; lean_object* v_endExclusive_996_; lean_object* v___x_997_; uint8_t v___x_998_; 
v_str_994_ = lean_ctor_get(v___y_987_, 0);
v_startInclusive_995_ = lean_ctor_get(v___y_987_, 1);
v_endExclusive_996_ = lean_ctor_get(v___y_987_, 2);
v___x_997_ = lean_nat_sub(v_endExclusive_996_, v_startInclusive_995_);
v___x_998_ = lean_nat_dec_eq(v_it_990_, v___x_997_);
lean_dec(v___x_997_);
if (v___x_998_ == 0)
{
lean_object* v_snd_999_; lean_object* v_snd_1000_; lean_object* v_fst_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1062_; 
v_snd_999_ = lean_ctor_get(v_acc_991_, 1);
lean_inc(v_snd_999_);
v_snd_1000_ = lean_ctor_get(v_snd_999_, 1);
lean_inc(v_snd_1000_);
v_fst_1001_ = lean_ctor_get(v_acc_991_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v_acc_991_);
if (v_isSharedCheck_1062_ == 0)
{
lean_object* v_unused_1063_; 
v_unused_1063_ = lean_ctor_get(v_acc_991_, 1);
lean_dec(v_unused_1063_);
v___x_1003_ = v_acc_991_;
v_isShared_1004_ = v_isSharedCheck_1062_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_fst_1001_);
lean_dec(v_acc_991_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1062_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v_fst_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1060_; 
v_fst_1005_ = lean_ctor_get(v_snd_999_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v_snd_999_);
if (v_isSharedCheck_1060_ == 0)
{
lean_object* v_unused_1061_; 
v_unused_1061_ = lean_ctor_get(v_snd_999_, 1);
lean_dec(v_unused_1061_);
v___x_1007_ = v_snd_999_;
v_isShared_1008_ = v_isSharedCheck_1060_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_fst_1005_);
lean_dec(v_snd_999_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1060_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v_snd_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1058_; 
v_snd_1009_ = lean_ctor_get(v_snd_1000_, 1);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_snd_1000_);
if (v_isSharedCheck_1058_ == 0)
{
lean_object* v_unused_1059_; 
v_unused_1059_ = lean_ctor_get(v_snd_1000_, 0);
lean_dec(v_unused_1059_);
v___x_1011_ = v_snd_1000_;
v_isShared_1012_ = v_isSharedCheck_1058_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_snd_1009_);
lean_dec(v_snd_1000_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1058_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; uint32_t v___x_1016_; uint8_t v___y_1018_; uint8_t v___y_1019_; uint8_t v___y_1037_; uint8_t v___y_1038_; uint8_t v___y_1043_; uint8_t v___y_1044_; uint8_t v___y_1049_; uint32_t v___x_1054_; uint8_t v___x_1055_; 
v___x_1013_ = lean_nat_add(v_startInclusive_995_, v_it_990_);
v___x_1014_ = lean_string_utf8_next_fast(v_str_994_, v___x_1013_);
v___x_1015_ = lean_nat_sub(v___x_1014_, v_startInclusive_995_);
v___x_1016_ = lean_string_utf8_get_fast(v_str_994_, v___x_1013_);
lean_dec(v___x_1013_);
v___x_1054_ = 48;
v___x_1055_ = lean_uint32_dec_le(v___x_1054_, v___x_1016_);
if (v___x_1055_ == 0)
{
v___y_1049_ = v___x_1055_;
goto v___jp_1048_;
}
else
{
uint32_t v___x_1056_; uint8_t v___x_1057_; 
v___x_1056_ = 57;
v___x_1057_ = lean_uint32_dec_le(v___x_1016_, v___x_1056_);
v___y_1049_ = v___x_1057_;
goto v___jp_1048_;
}
v___jp_1017_:
{
uint32_t v___x_1020_; uint8_t v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1025_; 
v___x_1020_ = 95;
v___x_1021_ = lean_uint32_dec_eq(v___x_1016_, v___x_1020_);
v___x_1022_ = lean_box(v___y_1018_);
v___x_1023_ = lean_box(v___y_1019_);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 1, v___x_1023_);
lean_ctor_set(v___x_1011_, 0, v___x_1022_);
v___x_1025_ = v___x_1011_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1022_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v___x_1023_);
v___x_1025_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1026_ = lean_box(v___x_1021_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 1, v___x_1025_);
lean_ctor_set(v___x_1007_, 0, v___x_1026_);
v___x_1028_ = v___x_1007_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v___x_1025_);
v___x_1028_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_object* v___x_1029_; lean_object* v___x_1031_; 
v___x_1029_ = lean_box(v___x_988_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 1, v___x_1028_);
lean_ctor_set(v___x_1003_, 0, v___x_1029_);
v___x_1031_ = v___x_1003_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1029_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v___x_1028_);
v___x_1031_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
lean_object* v___x_1032_; 
v___x_1032_ = lean_apply_4(v_recur_993_, v___x_1015_, v___x_1031_, lean_box(0), lean_box(0));
return v___x_1032_;
}
}
}
}
v___jp_1036_:
{
uint8_t v___x_1039_; 
v___x_1039_ = lean_unbox(v_fst_1005_);
lean_dec(v_fst_1005_);
if (v___x_1039_ == 0)
{
v___y_1018_ = v___y_1037_;
v___y_1019_ = v___y_1038_;
goto v___jp_1017_;
}
else
{
uint32_t v___x_1040_; uint8_t v___x_1041_; 
v___x_1040_ = 95;
v___x_1041_ = lean_uint32_dec_eq(v___x_1016_, v___x_1040_);
if (v___x_1041_ == 0)
{
v___y_1018_ = v___y_1037_;
v___y_1019_ = v___y_1038_;
goto v___jp_1017_;
}
else
{
v___y_1018_ = v___y_1037_;
v___y_1019_ = v___x_988_;
goto v___jp_1017_;
}
}
}
v___jp_1042_:
{
uint8_t v___x_1045_; 
v___x_1045_ = lean_unbox(v_fst_1001_);
lean_dec(v_fst_1001_);
if (v___x_1045_ == 0)
{
v___y_1037_ = v___y_1043_;
v___y_1038_ = v___y_1044_;
goto v___jp_1036_;
}
else
{
uint32_t v___x_1046_; uint8_t v___x_1047_; 
v___x_1046_ = 95;
v___x_1047_ = lean_uint32_dec_eq(v___x_1016_, v___x_1046_);
if (v___x_1047_ == 0)
{
v___y_1037_ = v___y_1043_;
v___y_1038_ = v___y_1044_;
goto v___jp_1036_;
}
else
{
if (v___x_988_ == 0)
{
lean_dec(v_fst_1005_);
v___y_1018_ = v___y_1043_;
v___y_1019_ = v___x_988_;
goto v___jp_1017_;
}
else
{
v___y_1037_ = v___y_1043_;
v___y_1038_ = v___x_988_;
goto v___jp_1036_;
}
}
}
}
v___jp_1048_:
{
uint8_t v___x_1050_; 
v___x_1050_ = lean_unbox(v_snd_1009_);
if (v___x_1050_ == 0)
{
uint8_t v___x_1051_; 
lean_dec(v_fst_1005_);
lean_dec(v_fst_1001_);
v___x_1051_ = lean_unbox(v_snd_1009_);
lean_dec(v_snd_1009_);
v___y_1018_ = v___y_1049_;
v___y_1019_ = v___x_1051_;
goto v___jp_1017_;
}
else
{
lean_dec(v_snd_1009_);
if (v___y_1049_ == 0)
{
uint32_t v___x_1052_; uint8_t v___x_1053_; 
v___x_1052_ = 95;
v___x_1053_ = lean_uint32_dec_eq(v___x_1016_, v___x_1052_);
if (v___x_1053_ == 0)
{
lean_dec(v_fst_1005_);
lean_dec(v_fst_1001_);
v___y_1018_ = v___y_1049_;
v___y_1019_ = v___x_1053_;
goto v___jp_1017_;
}
else
{
v___y_1043_ = v___y_1049_;
v___y_1044_ = v___x_1053_;
goto v___jp_1042_;
}
}
else
{
v___y_1043_ = v___y_1049_;
v___y_1044_ = v___x_989_;
goto v___jp_1042_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_recur_993_);
return v_acc_991_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___lam__0___boxed(lean_object* v___y_1064_, lean_object* v___x_1065_, lean_object* v___x_1066_, lean_object* v_it_1067_, lean_object* v_acc_1068_, lean_object* v_hP_1069_, lean_object* v_recur_1070_){
_start:
{
uint8_t v___x_1061__boxed_1071_; uint8_t v___x_1062__boxed_1072_; lean_object* v_res_1073_; 
v___x_1061__boxed_1071_ = lean_unbox(v___x_1065_);
v___x_1062__boxed_1072_ = lean_unbox(v___x_1066_);
v_res_1073_ = l_Substring_Raw_isNat___lam__0(v___y_1064_, v___x_1061__boxed_1071_, v___x_1062__boxed_1072_, v_it_1067_, v_acc_1068_, v_hP_1069_, v_recur_1070_);
lean_dec(v_it_1067_);
lean_dec_ref(v___y_1064_);
return v_res_1073_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_isNat(lean_object* v_s_1074_){
_start:
{
lean_object* v_str_1075_; lean_object* v_startPos_1076_; lean_object* v_stopPos_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1116_; 
v_str_1075_ = lean_ctor_get(v_s_1074_, 0);
v_startPos_1076_ = lean_ctor_get(v_s_1074_, 1);
v_stopPos_1077_ = lean_ctor_get(v_s_1074_, 2);
v_isSharedCheck_1116_ = !lean_is_exclusive(v_s_1074_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1079_ = v_s_1074_;
v_isShared_1080_ = v_isSharedCheck_1116_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_stopPos_1077_);
lean_inc(v_startPos_1076_);
lean_inc(v_str_1075_);
lean_dec(v_s_1074_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1116_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; 
v___x_1081_ = lean_nat_sub(v_stopPos_1077_, v_startPos_1076_);
v___x_1082_ = lean_unsigned_to_nat(0u);
v___x_1083_ = lean_nat_dec_eq(v___x_1081_, v___x_1082_);
lean_dec(v___x_1081_);
if (v___x_1083_ == 0)
{
uint8_t v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___y_1093_; lean_object* v___x_1105_; uint8_t v___x_1109_; 
v___x_1084_ = 1;
v___x_1085_ = lean_box(v___x_1083_);
v___x_1086_ = lean_box(v___x_1084_);
v___x_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1085_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
v___x_1088_ = lean_box(v___x_1083_);
v___x_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
lean_ctor_set(v___x_1089_, 1, v___x_1087_);
v___x_1090_ = lean_box(v___x_1084_);
v___x_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
lean_ctor_set(v___x_1091_, 1, v___x_1089_);
v___x_1105_ = l_String_instInhabitedSlice;
v___x_1109_ = lean_string_is_valid_pos(v_str_1075_, v_startPos_1076_);
if (v___x_1109_ == 0)
{
lean_del_object(v___x_1079_);
lean_dec(v_stopPos_1077_);
lean_dec(v_startPos_1076_);
lean_dec_ref(v_str_1075_);
goto v___jp_1106_;
}
else
{
uint8_t v___x_1110_; 
v___x_1110_ = lean_string_is_valid_pos(v_str_1075_, v_stopPos_1077_);
if (v___x_1110_ == 0)
{
lean_del_object(v___x_1079_);
lean_dec(v_stopPos_1077_);
lean_dec(v_startPos_1076_);
lean_dec_ref(v_str_1075_);
goto v___jp_1106_;
}
else
{
uint8_t v___x_1111_; 
v___x_1111_ = lean_nat_dec_le(v_startPos_1076_, v_stopPos_1077_);
if (v___x_1111_ == 0)
{
lean_del_object(v___x_1079_);
lean_dec(v_stopPos_1077_);
lean_dec(v_startPos_1076_);
lean_dec_ref(v_str_1075_);
goto v___jp_1106_;
}
else
{
lean_object* v___x_1113_; 
if (v_isShared_1080_ == 0)
{
v___x_1113_ = v___x_1079_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_str_1075_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_startPos_1076_);
lean_ctor_set(v_reuseFailAlloc_1114_, 2, v_stopPos_1077_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
v___y_1093_ = v___x_1113_;
goto v___jp_1092_;
}
}
}
}
v___jp_1092_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___f_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v_snd_1099_; lean_object* v_snd_1100_; lean_object* v_snd_1101_; uint8_t v___x_1102_; 
v___x_1094_ = lean_box(v___x_1083_);
v___x_1095_ = lean_box(v___x_1084_);
lean_inc_ref(v___y_1093_);
v___f_1096_ = lean_alloc_closure((void*)(l_Substring_Raw_isNat___lam__0___boxed), 7, 3);
lean_closure_set(v___f_1096_, 0, v___y_1093_);
lean_closure_set(v___f_1096_, 1, v___x_1094_);
lean_closure_set(v___f_1096_, 2, v___x_1095_);
v___x_1097_ = l_String_Slice_positions(v___y_1093_);
lean_dec_ref(v___y_1093_);
v___x_1098_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1096_, v___x_1097_, v___x_1091_, lean_box(0));
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
return v___x_1083_;
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
v___y_1093_ = v___x_1108_;
goto v___jp_1092_;
}
}
else
{
uint8_t v___x_1115_; 
lean_del_object(v___x_1079_);
lean_dec(v_stopPos_1077_);
lean_dec(v_startPos_1076_);
lean_dec_ref(v_str_1075_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(lean_object* v___x_1120_, lean_object* v___y_1121_, lean_object* v_a_1122_, lean_object* v_b_1123_){
_start:
{
lean_object* v_str_1124_; lean_object* v_startInclusive_1125_; lean_object* v_endExclusive_1126_; lean_object* v___x_1127_; uint8_t v___x_1128_; 
v_str_1124_ = lean_ctor_get(v___y_1121_, 0);
v_startInclusive_1125_ = lean_ctor_get(v___y_1121_, 1);
v_endExclusive_1126_ = lean_ctor_get(v___y_1121_, 2);
v___x_1127_ = lean_nat_sub(v_endExclusive_1126_, v_startInclusive_1125_);
v___x_1128_ = lean_nat_dec_eq(v_a_1122_, v___x_1127_);
lean_dec(v___x_1127_);
if (v___x_1128_ == 0)
{
lean_object* v_snd_1129_; lean_object* v_snd_1130_; lean_object* v_fst_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1195_; 
v_snd_1129_ = lean_ctor_get(v_b_1123_, 1);
lean_inc(v_snd_1129_);
v_snd_1130_ = lean_ctor_get(v_snd_1129_, 1);
lean_inc(v_snd_1130_);
v_fst_1131_ = lean_ctor_get(v_b_1123_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_b_1123_);
if (v_isSharedCheck_1195_ == 0)
{
lean_object* v_unused_1196_; 
v_unused_1196_ = lean_ctor_get(v_b_1123_, 1);
lean_dec(v_unused_1196_);
v___x_1133_ = v_b_1123_;
v_isShared_1134_ = v_isSharedCheck_1195_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_fst_1131_);
lean_dec(v_b_1123_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1195_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v_fst_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1193_; 
v_fst_1135_ = lean_ctor_get(v_snd_1129_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v_snd_1129_);
if (v_isSharedCheck_1193_ == 0)
{
lean_object* v_unused_1194_; 
v_unused_1194_ = lean_ctor_get(v_snd_1129_, 1);
lean_dec(v_unused_1194_);
v___x_1137_ = v_snd_1129_;
v_isShared_1138_ = v_isSharedCheck_1193_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_fst_1135_);
lean_dec(v_snd_1129_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1193_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v_snd_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1191_; 
v_snd_1139_ = lean_ctor_get(v_snd_1130_, 1);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_snd_1130_);
if (v_isSharedCheck_1191_ == 0)
{
lean_object* v_unused_1192_; 
v_unused_1192_ = lean_ctor_get(v_snd_1130_, 0);
lean_dec(v_unused_1192_);
v___x_1141_ = v_snd_1130_;
v_isShared_1142_ = v_isSharedCheck_1191_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_snd_1139_);
lean_dec(v_snd_1130_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1191_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1143_; uint8_t v___x_1144_; uint8_t v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; uint32_t v___x_1149_; uint8_t v___y_1151_; uint8_t v___y_1152_; uint8_t v___y_1170_; uint8_t v___y_1171_; uint8_t v___y_1176_; uint8_t v___y_1177_; uint8_t v___y_1182_; uint32_t v___x_1187_; uint8_t v___x_1188_; 
v___x_1143_ = lean_unsigned_to_nat(0u);
v___x_1144_ = lean_nat_dec_eq(v___x_1120_, v___x_1143_);
v___x_1145_ = 1;
v___x_1146_ = lean_nat_add(v_startInclusive_1125_, v_a_1122_);
lean_dec(v_a_1122_);
v___x_1147_ = lean_string_utf8_next_fast(v_str_1124_, v___x_1146_);
v___x_1148_ = lean_nat_sub(v___x_1147_, v_startInclusive_1125_);
v___x_1149_ = lean_string_utf8_get_fast(v_str_1124_, v___x_1146_);
lean_dec(v___x_1146_);
v___x_1187_ = 48;
v___x_1188_ = lean_uint32_dec_le(v___x_1187_, v___x_1149_);
if (v___x_1188_ == 0)
{
v___y_1182_ = v___x_1188_;
goto v___jp_1181_;
}
else
{
uint32_t v___x_1189_; uint8_t v___x_1190_; 
v___x_1189_ = 57;
v___x_1190_ = lean_uint32_dec_le(v___x_1149_, v___x_1189_);
v___y_1182_ = v___x_1190_;
goto v___jp_1181_;
}
v___jp_1150_:
{
uint32_t v___x_1153_; uint8_t v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1158_; 
v___x_1153_ = 95;
v___x_1154_ = lean_uint32_dec_eq(v___x_1149_, v___x_1153_);
v___x_1155_ = lean_box(v___y_1151_);
v___x_1156_ = lean_box(v___y_1152_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 1, v___x_1156_);
lean_ctor_set(v___x_1141_, 0, v___x_1155_);
v___x_1158_ = v___x_1141_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1155_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v___x_1156_);
v___x_1158_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1159_ = lean_box(v___x_1154_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 1, v___x_1158_);
lean_ctor_set(v___x_1137_, 0, v___x_1159_);
v___x_1161_ = v___x_1137_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1159_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v___x_1158_);
v___x_1161_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1162_; lean_object* v___x_1164_; 
v___x_1162_ = lean_box(v___x_1144_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 1, v___x_1161_);
lean_ctor_set(v___x_1133_, 0, v___x_1162_);
v___x_1164_ = v___x_1133_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v___x_1161_);
v___x_1164_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
v_a_1122_ = v___x_1148_;
v_b_1123_ = v___x_1164_;
goto _start;
}
}
}
}
v___jp_1169_:
{
uint8_t v___x_1172_; 
v___x_1172_ = lean_unbox(v_fst_1135_);
lean_dec(v_fst_1135_);
if (v___x_1172_ == 0)
{
v___y_1151_ = v___y_1170_;
v___y_1152_ = v___y_1171_;
goto v___jp_1150_;
}
else
{
uint32_t v___x_1173_; uint8_t v___x_1174_; 
v___x_1173_ = 95;
v___x_1174_ = lean_uint32_dec_eq(v___x_1149_, v___x_1173_);
if (v___x_1174_ == 0)
{
v___y_1151_ = v___y_1170_;
v___y_1152_ = v___y_1171_;
goto v___jp_1150_;
}
else
{
v___y_1151_ = v___y_1170_;
v___y_1152_ = v___x_1144_;
goto v___jp_1150_;
}
}
}
v___jp_1175_:
{
uint8_t v___x_1178_; 
v___x_1178_ = lean_unbox(v_fst_1131_);
lean_dec(v_fst_1131_);
if (v___x_1178_ == 0)
{
v___y_1170_ = v___y_1176_;
v___y_1171_ = v___y_1177_;
goto v___jp_1169_;
}
else
{
uint32_t v___x_1179_; uint8_t v___x_1180_; 
v___x_1179_ = 95;
v___x_1180_ = lean_uint32_dec_eq(v___x_1149_, v___x_1179_);
if (v___x_1180_ == 0)
{
v___y_1170_ = v___y_1176_;
v___y_1171_ = v___y_1177_;
goto v___jp_1169_;
}
else
{
if (v___x_1144_ == 0)
{
lean_dec(v_fst_1135_);
v___y_1151_ = v___y_1176_;
v___y_1152_ = v___x_1144_;
goto v___jp_1150_;
}
else
{
v___y_1170_ = v___y_1176_;
v___y_1171_ = v___x_1144_;
goto v___jp_1169_;
}
}
}
}
v___jp_1181_:
{
uint8_t v___x_1183_; 
v___x_1183_ = lean_unbox(v_snd_1139_);
if (v___x_1183_ == 0)
{
uint8_t v___x_1184_; 
lean_dec(v_fst_1135_);
lean_dec(v_fst_1131_);
v___x_1184_ = lean_unbox(v_snd_1139_);
lean_dec(v_snd_1139_);
v___y_1151_ = v___y_1182_;
v___y_1152_ = v___x_1184_;
goto v___jp_1150_;
}
else
{
lean_dec(v_snd_1139_);
if (v___y_1182_ == 0)
{
uint32_t v___x_1185_; uint8_t v___x_1186_; 
v___x_1185_ = 95;
v___x_1186_ = lean_uint32_dec_eq(v___x_1149_, v___x_1185_);
if (v___x_1186_ == 0)
{
lean_dec(v_fst_1135_);
lean_dec(v_fst_1131_);
v___y_1151_ = v___y_1182_;
v___y_1152_ = v___x_1186_;
goto v___jp_1150_;
}
else
{
v___y_1176_ = v___y_1182_;
v___y_1177_ = v___x_1186_;
goto v___jp_1175_;
}
}
else
{
v___y_1176_ = v___y_1182_;
v___y_1177_ = v___x_1145_;
goto v___jp_1175_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1122_);
return v_b_1123_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg___boxed(lean_object* v___x_1197_, lean_object* v___y_1198_, lean_object* v_a_1199_, lean_object* v_b_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(v___x_1197_, v___y_1198_, v_a_1199_, v_b_1200_);
lean_dec_ref(v___y_1198_);
lean_dec(v___x_1197_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(lean_object* v___y_1202_, lean_object* v_a_1203_, lean_object* v_b_1204_){
_start:
{
lean_object* v_str_1205_; lean_object* v_startInclusive_1206_; lean_object* v_endExclusive_1207_; lean_object* v___x_1208_; uint8_t v___x_1209_; 
v_str_1205_ = lean_ctor_get(v___y_1202_, 0);
v_startInclusive_1206_ = lean_ctor_get(v___y_1202_, 1);
v_endExclusive_1207_ = lean_ctor_get(v___y_1202_, 2);
v___x_1208_ = lean_nat_sub(v_endExclusive_1207_, v_startInclusive_1206_);
v___x_1209_ = lean_nat_dec_eq(v_a_1203_, v___x_1208_);
lean_dec(v___x_1208_);
if (v___x_1209_ == 0)
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; uint32_t v___x_1213_; uint32_t v___x_1214_; uint8_t v___x_1215_; 
v___x_1210_ = lean_nat_add(v_startInclusive_1206_, v_a_1203_);
lean_dec(v_a_1203_);
v___x_1211_ = lean_string_utf8_next_fast(v_str_1205_, v___x_1210_);
v___x_1212_ = lean_nat_sub(v___x_1211_, v_startInclusive_1206_);
v___x_1213_ = lean_string_utf8_get_fast(v_str_1205_, v___x_1210_);
lean_dec(v___x_1210_);
v___x_1214_ = 95;
v___x_1215_ = lean_uint32_dec_eq(v___x_1213_, v___x_1214_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1216_ = lean_unsigned_to_nat(10u);
v___x_1217_ = lean_nat_mul(v_b_1204_, v___x_1216_);
lean_dec(v_b_1204_);
v___x_1218_ = lean_uint32_to_nat(v___x_1213_);
v___x_1219_ = lean_unsigned_to_nat(48u);
v___x_1220_ = lean_nat_sub(v___x_1218_, v___x_1219_);
lean_dec(v___x_1218_);
v___x_1221_ = lean_nat_add(v___x_1217_, v___x_1220_);
lean_dec(v___x_1220_);
lean_dec(v___x_1217_);
v_a_1203_ = v___x_1212_;
v_b_1204_ = v___x_1221_;
goto _start;
}
else
{
v_a_1203_ = v___x_1212_;
goto _start;
}
}
else
{
lean_dec(v_a_1203_);
return v_b_1204_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg___boxed(lean_object* v___y_1224_, lean_object* v_a_1225_, lean_object* v_b_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(v___y_1224_, v_a_1225_, v_b_1226_);
lean_dec_ref(v___y_1224_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toNat_x3f(lean_object* v_s_1228_){
_start:
{
lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1236_; lean_object* v_str_1239_; lean_object* v_startPos_1240_; lean_object* v_stopPos_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1284_; 
v_str_1239_ = lean_ctor_get(v_s_1228_, 0);
v_startPos_1240_ = lean_ctor_get(v_s_1228_, 1);
v_stopPos_1241_ = lean_ctor_get(v_s_1228_, 2);
v_isSharedCheck_1284_ = !lean_is_exclusive(v_s_1228_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1243_ = v_s_1228_;
v_isShared_1244_ = v_isSharedCheck_1284_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_stopPos_1241_);
lean_inc(v_startPos_1240_);
lean_inc(v_str_1239_);
lean_dec(v_s_1228_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1284_;
goto v_resetjp_1242_;
}
v___jp_1229_:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1232_ = l_String_Slice_positions(v___y_1231_);
v___x_1233_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(v___y_1231_, v___x_1232_, v___y_1230_);
lean_dec_ref(v___y_1231_);
v___x_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
return v___x_1234_;
}
v___jp_1235_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_1238_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_1237_);
v___y_1230_ = v___y_1236_;
v___y_1231_ = v___x_1238_;
goto v___jp_1229_;
}
v_resetjp_1242_:
{
uint8_t v___y_1246_; lean_object* v___x_1255_; lean_object* v___x_1256_; uint8_t v___x_1257_; 
v___x_1255_ = lean_nat_sub(v_stopPos_1241_, v_startPos_1240_);
v___x_1256_ = lean_unsigned_to_nat(0u);
v___x_1257_ = lean_nat_dec_eq(v___x_1255_, v___x_1256_);
if (v___x_1257_ == 0)
{
uint8_t v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___y_1267_; uint8_t v___x_1279_; 
v___x_1258_ = 1;
v___x_1259_ = lean_box(v___x_1257_);
v___x_1260_ = lean_box(v___x_1258_);
v___x_1261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1259_);
lean_ctor_set(v___x_1261_, 1, v___x_1260_);
v___x_1262_ = lean_box(v___x_1257_);
v___x_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
lean_ctor_set(v___x_1263_, 1, v___x_1261_);
v___x_1264_ = lean_box(v___x_1258_);
v___x_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
lean_ctor_set(v___x_1265_, 1, v___x_1263_);
v___x_1279_ = lean_string_is_valid_pos(v_str_1239_, v_startPos_1240_);
if (v___x_1279_ == 0)
{
goto v___jp_1276_;
}
else
{
uint8_t v___x_1280_; 
v___x_1280_ = lean_string_is_valid_pos(v_str_1239_, v_stopPos_1241_);
if (v___x_1280_ == 0)
{
goto v___jp_1276_;
}
else
{
uint8_t v___x_1281_; 
v___x_1281_ = lean_nat_dec_le(v_startPos_1240_, v_stopPos_1241_);
if (v___x_1281_ == 0)
{
goto v___jp_1276_;
}
else
{
lean_object* v___x_1282_; 
lean_inc(v_stopPos_1241_);
lean_inc(v_startPos_1240_);
lean_inc_ref(v_str_1239_);
v___x_1282_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1282_, 0, v_str_1239_);
lean_ctor_set(v___x_1282_, 1, v_startPos_1240_);
lean_ctor_set(v___x_1282_, 2, v_stopPos_1241_);
v___y_1267_ = v___x_1282_;
goto v___jp_1266_;
}
}
}
v___jp_1266_:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v_snd_1270_; lean_object* v_snd_1271_; lean_object* v_snd_1272_; uint8_t v___x_1273_; 
v___x_1268_ = l_String_Slice_positions(v___y_1267_);
v___x_1269_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(v___x_1255_, v___y_1267_, v___x_1268_, v___x_1265_);
lean_dec_ref(v___y_1267_);
lean_dec(v___x_1255_);
v_snd_1270_ = lean_ctor_get(v___x_1269_, 1);
lean_inc(v_snd_1270_);
lean_dec_ref(v___x_1269_);
v_snd_1271_ = lean_ctor_get(v_snd_1270_, 1);
lean_inc(v_snd_1271_);
lean_dec(v_snd_1270_);
v_snd_1272_ = lean_ctor_get(v_snd_1271_, 1);
v___x_1273_ = lean_unbox(v_snd_1272_);
if (v___x_1273_ == 0)
{
lean_dec(v_snd_1271_);
v___y_1246_ = v___x_1257_;
goto v___jp_1245_;
}
else
{
lean_object* v_fst_1274_; uint8_t v___x_1275_; 
v_fst_1274_ = lean_ctor_get(v_snd_1271_, 0);
lean_inc(v_fst_1274_);
lean_dec(v_snd_1271_);
v___x_1275_ = lean_unbox(v_fst_1274_);
lean_dec(v_fst_1274_);
v___y_1246_ = v___x_1275_;
goto v___jp_1245_;
}
}
v___jp_1276_:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_1278_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_1277_);
v___y_1267_ = v___x_1278_;
goto v___jp_1266_;
}
}
else
{
lean_object* v___x_1283_; 
lean_dec(v___x_1255_);
lean_del_object(v___x_1243_);
lean_dec(v_stopPos_1241_);
lean_dec(v_startPos_1240_);
lean_dec_ref(v_str_1239_);
v___x_1283_ = lean_box(0);
return v___x_1283_;
}
v___jp_1245_:
{
if (v___y_1246_ == 0)
{
lean_object* v___x_1247_; 
lean_del_object(v___x_1243_);
lean_dec(v_stopPos_1241_);
lean_dec(v_startPos_1240_);
lean_dec_ref(v_str_1239_);
v___x_1247_ = lean_box(0);
return v___x_1247_;
}
else
{
lean_object* v___x_1248_; uint8_t v___x_1249_; 
v___x_1248_ = lean_unsigned_to_nat(0u);
v___x_1249_ = lean_string_is_valid_pos(v_str_1239_, v_startPos_1240_);
if (v___x_1249_ == 0)
{
lean_del_object(v___x_1243_);
lean_dec(v_stopPos_1241_);
lean_dec(v_startPos_1240_);
lean_dec_ref(v_str_1239_);
v___y_1236_ = v___x_1248_;
goto v___jp_1235_;
}
else
{
uint8_t v___x_1250_; 
v___x_1250_ = lean_string_is_valid_pos(v_str_1239_, v_stopPos_1241_);
if (v___x_1250_ == 0)
{
lean_del_object(v___x_1243_);
lean_dec(v_stopPos_1241_);
lean_dec(v_startPos_1240_);
lean_dec_ref(v_str_1239_);
v___y_1236_ = v___x_1248_;
goto v___jp_1235_;
}
else
{
uint8_t v___x_1251_; 
v___x_1251_ = lean_nat_dec_le(v_startPos_1240_, v_stopPos_1241_);
if (v___x_1251_ == 0)
{
lean_del_object(v___x_1243_);
lean_dec(v_stopPos_1241_);
lean_dec(v_startPos_1240_);
lean_dec_ref(v_str_1239_);
v___y_1236_ = v___x_1248_;
goto v___jp_1235_;
}
else
{
lean_object* v___x_1253_; 
if (v_isShared_1244_ == 0)
{
v___x_1253_ = v___x_1243_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_str_1239_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v_startPos_1240_);
lean_ctor_set(v_reuseFailAlloc_1254_, 2, v_stopPos_1241_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
v___y_1230_ = v___x_1248_;
v___y_1231_ = v___x_1253_;
goto v___jp_1229_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0(lean_object* v___y_1285_, lean_object* v_inst_1286_, lean_object* v_R_1287_, lean_object* v_a_1288_, lean_object* v_b_1289_, lean_object* v_c_1290_){
_start:
{
lean_object* v___x_1291_; 
v___x_1291_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(v___y_1285_, v_a_1288_, v_b_1289_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___boxed(lean_object* v___y_1292_, lean_object* v_inst_1293_, lean_object* v_R_1294_, lean_object* v_a_1295_, lean_object* v_b_1296_, lean_object* v_c_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0(v___y_1292_, v_inst_1293_, v_R_1294_, v_a_1295_, v_b_1296_, v_c_1297_);
lean_dec_ref(v___y_1292_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1(lean_object* v___x_1299_, lean_object* v___y_1300_, lean_object* v_inst_1301_, lean_object* v_R_1302_, lean_object* v_a_1303_, lean_object* v_b_1304_, lean_object* v_c_1305_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(v___x_1299_, v___y_1300_, v_a_1303_, v_b_1304_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___boxed(lean_object* v___x_1307_, lean_object* v___y_1308_, lean_object* v_inst_1309_, lean_object* v_R_1310_, lean_object* v_a_1311_, lean_object* v_b_1312_, lean_object* v_c_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1(v___x_1307_, v___y_1308_, v_inst_1309_, v_R_1310_, v_a_1311_, v_b_1312_, v_c_1313_);
lean_dec_ref(v___y_1308_);
lean_dec(v___x_1307_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_repair(lean_object* v_x_1315_){
_start:
{
lean_object* v_str_1316_; lean_object* v_startPos_1317_; lean_object* v_stopPos_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1334_; 
v_str_1316_ = lean_ctor_get(v_x_1315_, 0);
v_startPos_1317_ = lean_ctor_get(v_x_1315_, 1);
v_stopPos_1318_ = lean_ctor_get(v_x_1315_, 2);
v_isSharedCheck_1334_ = !lean_is_exclusive(v_x_1315_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1320_ = v_x_1315_;
v_isShared_1321_ = v_isSharedCheck_1334_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_stopPos_1318_);
lean_inc(v_startPos_1317_);
lean_inc(v_str_1316_);
lean_dec(v_x_1315_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1334_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___y_1323_; uint8_t v___x_1332_; 
v___x_1332_ = lean_string_is_valid_pos(v_str_1316_, v_startPos_1317_);
if (v___x_1332_ == 0)
{
lean_object* v___x_1333_; 
lean_dec(v_startPos_1317_);
v___x_1333_ = lean_string_utf8_byte_size(v_str_1316_);
v___y_1323_ = v___x_1333_;
goto v___jp_1322_;
}
else
{
v___y_1323_ = v_startPos_1317_;
goto v___jp_1322_;
}
v___jp_1322_:
{
uint8_t v___x_1324_; 
v___x_1324_ = lean_string_is_valid_pos(v_str_1316_, v_stopPos_1318_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; lean_object* v___x_1327_; 
lean_dec(v_stopPos_1318_);
v___x_1325_ = lean_string_utf8_byte_size(v_str_1316_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 2, v___x_1325_);
lean_ctor_set(v___x_1320_, 1, v___y_1323_);
v___x_1327_ = v___x_1320_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_str_1316_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v___y_1323_);
lean_ctor_set(v_reuseFailAlloc_1328_, 2, v___x_1325_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
else
{
lean_object* v___x_1330_; 
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 1, v___y_1323_);
v___x_1330_ = v___x_1320_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_str_1316_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v___y_1323_);
lean_ctor_set(v_reuseFailAlloc_1331_, 2, v_stopPos_1318_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_beq(lean_object* v_ss1_1335_, lean_object* v_ss2_1336_){
_start:
{
lean_object* v_ss1_1337_; lean_object* v_str_1338_; lean_object* v_startPos_1339_; lean_object* v_stopPos_1340_; lean_object* v_ss2_1341_; lean_object* v_str_1342_; lean_object* v_startPos_1343_; lean_object* v_stopPos_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; uint8_t v___x_1347_; 
v_ss1_1337_ = l_Substring_Raw_repair(v_ss1_1335_);
v_str_1338_ = lean_ctor_get(v_ss1_1337_, 0);
lean_inc_ref(v_str_1338_);
v_startPos_1339_ = lean_ctor_get(v_ss1_1337_, 1);
lean_inc(v_startPos_1339_);
v_stopPos_1340_ = lean_ctor_get(v_ss1_1337_, 2);
lean_inc(v_stopPos_1340_);
lean_dec_ref(v_ss1_1337_);
v_ss2_1341_ = l_Substring_Raw_repair(v_ss2_1336_);
v_str_1342_ = lean_ctor_get(v_ss2_1341_, 0);
lean_inc_ref(v_str_1342_);
v_startPos_1343_ = lean_ctor_get(v_ss2_1341_, 1);
lean_inc(v_startPos_1343_);
v_stopPos_1344_ = lean_ctor_get(v_ss2_1341_, 2);
lean_inc(v_stopPos_1344_);
lean_dec_ref(v_ss2_1341_);
v___x_1345_ = lean_nat_sub(v_stopPos_1340_, v_startPos_1339_);
lean_dec(v_stopPos_1340_);
v___x_1346_ = lean_nat_sub(v_stopPos_1344_, v_startPos_1343_);
lean_dec(v_stopPos_1344_);
v___x_1347_ = lean_nat_dec_eq(v___x_1345_, v___x_1346_);
lean_dec(v___x_1346_);
if (v___x_1347_ == 0)
{
lean_dec(v___x_1345_);
lean_dec(v_startPos_1343_);
lean_dec_ref(v_str_1342_);
lean_dec(v_startPos_1339_);
lean_dec_ref(v_str_1338_);
return v___x_1347_;
}
else
{
uint8_t v___x_1348_; 
v___x_1348_ = l_String_Pos_Raw_substrEq(v_str_1338_, v_startPos_1339_, v_str_1342_, v_startPos_1343_, v___x_1345_);
lean_dec(v___x_1345_);
lean_dec_ref(v_str_1342_);
lean_dec_ref(v_str_1338_);
return v___x_1348_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_beq___boxed(lean_object* v_ss1_1349_, lean_object* v_ss2_1350_){
_start:
{
uint8_t v_res_1351_; lean_object* v_r_1352_; 
v_res_1351_ = l_Substring_Raw_beq(v_ss1_1349_, v_ss2_1350_);
v_r_1352_ = lean_box(v_res_1351_);
return v_r_1352_;
}
}
LEAN_EXPORT uint8_t lean_substring_beq(lean_object* v_ss1_1353_, lean_object* v_ss2_1354_){
_start:
{
uint8_t v___x_1355_; 
v___x_1355_ = l_Substring_Raw_beq(v_ss1_1353_, v_ss2_1354_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_beqImpl___boxed(lean_object* v_ss1_1356_, lean_object* v_ss2_1357_){
_start:
{
uint8_t v_res_1358_; lean_object* v_r_1359_; 
v_res_1358_ = lean_substring_beq(v_ss1_1356_, v_ss2_1357_);
v_r_1359_ = lean_box(v_res_1358_);
return v_r_1359_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_sameAs(lean_object* v_ss1_1362_, lean_object* v_ss2_1363_){
_start:
{
lean_object* v_startPos_1364_; lean_object* v_startPos_1365_; uint8_t v___x_1366_; 
v_startPos_1364_ = lean_ctor_get(v_ss1_1362_, 1);
v_startPos_1365_ = lean_ctor_get(v_ss2_1363_, 1);
v___x_1366_ = lean_nat_dec_eq(v_startPos_1364_, v_startPos_1365_);
if (v___x_1366_ == 0)
{
lean_dec_ref(v_ss2_1363_);
lean_dec_ref(v_ss1_1362_);
return v___x_1366_;
}
else
{
uint8_t v___x_1367_; 
v___x_1367_ = l_Substring_Raw_beq(v_ss1_1362_, v_ss2_1363_);
return v___x_1367_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_sameAs___boxed(lean_object* v_ss1_1368_, lean_object* v_ss2_1369_){
_start:
{
uint8_t v_res_1370_; lean_object* v_r_1371_; 
v_res_1370_ = l_Substring_Raw_sameAs(v_ss1_1368_, v_ss2_1369_);
v_r_1371_ = lean_box(v_res_1370_);
return v_r_1371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(lean_object* v_s_1372_, lean_object* v_t_1373_, lean_object* v_spos_1374_, lean_object* v_tpos_1375_){
_start:
{
lean_object* v_str_1376_; lean_object* v_stopPos_1377_; uint8_t v___x_1378_; 
v_str_1376_ = lean_ctor_get(v_s_1372_, 0);
v_stopPos_1377_ = lean_ctor_get(v_s_1372_, 2);
v___x_1378_ = lean_nat_dec_lt(v_spos_1374_, v_stopPos_1377_);
if (v___x_1378_ == 0)
{
lean_dec(v_tpos_1375_);
return v_spos_1374_;
}
else
{
lean_object* v_str_1379_; lean_object* v_stopPos_1380_; uint8_t v___x_1381_; 
v_str_1379_ = lean_ctor_get(v_t_1373_, 0);
v_stopPos_1380_ = lean_ctor_get(v_t_1373_, 2);
v___x_1381_ = lean_nat_dec_lt(v_tpos_1375_, v_stopPos_1380_);
if (v___x_1381_ == 0)
{
lean_dec(v_tpos_1375_);
return v_spos_1374_;
}
else
{
uint32_t v___x_1382_; uint32_t v___x_1383_; uint8_t v___x_1384_; 
v___x_1382_ = lean_string_utf8_get(v_str_1376_, v_spos_1374_);
v___x_1383_ = lean_string_utf8_get(v_str_1379_, v_tpos_1375_);
v___x_1384_ = lean_uint32_dec_eq(v___x_1382_, v___x_1383_);
if (v___x_1384_ == 0)
{
lean_dec(v_tpos_1375_);
return v_spos_1374_;
}
else
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = lean_string_utf8_next(v_str_1376_, v_spos_1374_);
lean_dec(v_spos_1374_);
v___x_1386_ = lean_string_utf8_next(v_str_1379_, v_tpos_1375_);
lean_dec(v_tpos_1375_);
v_spos_1374_ = v___x_1385_;
v_tpos_1375_ = v___x_1386_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop___boxed(lean_object* v_s_1388_, lean_object* v_t_1389_, lean_object* v_spos_1390_, lean_object* v_tpos_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(v_s_1388_, v_t_1389_, v_spos_1390_, v_tpos_1391_);
lean_dec_ref(v_t_1389_);
lean_dec_ref(v_s_1388_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_commonPrefix(lean_object* v_s_1393_, lean_object* v_t_1394_){
_start:
{
lean_object* v_str_1395_; lean_object* v_startPos_1396_; lean_object* v_startPos_1397_; lean_object* v___x_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
v_str_1395_ = lean_ctor_get(v_s_1393_, 0);
lean_inc_ref(v_str_1395_);
v_startPos_1396_ = lean_ctor_get(v_s_1393_, 1);
lean_inc(v_startPos_1396_);
v_startPos_1397_ = lean_ctor_get(v_t_1394_, 1);
lean_inc(v_startPos_1397_);
lean_inc(v_startPos_1396_);
v___x_1398_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(v_s_1393_, v_t_1394_, v_startPos_1396_, v_startPos_1397_);
lean_dec_ref(v_s_1393_);
v_isSharedCheck_1405_ = !lean_is_exclusive(v_t_1394_);
if (v_isSharedCheck_1405_ == 0)
{
lean_object* v_unused_1406_; lean_object* v_unused_1407_; lean_object* v_unused_1408_; 
v_unused_1406_ = lean_ctor_get(v_t_1394_, 2);
lean_dec(v_unused_1406_);
v_unused_1407_ = lean_ctor_get(v_t_1394_, 1);
lean_dec(v_unused_1407_);
v_unused_1408_ = lean_ctor_get(v_t_1394_, 0);
lean_dec(v_unused_1408_);
v___x_1400_ = v_t_1394_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_dec(v_t_1394_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 2, v___x_1398_);
lean_ctor_set(v___x_1400_, 1, v_startPos_1396_);
lean_ctor_set(v___x_1400_, 0, v_str_1395_);
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_str_1395_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v_startPos_1396_);
lean_ctor_set(v_reuseFailAlloc_1404_, 2, v___x_1398_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(lean_object* v_s_1409_, lean_object* v_t_1410_, lean_object* v_spos_1411_, lean_object* v_tpos_1412_){
_start:
{
lean_object* v_str_1413_; lean_object* v_startPos_1414_; uint8_t v___x_1415_; 
v_str_1413_ = lean_ctor_get(v_s_1409_, 0);
v_startPos_1414_ = lean_ctor_get(v_s_1409_, 1);
v___x_1415_ = lean_nat_dec_lt(v_startPos_1414_, v_spos_1411_);
if (v___x_1415_ == 0)
{
lean_dec(v_tpos_1412_);
return v_spos_1411_;
}
else
{
lean_object* v_str_1416_; lean_object* v_startPos_1417_; uint8_t v___x_1418_; 
v_str_1416_ = lean_ctor_get(v_t_1410_, 0);
v_startPos_1417_ = lean_ctor_get(v_t_1410_, 1);
v___x_1418_ = lean_nat_dec_lt(v_startPos_1417_, v_tpos_1412_);
if (v___x_1418_ == 0)
{
lean_dec(v_tpos_1412_);
return v_spos_1411_;
}
else
{
lean_object* v_spos_x27_1419_; lean_object* v_tpos_x27_1420_; uint32_t v___x_1421_; uint32_t v___x_1422_; uint8_t v___x_1423_; 
v_spos_x27_1419_ = lean_string_utf8_prev(v_str_1413_, v_spos_1411_);
v_tpos_x27_1420_ = lean_string_utf8_prev(v_str_1416_, v_tpos_1412_);
lean_dec(v_tpos_1412_);
v___x_1421_ = lean_string_utf8_get(v_str_1413_, v_spos_x27_1419_);
v___x_1422_ = lean_string_utf8_get(v_str_1416_, v_tpos_x27_1420_);
v___x_1423_ = lean_uint32_dec_eq(v___x_1421_, v___x_1422_);
if (v___x_1423_ == 0)
{
lean_dec(v_tpos_x27_1420_);
lean_dec(v_spos_x27_1419_);
return v_spos_1411_;
}
else
{
lean_dec(v_spos_1411_);
v_spos_1411_ = v_spos_x27_1419_;
v_tpos_1412_ = v_tpos_x27_1420_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop___boxed(lean_object* v_s_1425_, lean_object* v_t_1426_, lean_object* v_spos_1427_, lean_object* v_tpos_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(v_s_1425_, v_t_1426_, v_spos_1427_, v_tpos_1428_);
lean_dec_ref(v_t_1426_);
lean_dec_ref(v_s_1425_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_commonSuffix(lean_object* v_s_1430_, lean_object* v_t_1431_){
_start:
{
lean_object* v_str_1432_; lean_object* v_stopPos_1433_; lean_object* v_stopPos_1434_; lean_object* v___x_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
v_str_1432_ = lean_ctor_get(v_s_1430_, 0);
lean_inc_ref(v_str_1432_);
v_stopPos_1433_ = lean_ctor_get(v_s_1430_, 2);
lean_inc(v_stopPos_1433_);
v_stopPos_1434_ = lean_ctor_get(v_t_1431_, 2);
lean_inc(v_stopPos_1434_);
lean_inc(v_stopPos_1433_);
v___x_1435_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(v_s_1430_, v_t_1431_, v_stopPos_1433_, v_stopPos_1434_);
lean_dec_ref(v_s_1430_);
v_isSharedCheck_1442_ = !lean_is_exclusive(v_t_1431_);
if (v_isSharedCheck_1442_ == 0)
{
lean_object* v_unused_1443_; lean_object* v_unused_1444_; lean_object* v_unused_1445_; 
v_unused_1443_ = lean_ctor_get(v_t_1431_, 2);
lean_dec(v_unused_1443_);
v_unused_1444_ = lean_ctor_get(v_t_1431_, 1);
lean_dec(v_unused_1444_);
v_unused_1445_ = lean_ctor_get(v_t_1431_, 0);
lean_dec(v_unused_1445_);
v___x_1437_ = v_t_1431_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_dec(v_t_1431_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 2, v_stopPos_1433_);
lean_ctor_set(v___x_1437_, 1, v___x_1435_);
lean_ctor_set(v___x_1437_, 0, v_str_1432_);
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_str_1432_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v___x_1435_);
lean_ctor_set(v_reuseFailAlloc_1441_, 2, v_stopPos_1433_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropPrefix_x3f(lean_object* v_s_1446_, lean_object* v_pre_1447_){
_start:
{
lean_object* v_t_1448_; lean_object* v_startPos_1449_; lean_object* v_stopPos_1450_; lean_object* v_startPos_1451_; lean_object* v_stopPos_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; uint8_t v___x_1455_; 
lean_inc_ref(v_pre_1447_);
lean_inc_ref(v_s_1446_);
v_t_1448_ = l_Substring_Raw_commonPrefix(v_s_1446_, v_pre_1447_);
v_startPos_1449_ = lean_ctor_get(v_t_1448_, 1);
lean_inc(v_startPos_1449_);
v_stopPos_1450_ = lean_ctor_get(v_t_1448_, 2);
lean_inc(v_stopPos_1450_);
lean_dec_ref(v_t_1448_);
v_startPos_1451_ = lean_ctor_get(v_pre_1447_, 1);
lean_inc(v_startPos_1451_);
v_stopPos_1452_ = lean_ctor_get(v_pre_1447_, 2);
lean_inc(v_stopPos_1452_);
lean_dec_ref(v_pre_1447_);
v___x_1453_ = lean_nat_sub(v_stopPos_1450_, v_startPos_1449_);
lean_dec(v_startPos_1449_);
v___x_1454_ = lean_nat_sub(v_stopPos_1452_, v_startPos_1451_);
lean_dec(v_startPos_1451_);
lean_dec(v_stopPos_1452_);
v___x_1455_ = lean_nat_dec_eq(v___x_1453_, v___x_1454_);
lean_dec(v___x_1454_);
lean_dec(v___x_1453_);
if (v___x_1455_ == 0)
{
lean_object* v___x_1456_; 
lean_dec(v_stopPos_1450_);
lean_dec_ref(v_s_1446_);
v___x_1456_ = lean_box(0);
return v___x_1456_;
}
else
{
lean_object* v_str_1457_; lean_object* v_stopPos_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1466_; 
v_str_1457_ = lean_ctor_get(v_s_1446_, 0);
v_stopPos_1458_ = lean_ctor_get(v_s_1446_, 2);
v_isSharedCheck_1466_ = !lean_is_exclusive(v_s_1446_);
if (v_isSharedCheck_1466_ == 0)
{
lean_object* v_unused_1467_; 
v_unused_1467_ = lean_ctor_get(v_s_1446_, 1);
lean_dec(v_unused_1467_);
v___x_1460_ = v_s_1446_;
v_isShared_1461_ = v_isSharedCheck_1466_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_stopPos_1458_);
lean_inc(v_str_1457_);
lean_dec(v_s_1446_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1466_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 1, v_stopPos_1450_);
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_str_1457_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v_stopPos_1450_);
lean_ctor_set(v_reuseFailAlloc_1465_, 2, v_stopPos_1458_);
v___x_1463_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
lean_object* v___x_1464_; 
v___x_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1463_);
return v___x_1464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropSuffix_x3f(lean_object* v_s_1468_, lean_object* v_suff_1469_){
_start:
{
lean_object* v_t_1470_; lean_object* v_startPos_1471_; lean_object* v_stopPos_1472_; lean_object* v_startPos_1473_; lean_object* v_stopPos_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; uint8_t v___x_1477_; 
lean_inc_ref(v_suff_1469_);
lean_inc_ref(v_s_1468_);
v_t_1470_ = l_Substring_Raw_commonSuffix(v_s_1468_, v_suff_1469_);
v_startPos_1471_ = lean_ctor_get(v_t_1470_, 1);
lean_inc(v_startPos_1471_);
v_stopPos_1472_ = lean_ctor_get(v_t_1470_, 2);
lean_inc(v_stopPos_1472_);
lean_dec_ref(v_t_1470_);
v_startPos_1473_ = lean_ctor_get(v_suff_1469_, 1);
lean_inc(v_startPos_1473_);
v_stopPos_1474_ = lean_ctor_get(v_suff_1469_, 2);
lean_inc(v_stopPos_1474_);
lean_dec_ref(v_suff_1469_);
v___x_1475_ = lean_nat_sub(v_stopPos_1472_, v_startPos_1471_);
lean_dec(v_stopPos_1472_);
v___x_1476_ = lean_nat_sub(v_stopPos_1474_, v_startPos_1473_);
lean_dec(v_startPos_1473_);
lean_dec(v_stopPos_1474_);
v___x_1477_ = lean_nat_dec_eq(v___x_1475_, v___x_1476_);
lean_dec(v___x_1476_);
lean_dec(v___x_1475_);
if (v___x_1477_ == 0)
{
lean_object* v___x_1478_; 
lean_dec(v_startPos_1471_);
lean_dec_ref(v_s_1468_);
v___x_1478_ = lean_box(0);
return v___x_1478_;
}
else
{
lean_object* v_str_1479_; lean_object* v_startPos_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1488_; 
v_str_1479_ = lean_ctor_get(v_s_1468_, 0);
v_startPos_1480_ = lean_ctor_get(v_s_1468_, 1);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_s_1468_);
if (v_isSharedCheck_1488_ == 0)
{
lean_object* v_unused_1489_; 
v_unused_1489_ = lean_ctor_get(v_s_1468_, 2);
lean_dec(v_unused_1489_);
v___x_1482_ = v_s_1468_;
v_isShared_1483_ = v_isSharedCheck_1488_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_startPos_1480_);
lean_inc(v_str_1479_);
lean_dec(v_s_1468_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1488_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 2, v_startPos_1471_);
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_str_1479_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v_startPos_1480_);
lean_ctor_set(v_reuseFailAlloc_1487_, 2, v_startPos_1471_);
v___x_1485_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
return v___x_1486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg(lean_object* v_x_1490_, lean_object* v_x_1491_, lean_object* v_x_1492_, lean_object* v_h__1_1493_, lean_object* v_h__2_1494_){
_start:
{
lean_object* v_zero_1495_; uint8_t v_isZero_1496_; 
v_zero_1495_ = lean_unsigned_to_nat(0u);
v_isZero_1496_ = lean_nat_dec_eq(v_x_1491_, v_zero_1495_);
if (v_isZero_1496_ == 1)
{
lean_object* v___x_1497_; 
lean_dec(v_h__2_1494_);
v___x_1497_ = lean_apply_2(v_h__1_1493_, v_x_1490_, v_x_1492_);
return v___x_1497_;
}
else
{
lean_object* v_one_1498_; lean_object* v_n_1499_; lean_object* v___x_1500_; 
lean_dec(v_h__1_1493_);
v_one_1498_ = lean_unsigned_to_nat(1u);
v_n_1499_ = lean_nat_sub(v_x_1491_, v_one_1498_);
v___x_1500_ = lean_apply_3(v_h__2_1494_, v_x_1490_, v_n_1499_, v_x_1492_);
return v___x_1500_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg___boxed(lean_object* v_x_1501_, lean_object* v_x_1502_, lean_object* v_x_1503_, lean_object* v_h__1_1504_, lean_object* v_h__2_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg(v_x_1501_, v_x_1502_, v_x_1503_, v_h__1_1504_, v_h__2_1505_);
lean_dec(v_x_1502_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter(lean_object* v_motive_1507_, lean_object* v_x_1508_, lean_object* v_x_1509_, lean_object* v_x_1510_, lean_object* v_h__1_1511_, lean_object* v_h__2_1512_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg(v_x_1508_, v_x_1509_, v_x_1510_, v_h__1_1511_, v_h__2_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___boxed(lean_object* v_motive_1514_, lean_object* v_x_1515_, lean_object* v_x_1516_, lean_object* v_x_1517_, lean_object* v_h__1_1518_, lean_object* v_h__2_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter(v_motive_1514_, v_x_1515_, v_x_1516_, v_x_1517_, v_h__1_1518_, v_h__2_1519_);
lean_dec(v_x_1516_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_Substring_bsize(lean_object* v_a_1521_){
_start:
{
lean_object* v_startPos_1522_; lean_object* v_stopPos_1523_; lean_object* v___x_1524_; 
v_startPos_1522_ = lean_ctor_get(v_a_1521_, 1);
v_stopPos_1523_ = lean_ctor_get(v_a_1521_, 2);
v___x_1524_ = lean_nat_sub(v_stopPos_1523_, v_startPos_1522_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Substring_bsize___boxed(lean_object* v_a_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_Substring_bsize(v_a_1525_);
lean_dec_ref(v_a_1525_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Substring_toString(lean_object* v_a_1527_){
_start:
{
lean_object* v_str_1528_; lean_object* v_startPos_1529_; lean_object* v_stopPos_1530_; lean_object* v___x_1531_; 
v_str_1528_ = lean_ctor_get(v_a_1527_, 0);
v_startPos_1529_ = lean_ctor_get(v_a_1527_, 1);
v_stopPos_1530_ = lean_ctor_get(v_a_1527_, 2);
v___x_1531_ = lean_string_utf8_extract(v_str_1528_, v_startPos_1529_, v_stopPos_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Substring_toString___boxed(lean_object* v_a_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Substring_toString(v_a_1532_);
lean_dec_ref(v_a_1532_);
return v_res_1533_;
}
}
LEAN_EXPORT uint8_t l_Substring_isEmpty(lean_object* v_ss_1534_){
_start:
{
lean_object* v_startPos_1535_; lean_object* v_stopPos_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; uint8_t v___x_1539_; 
v_startPos_1535_ = lean_ctor_get(v_ss_1534_, 1);
v_stopPos_1536_ = lean_ctor_get(v_ss_1534_, 2);
v___x_1537_ = lean_nat_sub(v_stopPos_1536_, v_startPos_1535_);
v___x_1538_ = lean_unsigned_to_nat(0u);
v___x_1539_ = lean_nat_dec_eq(v___x_1537_, v___x_1538_);
lean_dec(v___x_1537_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Substring_isEmpty___boxed(lean_object* v_ss_1540_){
_start:
{
uint8_t v_res_1541_; lean_object* v_r_1542_; 
v_res_1541_ = l_Substring_isEmpty(v_ss_1540_);
lean_dec_ref(v_ss_1540_);
v_r_1542_ = lean_box(v_res_1541_);
return v_r_1542_;
}
}
LEAN_EXPORT lean_object* l_Substring_next(lean_object* v_a_1543_, lean_object* v_a_1544_){
_start:
{
lean_object* v_str_1545_; lean_object* v_startPos_1546_; lean_object* v_stopPos_1547_; lean_object* v_absP_1548_; uint8_t v___x_1549_; 
v_str_1545_ = lean_ctor_get(v_a_1543_, 0);
v_startPos_1546_ = lean_ctor_get(v_a_1543_, 1);
v_stopPos_1547_ = lean_ctor_get(v_a_1543_, 2);
v_absP_1548_ = lean_nat_add(v_startPos_1546_, v_a_1544_);
v___x_1549_ = lean_nat_dec_eq(v_absP_1548_, v_stopPos_1547_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1550_ = lean_string_utf8_next(v_str_1545_, v_absP_1548_);
lean_dec(v_absP_1548_);
v___x_1551_ = lean_nat_sub(v___x_1550_, v_startPos_1546_);
lean_dec(v___x_1550_);
return v___x_1551_;
}
else
{
lean_dec(v_absP_1548_);
lean_inc(v_a_1544_);
return v_a_1544_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_next___boxed(lean_object* v_a_1552_, lean_object* v_a_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Substring_next(v_a_1552_, v_a_1553_);
lean_dec(v_a_1553_);
lean_dec_ref(v_a_1552_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Substring_prev(lean_object* v_a_1555_, lean_object* v_a_1556_){
_start:
{
lean_object* v_str_1557_; lean_object* v_startPos_1558_; lean_object* v_absP_1559_; uint8_t v___x_1560_; 
v_str_1557_ = lean_ctor_get(v_a_1555_, 0);
v_startPos_1558_ = lean_ctor_get(v_a_1555_, 1);
v_absP_1559_ = lean_nat_add(v_startPos_1558_, v_a_1556_);
v___x_1560_ = lean_nat_dec_eq(v_absP_1559_, v_startPos_1558_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = lean_string_utf8_prev(v_str_1557_, v_absP_1559_);
lean_dec(v_absP_1559_);
v___x_1562_ = lean_nat_sub(v___x_1561_, v_startPos_1558_);
lean_dec(v___x_1561_);
return v___x_1562_;
}
else
{
lean_dec(v_absP_1559_);
lean_inc(v_a_1556_);
return v_a_1556_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_prev___boxed(lean_object* v_a_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_Substring_prev(v_a_1563_, v_a_1564_);
lean_dec(v_a_1564_);
lean_dec_ref(v_a_1563_);
return v_res_1565_;
}
}
LEAN_EXPORT uint8_t l_Substring_atEnd(lean_object* v_a_1566_, lean_object* v_a_1567_){
_start:
{
lean_object* v_startPos_1568_; lean_object* v_stopPos_1569_; lean_object* v___x_1570_; uint8_t v___x_1571_; 
v_startPos_1568_ = lean_ctor_get(v_a_1566_, 1);
v_stopPos_1569_ = lean_ctor_get(v_a_1566_, 2);
v___x_1570_ = lean_nat_add(v_startPos_1568_, v_a_1567_);
v___x_1571_ = lean_nat_dec_eq(v___x_1570_, v_stopPos_1569_);
lean_dec(v___x_1570_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Substring_atEnd___boxed(lean_object* v_a_1572_, lean_object* v_a_1573_){
_start:
{
uint8_t v_res_1574_; lean_object* v_r_1575_; 
v_res_1574_ = l_Substring_atEnd(v_a_1572_, v_a_1573_);
lean_dec(v_a_1573_);
lean_dec_ref(v_a_1572_);
v_r_1575_ = lean_box(v_res_1574_);
return v_r_1575_;
}
}
LEAN_EXPORT uint8_t l_Substring_beq(lean_object* v_ss1_1576_, lean_object* v_ss2_1577_){
_start:
{
uint8_t v___x_1578_; 
v___x_1578_ = l_Substring_Raw_beq(v_ss1_1576_, v_ss2_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Substring_beq___boxed(lean_object* v_ss1_1579_, lean_object* v_ss2_1580_){
_start:
{
uint8_t v_res_1581_; lean_object* v_r_1582_; 
v_res_1581_ = l_Substring_beq(v_ss1_1579_, v_ss2_1580_);
v_r_1582_ = lean_box(v_res_1581_);
return v_r_1582_;
}
}
lean_object* runtime_initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_BasicAux(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Substring(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

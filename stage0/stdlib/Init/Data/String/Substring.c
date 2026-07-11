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
uint8_t lean_bool_not(uint8_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_instInhabitedSlice;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_str_109_; lean_object* v_startPos_110_; lean_object* v_absP_111_; uint8_t v___x_112_; 
v_str_109_ = lean_ctor_get(v_x_107_, 0);
v_startPos_110_ = lean_ctor_get(v_x_107_, 1);
v_absP_111_ = lean_nat_add(v_startPos_110_, v_x_108_);
v___x_112_ = lean_nat_dec_eq(v_absP_111_, v_startPos_110_);
if (v___x_112_ == 0)
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
lean_object* v_str_120_; lean_object* v_startPos_121_; lean_object* v_absP_122_; uint8_t v___x_123_; 
v_str_120_ = lean_ctor_get(v_a_118_, 0);
lean_inc_ref(v_str_120_);
v_startPos_121_ = lean_ctor_get(v_a_118_, 1);
lean_inc(v_startPos_121_);
lean_dec_ref(v_a_118_);
v_absP_122_ = lean_nat_add(v_startPos_121_, v_a_119_);
v___x_123_ = lean_nat_dec_eq(v_absP_122_, v_startPos_121_);
if (v___x_123_ == 0)
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
lean_object* v_str_131_; lean_object* v_startPos_132_; lean_object* v_stopPos_133_; lean_object* v_one_134_; lean_object* v_n_135_; lean_object* v_absP_136_; uint8_t v___x_137_; 
v_str_131_ = lean_ctor_get(v_x_126_, 0);
v_startPos_132_ = lean_ctor_get(v_x_126_, 1);
v_stopPos_133_ = lean_ctor_get(v_x_126_, 2);
v_one_134_ = lean_unsigned_to_nat(1u);
v_n_135_ = lean_nat_sub(v_x_127_, v_one_134_);
lean_dec(v_x_127_);
v_absP_136_ = lean_nat_add(v_startPos_132_, v_x_128_);
v___x_137_ = lean_nat_dec_eq(v_absP_136_, v_stopPos_133_);
if (v___x_137_ == 0)
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
lean_object* v_str_151_; lean_object* v_startPos_152_; lean_object* v_one_153_; lean_object* v_n_154_; lean_object* v_absP_155_; uint8_t v___x_156_; 
v_str_151_ = lean_ctor_get(v_x_146_, 0);
v_startPos_152_ = lean_ctor_get(v_x_146_, 1);
v_one_153_ = lean_unsigned_to_nat(1u);
v_n_154_ = lean_nat_sub(v_x_147_, v_one_153_);
lean_dec(v_x_147_);
v_absP_155_ = lean_nat_add(v_startPos_152_, v_x_148_);
v___x_156_ = lean_nat_dec_eq(v_absP_155_, v_startPos_152_);
if (v___x_156_ == 0)
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
lean_object* v___x_188_; uint8_t v___x_189_; 
v___x_188_ = lean_nat_sub(v_stopPos_179_, v_startPos_180_);
v___x_189_ = lean_nat_dec_eq(v_it_184_, v___x_188_);
lean_dec(v___x_188_);
if (v___x_189_ == 0)
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
lean_object* v_startPos_321_; lean_object* v_stopPos_322_; lean_object* v___x_323_; uint8_t v___x_324_; 
v_startPos_321_ = lean_ctor_get(v_x_319_, 1);
v_stopPos_322_ = lean_ctor_get(v_x_319_, 2);
v___x_323_ = lean_nat_add(v_startPos_321_, v_x_320_);
v___x_324_ = lean_nat_dec_eq(v___x_323_, v_stopPos_322_);
lean_dec(v___x_323_);
return v___x_324_;
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
static lean_object* _init_l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__0(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = ((lean_object*)(l_Substring_Raw_extract___closed__0));
v___x_386_ = lean_string_utf8_byte_size(v___x_385_);
return v___x_386_;
}
}
static lean_object* _init_l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__1(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_387_ = lean_obj_once(&l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__0, &l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__0_once, _init_l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__0);
v___x_388_ = lean_unsigned_to_nat(0u);
v___x_389_ = ((lean_object*)(l_Substring_Raw_extract___closed__0));
v___x_390_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set(v___x_390_, 1, v___x_388_);
lean_ctor_set(v___x_390_, 2, v___x_387_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop(lean_object* v_s_391_, lean_object* v_sep_392_, lean_object* v_b_393_, lean_object* v_i_394_, lean_object* v_j_395_, lean_object* v_r_396_){
_start:
{
lean_object* v___y_398_; lean_object* v___y_402_; lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___y_408_; lean_object* v_str_411_; lean_object* v_startPos_412_; lean_object* v_stopPos_413_; lean_object* v___y_415_; lean_object* v___y_416_; lean_object* v___y_417_; lean_object* v___y_418_; lean_object* v___y_424_; lean_object* v___y_435_; lean_object* v___x_440_; uint8_t v___x_441_; 
v_str_411_ = lean_ctor_get(v_s_391_, 0);
v_startPos_412_ = lean_ctor_get(v_s_391_, 1);
v_stopPos_413_ = lean_ctor_get(v_s_391_, 2);
v___x_440_ = lean_nat_sub(v_stopPos_413_, v_startPos_412_);
v___x_441_ = lean_nat_dec_lt(v_i_394_, v___x_440_);
lean_dec(v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_471_; 
lean_inc(v_stopPos_413_);
lean_inc(v_startPos_412_);
lean_inc_ref(v_str_411_);
v_isSharedCheck_471_ = !lean_is_exclusive(v_s_391_);
if (v_isSharedCheck_471_ == 0)
{
lean_object* v_unused_472_; lean_object* v_unused_473_; lean_object* v_unused_474_; 
v_unused_472_ = lean_ctor_get(v_s_391_, 2);
lean_dec(v_unused_472_);
v_unused_473_ = lean_ctor_get(v_s_391_, 1);
lean_dec(v_unused_473_);
v_unused_474_ = lean_ctor_get(v_s_391_, 0);
lean_dec(v_unused_474_);
v___x_443_ = v_s_391_;
v_isShared_444_ = v_isSharedCheck_471_;
goto v_resetjp_442_;
}
else
{
lean_dec(v_s_391_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_471_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
uint8_t v___x_445_; 
v___x_445_ = lean_string_utf8_at_end(v_sep_392_, v_j_395_);
if (v___x_445_ == 0)
{
uint8_t v___x_446_; 
lean_del_object(v___x_443_);
lean_dec(v_j_395_);
v___x_446_ = lean_nat_dec_le(v_i_394_, v_b_393_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_447_ = lean_nat_add(v_startPos_412_, v_b_393_);
lean_dec(v_b_393_);
v___x_448_ = lean_nat_dec_le(v_stopPos_413_, v___x_447_);
if (v___x_448_ == 0)
{
v___y_435_ = v___x_447_;
goto v___jp_434_;
}
else
{
lean_dec(v___x_447_);
lean_inc(v_stopPos_413_);
v___y_435_ = v_stopPos_413_;
goto v___jp_434_;
}
}
else
{
lean_object* v___x_449_; 
lean_dec(v_stopPos_413_);
lean_dec(v_startPos_412_);
lean_dec_ref(v_str_411_);
lean_dec(v_i_394_);
lean_dec(v_b_393_);
v___x_449_ = ((lean_object*)(l_Substring_Raw_extract___closed__1));
v___y_398_ = v___x_449_;
goto v___jp_397_;
}
}
else
{
lean_object* v___x_450_; lean_object* v___y_452_; lean_object* v___x_456_; lean_object* v___y_458_; uint8_t v___x_467_; 
v___x_450_ = lean_obj_once(&l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__1, &l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__1_once, _init_l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__1);
v___x_456_ = lean_nat_sub(v_i_394_, v_j_395_);
lean_dec(v_j_395_);
lean_dec(v_i_394_);
v___x_467_ = lean_nat_dec_le(v___x_456_, v_b_393_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_468_ = lean_nat_add(v_startPos_412_, v_b_393_);
lean_dec(v_b_393_);
v___x_469_ = lean_nat_dec_le(v_stopPos_413_, v___x_468_);
if (v___x_469_ == 0)
{
v___y_458_ = v___x_468_;
goto v___jp_457_;
}
else
{
lean_dec(v___x_468_);
lean_inc(v_stopPos_413_);
v___y_458_ = v_stopPos_413_;
goto v___jp_457_;
}
}
else
{
lean_object* v___x_470_; 
lean_dec(v___x_456_);
lean_del_object(v___x_443_);
lean_dec(v_stopPos_413_);
lean_dec(v_startPos_412_);
lean_dec_ref(v_str_411_);
lean_dec(v_b_393_);
v___x_470_ = ((lean_object*)(l_Substring_Raw_extract___closed__1));
v___y_452_ = v___x_470_;
goto v___jp_451_;
}
v___jp_451_:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_453_, 0, v___y_452_);
lean_ctor_set(v___x_453_, 1, v_r_396_);
v___x_454_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_450_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = l_List_reverse___redArg(v___x_454_);
return v___x_455_;
}
v___jp_457_:
{
lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_459_ = lean_nat_add(v_startPos_412_, v___x_456_);
lean_dec(v___x_456_);
lean_dec(v_startPos_412_);
v___x_460_ = lean_nat_dec_le(v_stopPos_413_, v___x_459_);
if (v___x_460_ == 0)
{
lean_object* v___x_462_; 
lean_dec(v_stopPos_413_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 2, v___x_459_);
lean_ctor_set(v___x_443_, 1, v___y_458_);
v___x_462_ = v___x_443_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_str_411_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v___y_458_);
lean_ctor_set(v_reuseFailAlloc_463_, 2, v___x_459_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
v___y_452_ = v___x_462_;
goto v___jp_451_;
}
}
else
{
lean_object* v___x_465_; 
lean_dec(v___x_459_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 1, v___y_458_);
v___x_465_ = v___x_443_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_str_411_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v___y_458_);
lean_ctor_set(v_reuseFailAlloc_466_, 2, v_stopPos_413_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
v___y_452_ = v___x_465_;
goto v___jp_451_;
}
}
}
}
}
}
else
{
lean_object* v___x_475_; uint32_t v___x_476_; uint32_t v___x_477_; uint8_t v___x_478_; 
v___x_475_ = lean_nat_add(v_startPos_412_, v_i_394_);
v___x_476_ = lean_string_utf8_get(v_str_411_, v___x_475_);
v___x_477_ = lean_string_utf8_get(v_sep_392_, v_j_395_);
v___x_478_ = lean_uint32_dec_eq(v___x_476_, v___x_477_);
if (v___x_478_ == 0)
{
uint8_t v___x_479_; 
lean_dec(v_j_395_);
v___x_479_ = lean_nat_dec_eq(v___x_475_, v_stopPos_413_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; lean_object* v___x_481_; 
lean_dec(v_i_394_);
v___x_480_ = lean_string_utf8_next(v_str_411_, v___x_475_);
lean_dec(v___x_475_);
v___x_481_ = lean_nat_sub(v___x_480_, v_startPos_412_);
lean_dec(v___x_480_);
v___y_402_ = v___x_481_;
goto v___jp_401_;
}
else
{
lean_dec(v___x_475_);
v___y_402_ = v_i_394_;
goto v___jp_401_;
}
}
else
{
uint8_t v___x_482_; 
v___x_482_ = lean_nat_dec_eq(v___x_475_, v_stopPos_413_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_484_; 
lean_dec(v_i_394_);
v___x_483_ = lean_string_utf8_next(v_str_411_, v___x_475_);
lean_dec(v___x_475_);
v___x_484_ = lean_nat_sub(v___x_483_, v_startPos_412_);
lean_dec(v___x_483_);
v___y_424_ = v___x_484_;
goto v___jp_423_;
}
else
{
lean_dec(v___x_475_);
v___y_424_ = v_i_394_;
goto v___jp_423_;
}
}
}
v___jp_397_:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_399_, 0, v___y_398_);
lean_ctor_set(v___x_399_, 1, v_r_396_);
v___x_400_ = l_List_reverse___redArg(v___x_399_);
return v___x_400_;
}
v___jp_401_:
{
lean_object* v___x_403_; 
v___x_403_ = lean_unsigned_to_nat(0u);
v_i_394_ = v___y_402_;
v_j_395_ = v___x_403_;
goto _start;
}
v___jp_405_:
{
lean_object* v___x_409_; 
v___x_409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_409_, 0, v___y_408_);
lean_ctor_set(v___x_409_, 1, v_r_396_);
lean_inc(v___y_406_);
v_b_393_ = v___y_406_;
v_i_394_ = v___y_406_;
v_j_395_ = v___y_407_;
v_r_396_ = v___x_409_;
goto _start;
}
v___jp_414_:
{
lean_object* v___x_419_; uint8_t v___x_420_; 
v___x_419_ = lean_nat_add(v_startPos_412_, v___y_417_);
lean_dec(v___y_417_);
v___x_420_ = lean_nat_dec_le(v_stopPos_413_, v___x_419_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; 
lean_inc_ref(v_str_411_);
v___x_421_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_421_, 0, v_str_411_);
lean_ctor_set(v___x_421_, 1, v___y_418_);
lean_ctor_set(v___x_421_, 2, v___x_419_);
v___y_406_ = v___y_415_;
v___y_407_ = v___y_416_;
v___y_408_ = v___x_421_;
goto v___jp_405_;
}
else
{
lean_object* v___x_422_; 
lean_dec(v___x_419_);
lean_inc(v_stopPos_413_);
lean_inc_ref(v_str_411_);
v___x_422_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_422_, 0, v_str_411_);
lean_ctor_set(v___x_422_, 1, v___y_418_);
lean_ctor_set(v___x_422_, 2, v_stopPos_413_);
v___y_406_ = v___y_415_;
v___y_407_ = v___y_416_;
v___y_408_ = v___x_422_;
goto v___jp_405_;
}
}
v___jp_423_:
{
lean_object* v_j_425_; uint8_t v___x_426_; 
v_j_425_ = lean_string_utf8_next(v_sep_392_, v_j_395_);
lean_dec(v_j_395_);
v___x_426_ = lean_string_utf8_at_end(v_sep_392_, v_j_425_);
if (v___x_426_ == 0)
{
v_i_394_ = v___y_424_;
v_j_395_ = v_j_425_;
goto _start;
}
else
{
lean_object* v___x_428_; lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_428_ = lean_unsigned_to_nat(0u);
v___x_429_ = lean_nat_sub(v___y_424_, v_j_425_);
lean_dec(v_j_425_);
v___x_430_ = lean_nat_dec_le(v___x_429_, v_b_393_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_431_ = lean_nat_add(v_startPos_412_, v_b_393_);
lean_dec(v_b_393_);
v___x_432_ = lean_nat_dec_le(v_stopPos_413_, v___x_431_);
if (v___x_432_ == 0)
{
v___y_415_ = v___y_424_;
v___y_416_ = v___x_428_;
v___y_417_ = v___x_429_;
v___y_418_ = v___x_431_;
goto v___jp_414_;
}
else
{
lean_dec(v___x_431_);
lean_inc(v_stopPos_413_);
v___y_415_ = v___y_424_;
v___y_416_ = v___x_428_;
v___y_417_ = v___x_429_;
v___y_418_ = v_stopPos_413_;
goto v___jp_414_;
}
}
else
{
lean_object* v___x_433_; 
lean_dec(v___x_429_);
lean_dec(v_b_393_);
v___x_433_ = ((lean_object*)(l_Substring_Raw_extract___closed__1));
v___y_406_ = v___y_424_;
v___y_407_ = v___x_428_;
v___y_408_ = v___x_433_;
goto v___jp_405_;
}
}
}
v___jp_434_:
{
lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_436_ = lean_nat_add(v_startPos_412_, v_i_394_);
lean_dec(v_i_394_);
lean_dec(v_startPos_412_);
v___x_437_ = lean_nat_dec_le(v_stopPos_413_, v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; 
lean_dec(v_stopPos_413_);
v___x_438_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_438_, 0, v_str_411_);
lean_ctor_set(v___x_438_, 1, v___y_435_);
lean_ctor_set(v___x_438_, 2, v___x_436_);
v___y_398_ = v___x_438_;
goto v___jp_397_;
}
else
{
lean_object* v___x_439_; 
lean_dec(v___x_436_);
v___x_439_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_439_, 0, v_str_411_);
lean_ctor_set(v___x_439_, 1, v___y_435_);
lean_ctor_set(v___x_439_, 2, v_stopPos_413_);
v___y_398_ = v___x_439_;
goto v___jp_397_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___boxed(lean_object* v_s_485_, lean_object* v_sep_486_, lean_object* v_b_487_, lean_object* v_i_488_, lean_object* v_j_489_, lean_object* v_r_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop(v_s_485_, v_sep_486_, v_b_487_, v_i_488_, v_j_489_, v_r_490_);
lean_dec_ref(v_sep_486_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_splitOn(lean_object* v_s_492_, lean_object* v_sep_493_){
_start:
{
lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_494_ = ((lean_object*)(l_Substring_Raw_extract___closed__0));
v___x_495_ = lean_string_dec_eq(v_sep_493_, v___x_494_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_496_ = lean_unsigned_to_nat(0u);
v___x_497_ = lean_box(0);
v___x_498_ = l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop(v_s_492_, v_sep_493_, v___x_496_, v___x_496_, v___x_496_, v___x_497_);
return v___x_498_;
}
else
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_box(0);
v___x_500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_500_, 0, v_s_492_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
return v___x_500_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_splitOn___boxed(lean_object* v_s_501_, lean_object* v_sep_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Substring_Raw_splitOn(v_s_501_, v_sep_502_);
lean_dec_ref(v_sep_502_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldl___redArg___lam__0(lean_object* v___y_504_, lean_object* v_f_505_, lean_object* v_it_506_, lean_object* v_acc_507_, lean_object* v_hP_508_, lean_object* v_recur_509_){
_start:
{
lean_object* v_str_510_; lean_object* v_startInclusive_511_; lean_object* v_endExclusive_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v_str_510_ = lean_ctor_get(v___y_504_, 0);
v_startInclusive_511_ = lean_ctor_get(v___y_504_, 1);
v_endExclusive_512_ = lean_ctor_get(v___y_504_, 2);
v___x_513_ = lean_nat_sub(v_endExclusive_512_, v_startInclusive_511_);
v___x_514_ = lean_nat_dec_eq(v_it_506_, v___x_513_);
lean_dec(v___x_513_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; uint32_t v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_515_ = lean_nat_add(v_startInclusive_511_, v_it_506_);
v___x_516_ = lean_string_utf8_next_fast(v_str_510_, v___x_515_);
v___x_517_ = lean_nat_sub(v___x_516_, v_startInclusive_511_);
v___x_518_ = lean_string_utf8_get_fast(v_str_510_, v___x_515_);
lean_dec(v___x_515_);
v___x_519_ = lean_box_uint32(v___x_518_);
v___x_520_ = lean_apply_2(v_f_505_, v_acc_507_, v___x_519_);
v___x_521_ = lean_apply_4(v_recur_509_, v___x_517_, v___x_520_, lean_box(0), lean_box(0));
return v___x_521_;
}
else
{
lean_dec(v_recur_509_);
lean_dec(v_f_505_);
return v_acc_507_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldl___redArg___lam__0___boxed(lean_object* v___y_522_, lean_object* v_f_523_, lean_object* v_it_524_, lean_object* v_acc_525_, lean_object* v_hP_526_, lean_object* v_recur_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Substring_Raw_foldl___redArg___lam__0(v___y_522_, v_f_523_, v_it_524_, v_acc_525_, v_hP_526_, v_recur_527_);
lean_dec(v_it_524_);
lean_dec_ref(v___y_522_);
return v_res_528_;
}
}
static lean_object* _init_l_Substring_Raw_foldl___redArg___closed__3(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_532_ = ((lean_object*)(l_Substring_Raw_foldl___redArg___closed__2));
v___x_533_ = lean_unsigned_to_nat(14u);
v___x_534_ = lean_unsigned_to_nat(22u);
v___x_535_ = ((lean_object*)(l_Substring_Raw_foldl___redArg___closed__1));
v___x_536_ = ((lean_object*)(l_Substring_Raw_foldl___redArg___closed__0));
v___x_537_ = l_mkPanicMessageWithDecl(v___x_536_, v___x_535_, v___x_534_, v___x_533_, v___x_532_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldl___redArg(lean_object* v_f_538_, lean_object* v_init_539_, lean_object* v_s_540_){
_start:
{
lean_object* v___y_542_; lean_object* v_str_546_; lean_object* v_startPos_547_; lean_object* v_stopPos_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_562_; 
v_str_546_ = lean_ctor_get(v_s_540_, 0);
v_startPos_547_ = lean_ctor_get(v_s_540_, 1);
v_stopPos_548_ = lean_ctor_get(v_s_540_, 2);
v_isSharedCheck_562_ = !lean_is_exclusive(v_s_540_);
if (v_isSharedCheck_562_ == 0)
{
v___x_550_ = v_s_540_;
v_isShared_551_ = v_isSharedCheck_562_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_stopPos_548_);
lean_inc(v_startPos_547_);
lean_inc(v_str_546_);
lean_dec(v_s_540_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_562_;
goto v_resetjp_549_;
}
v___jp_541_:
{
lean_object* v___f_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
lean_inc_ref(v___y_542_);
v___f_543_ = lean_alloc_closure((void*)(l_Substring_Raw_foldl___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_543_, 0, v___y_542_);
lean_closure_set(v___f_543_, 1, v_f_538_);
v___x_544_ = l_String_Slice_positions(v___y_542_);
lean_dec_ref(v___y_542_);
v___x_545_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_543_, v___x_544_, v_init_539_, lean_box(0));
return v___x_545_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; uint8_t v___x_556_; 
v___x_552_ = l_String_instInhabitedSlice;
v___x_556_ = lean_string_is_valid_pos(v_str_546_, v_startPos_547_);
if (v___x_556_ == 0)
{
lean_del_object(v___x_550_);
lean_dec(v_stopPos_548_);
lean_dec(v_startPos_547_);
lean_dec_ref(v_str_546_);
goto v___jp_553_;
}
else
{
uint8_t v___x_557_; 
v___x_557_ = lean_string_is_valid_pos(v_str_546_, v_stopPos_548_);
if (v___x_557_ == 0)
{
lean_del_object(v___x_550_);
lean_dec(v_stopPos_548_);
lean_dec(v_startPos_547_);
lean_dec_ref(v_str_546_);
goto v___jp_553_;
}
else
{
uint8_t v___x_558_; 
v___x_558_ = lean_nat_dec_le(v_startPos_547_, v_stopPos_548_);
if (v___x_558_ == 0)
{
lean_del_object(v___x_550_);
lean_dec(v_stopPos_548_);
lean_dec(v_startPos_547_);
lean_dec_ref(v_str_546_);
goto v___jp_553_;
}
else
{
lean_object* v___x_560_; 
if (v_isShared_551_ == 0)
{
v___x_560_ = v___x_550_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_str_546_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_startPos_547_);
lean_ctor_set(v_reuseFailAlloc_561_, 2, v_stopPos_548_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
v___y_542_ = v___x_560_;
goto v___jp_541_;
}
}
}
}
v___jp_553_:
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_555_ = l_panic___redArg(v___x_552_, v___x_554_);
v___y_542_ = v___x_555_;
goto v___jp_541_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldl(lean_object* v_00_u03b1_563_, lean_object* v_f_564_, lean_object* v_init_565_, lean_object* v_s_566_){
_start:
{
lean_object* v___y_568_; lean_object* v_str_572_; lean_object* v_startPos_573_; lean_object* v_stopPos_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_588_; 
v_str_572_ = lean_ctor_get(v_s_566_, 0);
v_startPos_573_ = lean_ctor_get(v_s_566_, 1);
v_stopPos_574_ = lean_ctor_get(v_s_566_, 2);
v_isSharedCheck_588_ = !lean_is_exclusive(v_s_566_);
if (v_isSharedCheck_588_ == 0)
{
v___x_576_ = v_s_566_;
v_isShared_577_ = v_isSharedCheck_588_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_stopPos_574_);
lean_inc(v_startPos_573_);
lean_inc(v_str_572_);
lean_dec(v_s_566_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_588_;
goto v_resetjp_575_;
}
v___jp_567_:
{
lean_object* v___f_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
lean_inc_ref(v___y_568_);
v___f_569_ = lean_alloc_closure((void*)(l_Substring_Raw_foldl___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_569_, 0, v___y_568_);
lean_closure_set(v___f_569_, 1, v_f_564_);
v___x_570_ = l_String_Slice_positions(v___y_568_);
lean_dec_ref(v___y_568_);
v___x_571_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_569_, v___x_570_, v_init_565_, lean_box(0));
return v___x_571_;
}
v_resetjp_575_:
{
lean_object* v___x_578_; uint8_t v___x_582_; 
v___x_578_ = l_String_instInhabitedSlice;
v___x_582_ = lean_string_is_valid_pos(v_str_572_, v_startPos_573_);
if (v___x_582_ == 0)
{
lean_del_object(v___x_576_);
lean_dec(v_stopPos_574_);
lean_dec(v_startPos_573_);
lean_dec_ref(v_str_572_);
goto v___jp_579_;
}
else
{
uint8_t v___x_583_; 
v___x_583_ = lean_string_is_valid_pos(v_str_572_, v_stopPos_574_);
if (v___x_583_ == 0)
{
lean_del_object(v___x_576_);
lean_dec(v_stopPos_574_);
lean_dec(v_startPos_573_);
lean_dec_ref(v_str_572_);
goto v___jp_579_;
}
else
{
uint8_t v___x_584_; 
v___x_584_ = lean_nat_dec_le(v_startPos_573_, v_stopPos_574_);
if (v___x_584_ == 0)
{
lean_del_object(v___x_576_);
lean_dec(v_stopPos_574_);
lean_dec(v_startPos_573_);
lean_dec_ref(v_str_572_);
goto v___jp_579_;
}
else
{
lean_object* v___x_586_; 
if (v_isShared_577_ == 0)
{
v___x_586_ = v___x_576_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_str_572_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_startPos_573_);
lean_ctor_set(v_reuseFailAlloc_587_, 2, v_stopPos_574_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
v___y_568_ = v___x_586_;
goto v___jp_567_;
}
}
}
}
v___jp_579_:
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_581_ = l_panic___redArg(v___x_578_, v___x_580_);
v___y_568_ = v___x_581_;
goto v___jp_567_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr___redArg___lam__0(lean_object* v___y_589_, lean_object* v_f_590_, lean_object* v_it_591_, lean_object* v_acc_592_, lean_object* v_hP_593_, lean_object* v_recur_594_){
_start:
{
lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_595_ = lean_unsigned_to_nat(0u);
v___x_596_ = lean_nat_dec_eq(v_it_591_, v___x_595_);
if (v___x_596_ == 0)
{
lean_object* v_str_597_; lean_object* v_startInclusive_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v_prevPos_601_; lean_object* v___x_602_; uint32_t v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v_str_597_ = lean_ctor_get(v___y_589_, 0);
v_startInclusive_598_ = lean_ctor_get(v___y_589_, 1);
v___x_599_ = lean_unsigned_to_nat(1u);
v___x_600_ = lean_nat_sub(v_it_591_, v___x_599_);
v_prevPos_601_ = l_String_Slice_posLE(v___y_589_, v___x_600_);
v___x_602_ = lean_nat_add(v_startInclusive_598_, v_prevPos_601_);
v___x_603_ = lean_string_utf8_get_fast(v_str_597_, v___x_602_);
lean_dec(v___x_602_);
v___x_604_ = lean_box_uint32(v___x_603_);
v___x_605_ = lean_apply_2(v_f_590_, v___x_604_, v_acc_592_);
v___x_606_ = lean_apply_4(v_recur_594_, v_prevPos_601_, v___x_605_, lean_box(0), lean_box(0));
return v___x_606_;
}
else
{
lean_dec(v_recur_594_);
lean_dec(v_f_590_);
return v_acc_592_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr___redArg___lam__0___boxed(lean_object* v___y_607_, lean_object* v_f_608_, lean_object* v_it_609_, lean_object* v_acc_610_, lean_object* v_hP_611_, lean_object* v_recur_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Substring_Raw_foldr___redArg___lam__0(v___y_607_, v_f_608_, v_it_609_, v_acc_610_, v_hP_611_, v_recur_612_);
lean_dec(v_it_609_);
lean_dec_ref(v___y_607_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr___redArg(lean_object* v_f_614_, lean_object* v_init_615_, lean_object* v_s_616_){
_start:
{
lean_object* v___y_618_; lean_object* v_str_622_; lean_object* v_startPos_623_; lean_object* v_stopPos_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_638_; 
v_str_622_ = lean_ctor_get(v_s_616_, 0);
v_startPos_623_ = lean_ctor_get(v_s_616_, 1);
v_stopPos_624_ = lean_ctor_get(v_s_616_, 2);
v_isSharedCheck_638_ = !lean_is_exclusive(v_s_616_);
if (v_isSharedCheck_638_ == 0)
{
v___x_626_ = v_s_616_;
v_isShared_627_ = v_isSharedCheck_638_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_stopPos_624_);
lean_inc(v_startPos_623_);
lean_inc(v_str_622_);
lean_dec(v_s_616_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_638_;
goto v_resetjp_625_;
}
v___jp_617_:
{
lean_object* v___f_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
lean_inc_ref(v___y_618_);
v___f_619_ = lean_alloc_closure((void*)(l_Substring_Raw_foldr___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_619_, 0, v___y_618_);
lean_closure_set(v___f_619_, 1, v_f_614_);
v___x_620_ = l_String_Slice_revPositions(v___y_618_);
lean_dec_ref(v___y_618_);
v___x_621_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_619_, v___x_620_, v_init_615_, lean_box(0));
return v___x_621_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; uint8_t v___x_632_; 
v___x_628_ = l_String_instInhabitedSlice;
v___x_632_ = lean_string_is_valid_pos(v_str_622_, v_startPos_623_);
if (v___x_632_ == 0)
{
lean_del_object(v___x_626_);
lean_dec(v_stopPos_624_);
lean_dec(v_startPos_623_);
lean_dec_ref(v_str_622_);
goto v___jp_629_;
}
else
{
uint8_t v___x_633_; 
v___x_633_ = lean_string_is_valid_pos(v_str_622_, v_stopPos_624_);
if (v___x_633_ == 0)
{
lean_del_object(v___x_626_);
lean_dec(v_stopPos_624_);
lean_dec(v_startPos_623_);
lean_dec_ref(v_str_622_);
goto v___jp_629_;
}
else
{
uint8_t v___x_634_; 
v___x_634_ = lean_nat_dec_le(v_startPos_623_, v_stopPos_624_);
if (v___x_634_ == 0)
{
lean_del_object(v___x_626_);
lean_dec(v_stopPos_624_);
lean_dec(v_startPos_623_);
lean_dec_ref(v_str_622_);
goto v___jp_629_;
}
else
{
lean_object* v___x_636_; 
if (v_isShared_627_ == 0)
{
v___x_636_ = v___x_626_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_str_622_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_startPos_623_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v_stopPos_624_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
v___y_618_ = v___x_636_;
goto v___jp_617_;
}
}
}
}
v___jp_629_:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_631_ = l_panic___redArg(v___x_628_, v___x_630_);
v___y_618_ = v___x_631_;
goto v___jp_617_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr(lean_object* v_00_u03b1_639_, lean_object* v_f_640_, lean_object* v_init_641_, lean_object* v_s_642_){
_start:
{
lean_object* v___y_644_; lean_object* v_str_648_; lean_object* v_startPos_649_; lean_object* v_stopPos_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_664_; 
v_str_648_ = lean_ctor_get(v_s_642_, 0);
v_startPos_649_ = lean_ctor_get(v_s_642_, 1);
v_stopPos_650_ = lean_ctor_get(v_s_642_, 2);
v_isSharedCheck_664_ = !lean_is_exclusive(v_s_642_);
if (v_isSharedCheck_664_ == 0)
{
v___x_652_ = v_s_642_;
v_isShared_653_ = v_isSharedCheck_664_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_stopPos_650_);
lean_inc(v_startPos_649_);
lean_inc(v_str_648_);
lean_dec(v_s_642_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_664_;
goto v_resetjp_651_;
}
v___jp_643_:
{
lean_object* v___f_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
lean_inc_ref(v___y_644_);
v___f_645_ = lean_alloc_closure((void*)(l_Substring_Raw_foldr___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_645_, 0, v___y_644_);
lean_closure_set(v___f_645_, 1, v_f_640_);
v___x_646_ = l_String_Slice_revPositions(v___y_644_);
lean_dec_ref(v___y_644_);
v___x_647_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_645_, v___x_646_, v_init_641_, lean_box(0));
return v___x_647_;
}
v_resetjp_651_:
{
lean_object* v___x_654_; uint8_t v___x_658_; 
v___x_654_ = l_String_instInhabitedSlice;
v___x_658_ = lean_string_is_valid_pos(v_str_648_, v_startPos_649_);
if (v___x_658_ == 0)
{
lean_del_object(v___x_652_);
lean_dec(v_stopPos_650_);
lean_dec(v_startPos_649_);
lean_dec_ref(v_str_648_);
goto v___jp_655_;
}
else
{
uint8_t v___x_659_; 
v___x_659_ = lean_string_is_valid_pos(v_str_648_, v_stopPos_650_);
if (v___x_659_ == 0)
{
lean_del_object(v___x_652_);
lean_dec(v_stopPos_650_);
lean_dec(v_startPos_649_);
lean_dec_ref(v_str_648_);
goto v___jp_655_;
}
else
{
uint8_t v___x_660_; 
v___x_660_ = lean_nat_dec_le(v_startPos_649_, v_stopPos_650_);
if (v___x_660_ == 0)
{
lean_del_object(v___x_652_);
lean_dec(v_stopPos_650_);
lean_dec(v_startPos_649_);
lean_dec_ref(v_str_648_);
goto v___jp_655_;
}
else
{
lean_object* v___x_662_; 
if (v_isShared_653_ == 0)
{
v___x_662_ = v___x_652_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_str_648_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v_startPos_649_);
lean_ctor_set(v_reuseFailAlloc_663_, 2, v_stopPos_650_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
v___y_644_ = v___x_662_;
goto v___jp_643_;
}
}
}
}
v___jp_655_:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_657_ = l_panic___redArg(v___x_654_, v___x_656_);
v___y_644_ = v___x_657_;
goto v___jp_643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_any___lam__0(lean_object* v___x_665_, lean_object* v_s_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(v_s_666_, v___x_665_, v___y_667_, lean_box(0), lean_box(0), v___y_670_, v___y_671_, v___y_672_);
return v___x_673_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_any(lean_object* v_s_674_, lean_object* v_p_675_){
_start:
{
lean_object* v___x_676_; lean_object* v_str_677_; lean_object* v_startPos_678_; lean_object* v_stopPos_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_697_; 
lean_inc_ref(v_p_675_);
v___x_676_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v_p_675_);
v_str_677_ = lean_ctor_get(v_s_674_, 0);
v_startPos_678_ = lean_ctor_get(v_s_674_, 1);
v_stopPos_679_ = lean_ctor_get(v_s_674_, 2);
v_isSharedCheck_697_ = !lean_is_exclusive(v_s_674_);
if (v_isSharedCheck_697_ == 0)
{
v___x_681_ = v_s_674_;
v_isShared_682_ = v_isSharedCheck_697_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_stopPos_679_);
lean_inc(v_startPos_678_);
lean_inc(v_str_677_);
lean_dec(v_s_674_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_697_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; lean_object* v___f_684_; lean_object* v___x_685_; uint8_t v___x_690_; 
v___x_683_ = l_String_instInhabitedSlice;
v___f_684_ = lean_alloc_closure((void*)(l_Substring_Raw_any___lam__0), 8, 1);
lean_closure_set(v___f_684_, 0, v___x_676_);
v___x_685_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_685_, 0, lean_box(0));
lean_closure_set(v___x_685_, 1, v_p_675_);
v___x_690_ = lean_string_is_valid_pos(v_str_677_, v_startPos_678_);
if (v___x_690_ == 0)
{
lean_del_object(v___x_681_);
lean_dec(v_stopPos_679_);
lean_dec(v_startPos_678_);
lean_dec_ref(v_str_677_);
goto v___jp_686_;
}
else
{
uint8_t v___x_691_; 
v___x_691_ = lean_string_is_valid_pos(v_str_677_, v_stopPos_679_);
if (v___x_691_ == 0)
{
lean_del_object(v___x_681_);
lean_dec(v_stopPos_679_);
lean_dec(v_startPos_678_);
lean_dec_ref(v_str_677_);
goto v___jp_686_;
}
else
{
uint8_t v___x_692_; 
v___x_692_ = lean_nat_dec_le(v_startPos_678_, v_stopPos_679_);
if (v___x_692_ == 0)
{
lean_del_object(v___x_681_);
lean_dec(v_stopPos_679_);
lean_dec(v_startPos_678_);
lean_dec_ref(v_str_677_);
goto v___jp_686_;
}
else
{
lean_object* v___x_694_; 
if (v_isShared_682_ == 0)
{
v___x_694_ = v___x_681_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_str_677_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v_startPos_678_);
lean_ctor_set(v_reuseFailAlloc_696_, 2, v_stopPos_679_);
v___x_694_ = v_reuseFailAlloc_696_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
uint8_t v___x_695_; 
v___x_695_ = l_String_Slice_contains___redArg(v___f_684_, v___x_694_, v___x_685_);
return v___x_695_;
}
}
}
}
v___jp_686_:
{
lean_object* v___x_687_; lean_object* v___x_688_; uint8_t v___x_689_; 
v___x_687_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_688_ = l_panic___redArg(v___x_683_, v___x_687_);
v___x_689_ = l_String_Slice_contains___redArg(v___f_684_, v___x_688_, v___x_685_);
return v___x_689_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_any___boxed(lean_object* v_s_698_, lean_object* v_p_699_){
_start:
{
uint8_t v_res_700_; lean_object* v_r_701_; 
v_res_700_ = l_Substring_Raw_any(v_s_698_, v_p_699_);
v_r_701_ = lean_box(v_res_700_);
return v_r_701_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_all(lean_object* v_s_702_, lean_object* v_p_703_){
_start:
{
lean_object* v___y_705_; lean_object* v_startInclusive_706_; lean_object* v_endExclusive_707_; lean_object* v_str_713_; lean_object* v_startPos_714_; lean_object* v_stopPos_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_731_; 
v_str_713_ = lean_ctor_get(v_s_702_, 0);
v_startPos_714_ = lean_ctor_get(v_s_702_, 1);
v_stopPos_715_ = lean_ctor_get(v_s_702_, 2);
v_isSharedCheck_731_ = !lean_is_exclusive(v_s_702_);
if (v_isSharedCheck_731_ == 0)
{
v___x_717_ = v_s_702_;
v_isShared_718_ = v_isSharedCheck_731_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_stopPos_715_);
lean_inc(v_startPos_714_);
lean_inc(v_str_713_);
lean_dec(v_s_702_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_731_;
goto v_resetjp_716_;
}
v___jp_704_:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; uint8_t v___x_712_; 
v___x_708_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v_p_703_);
v___x_709_ = lean_unsigned_to_nat(0u);
v___x_710_ = l_String_Slice_Pos_skipWhile___redArg(v___y_705_, v___x_709_, v___x_708_);
lean_dec_ref(v___y_705_);
v___x_711_ = lean_nat_sub(v_endExclusive_707_, v_startInclusive_706_);
lean_dec(v_startInclusive_706_);
lean_dec(v_endExclusive_707_);
v___x_712_ = lean_nat_dec_eq(v___x_710_, v___x_711_);
lean_dec(v___x_711_);
lean_dec(v___x_710_);
return v___x_712_;
}
v_resetjp_716_:
{
lean_object* v___x_719_; uint8_t v___x_725_; 
v___x_719_ = l_String_instInhabitedSlice;
v___x_725_ = lean_string_is_valid_pos(v_str_713_, v_startPos_714_);
if (v___x_725_ == 0)
{
lean_del_object(v___x_717_);
lean_dec(v_stopPos_715_);
lean_dec(v_startPos_714_);
lean_dec_ref(v_str_713_);
goto v___jp_720_;
}
else
{
uint8_t v___x_726_; 
v___x_726_ = lean_string_is_valid_pos(v_str_713_, v_stopPos_715_);
if (v___x_726_ == 0)
{
lean_del_object(v___x_717_);
lean_dec(v_stopPos_715_);
lean_dec(v_startPos_714_);
lean_dec_ref(v_str_713_);
goto v___jp_720_;
}
else
{
uint8_t v___x_727_; 
v___x_727_ = lean_nat_dec_le(v_startPos_714_, v_stopPos_715_);
if (v___x_727_ == 0)
{
lean_del_object(v___x_717_);
lean_dec(v_stopPos_715_);
lean_dec(v_startPos_714_);
lean_dec_ref(v_str_713_);
goto v___jp_720_;
}
else
{
lean_object* v___x_729_; 
lean_inc(v_stopPos_715_);
lean_inc(v_startPos_714_);
if (v_isShared_718_ == 0)
{
v___x_729_ = v___x_717_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_str_713_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_startPos_714_);
lean_ctor_set(v_reuseFailAlloc_730_, 2, v_stopPos_715_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
v___y_705_ = v___x_729_;
v_startInclusive_706_ = v_startPos_714_;
v_endExclusive_707_ = v_stopPos_715_;
goto v___jp_704_;
}
}
}
}
v___jp_720_:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v_startInclusive_723_; lean_object* v_endExclusive_724_; 
v___x_721_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_722_ = l_panic___redArg(v___x_719_, v___x_721_);
v_startInclusive_723_ = lean_ctor_get(v___x_722_, 1);
lean_inc(v_startInclusive_723_);
v_endExclusive_724_ = lean_ctor_get(v___x_722_, 2);
lean_inc(v_endExclusive_724_);
v___y_705_ = v___x_722_;
v_startInclusive_706_ = v_startInclusive_723_;
v_endExclusive_707_ = v_endExclusive_724_;
goto v___jp_704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_all___boxed(lean_object* v_s_732_, lean_object* v_p_733_){
_start:
{
uint8_t v_res_734_; lean_object* v_r_735_; 
v_res_734_ = l_Substring_Raw_all(v_s_732_, v_p_733_);
v_r_735_ = lean_box(v_res_734_);
return v_r_735_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(lean_object* v_msg_736_){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = l_String_instInhabitedSlice;
v___x_738_ = lean_panic_fn_borrowed(v___x_737_, v_msg_736_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0(lean_object* v_p_739_, lean_object* v_s_740_, lean_object* v_pos_741_){
_start:
{
lean_object* v_str_742_; lean_object* v_startInclusive_743_; lean_object* v_endExclusive_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; uint8_t v___x_748_; 
v_str_742_ = lean_ctor_get(v_s_740_, 0);
v_startInclusive_743_ = lean_ctor_get(v_s_740_, 1);
v_endExclusive_744_ = lean_ctor_get(v_s_740_, 2);
v___x_745_ = lean_nat_add(v_startInclusive_743_, v_pos_741_);
v___x_746_ = lean_unsigned_to_nat(0u);
v___x_747_ = lean_nat_sub(v_endExclusive_744_, v___x_745_);
v___x_748_ = lean_nat_dec_eq(v___x_746_, v___x_747_);
lean_dec(v___x_747_);
if (v___x_748_ == 0)
{
uint32_t v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_749_ = lean_string_utf8_get_fast(v_str_742_, v___x_745_);
v___x_750_ = lean_box_uint32(v___x_749_);
lean_inc_ref(v_p_739_);
v___x_751_ = lean_apply_1(v_p_739_, v___x_750_);
v___x_752_ = lean_unbox(v___x_751_);
if (v___x_752_ == 0)
{
lean_dec(v___x_745_);
lean_dec_ref(v_p_739_);
return v_pos_741_;
}
else
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_753_ = lean_string_utf8_next_fast(v_str_742_, v___x_745_);
v___x_754_ = lean_nat_sub(v___x_753_, v___x_745_);
lean_dec(v___x_745_);
v___x_755_ = lean_nat_add(v_pos_741_, v___x_754_);
lean_dec(v___x_754_);
v___x_756_ = lean_nat_dec_lt(v_pos_741_, v___x_755_);
if (v___x_756_ == 0)
{
lean_dec(v___x_755_);
lean_dec_ref(v_p_739_);
return v_pos_741_;
}
else
{
lean_dec(v_pos_741_);
v_pos_741_ = v___x_755_;
goto _start;
}
}
}
else
{
lean_dec(v___x_745_);
lean_dec_ref(v_p_739_);
return v_pos_741_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0___boxed(lean_object* v_p_758_, lean_object* v_s_759_, lean_object* v_pos_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0(v_p_758_, v_s_759_, v_pos_760_);
lean_dec_ref(v_s_759_);
return v_res_761_;
}
}
LEAN_EXPORT uint8_t lean_substring_all(lean_object* v_s_762_, lean_object* v_p_763_){
_start:
{
lean_object* v___y_765_; lean_object* v_startInclusive_766_; lean_object* v_endExclusive_767_; lean_object* v_str_777_; lean_object* v_startPos_778_; lean_object* v_stopPos_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_789_; 
v_str_777_ = lean_ctor_get(v_s_762_, 0);
v_startPos_778_ = lean_ctor_get(v_s_762_, 1);
v_stopPos_779_ = lean_ctor_get(v_s_762_, 2);
v_isSharedCheck_789_ = !lean_is_exclusive(v_s_762_);
if (v_isSharedCheck_789_ == 0)
{
v___x_781_ = v_s_762_;
v_isShared_782_ = v_isSharedCheck_789_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_stopPos_779_);
lean_inc(v_startPos_778_);
lean_inc(v_str_777_);
lean_dec(v_s_762_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_789_;
goto v_resetjp_780_;
}
v___jp_764_:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_768_ = lean_unsigned_to_nat(0u);
v___x_769_ = l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0(v_p_763_, v___y_765_, v___x_768_);
lean_dec_ref(v___y_765_);
v___x_770_ = lean_nat_sub(v_endExclusive_767_, v_startInclusive_766_);
lean_dec(v_startInclusive_766_);
lean_dec(v_endExclusive_767_);
v___x_771_ = lean_nat_dec_eq(v___x_769_, v___x_770_);
lean_dec(v___x_770_);
lean_dec(v___x_769_);
return v___x_771_;
}
v___jp_772_:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v_startInclusive_775_; lean_object* v_endExclusive_776_; 
v___x_773_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_774_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_773_);
v_startInclusive_775_ = lean_ctor_get(v___x_774_, 1);
lean_inc(v_startInclusive_775_);
v_endExclusive_776_ = lean_ctor_get(v___x_774_, 2);
lean_inc(v_endExclusive_776_);
v___y_765_ = v___x_774_;
v_startInclusive_766_ = v_startInclusive_775_;
v_endExclusive_767_ = v_endExclusive_776_;
goto v___jp_764_;
}
v_resetjp_780_:
{
uint8_t v___x_783_; 
v___x_783_ = lean_string_is_valid_pos(v_str_777_, v_startPos_778_);
if (v___x_783_ == 0)
{
lean_del_object(v___x_781_);
lean_dec(v_stopPos_779_);
lean_dec(v_startPos_778_);
lean_dec_ref(v_str_777_);
goto v___jp_772_;
}
else
{
uint8_t v___x_784_; 
v___x_784_ = lean_string_is_valid_pos(v_str_777_, v_stopPos_779_);
if (v___x_784_ == 0)
{
lean_del_object(v___x_781_);
lean_dec(v_stopPos_779_);
lean_dec(v_startPos_778_);
lean_dec_ref(v_str_777_);
goto v___jp_772_;
}
else
{
uint8_t v___x_785_; 
v___x_785_ = lean_nat_dec_le(v_startPos_778_, v_stopPos_779_);
if (v___x_785_ == 0)
{
lean_del_object(v___x_781_);
lean_dec(v_stopPos_779_);
lean_dec(v_startPos_778_);
lean_dec_ref(v_str_777_);
goto v___jp_772_;
}
else
{
lean_object* v___x_787_; 
lean_inc(v_stopPos_779_);
lean_inc(v_startPos_778_);
if (v_isShared_782_ == 0)
{
v___x_787_ = v___x_781_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_str_777_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_startPos_778_);
lean_ctor_set(v_reuseFailAlloc_788_, 2, v_stopPos_779_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
v___y_765_ = v___x_787_;
v_startInclusive_766_ = v_startPos_778_;
v_endExclusive_767_ = v_stopPos_779_;
goto v___jp_764_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_allImpl___boxed(lean_object* v_s_790_, lean_object* v_p_791_){
_start:
{
uint8_t v_res_792_; lean_object* v_r_793_; 
v_res_792_ = lean_substring_all(v_s_790_, v_p_791_);
v_r_793_ = lean_box(v_res_792_);
return v_r_793_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_contains___lam__0(uint32_t v_c_794_, uint32_t v_a_795_){
_start:
{
uint8_t v___x_796_; 
v___x_796_ = lean_uint32_dec_eq(v_a_795_, v_c_794_);
return v___x_796_;
}
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
LEAN_EXPORT uint8_t l_Substring_Raw_contains(lean_object* v_s_803_, uint32_t v_c_804_){
_start:
{
lean_object* v___x_805_; lean_object* v___f_806_; lean_object* v___x_807_; lean_object* v_str_808_; lean_object* v_startPos_809_; lean_object* v_stopPos_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_828_; 
v___x_805_ = lean_box_uint32(v_c_804_);
v___f_806_ = lean_alloc_closure((void*)(l_Substring_Raw_contains___lam__0___boxed), 2, 1);
lean_closure_set(v___f_806_, 0, v___x_805_);
lean_inc_ref(v___f_806_);
v___x_807_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___f_806_);
v_str_808_ = lean_ctor_get(v_s_803_, 0);
v_startPos_809_ = lean_ctor_get(v_s_803_, 1);
v_stopPos_810_ = lean_ctor_get(v_s_803_, 2);
v_isSharedCheck_828_ = !lean_is_exclusive(v_s_803_);
if (v_isSharedCheck_828_ == 0)
{
v___x_812_ = v_s_803_;
v_isShared_813_ = v_isSharedCheck_828_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_stopPos_810_);
lean_inc(v_startPos_809_);
lean_inc(v_str_808_);
lean_dec(v_s_803_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_828_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_814_; lean_object* v___f_815_; lean_object* v___x_816_; uint8_t v___x_821_; 
v___x_814_ = l_String_instInhabitedSlice;
v___f_815_ = lean_alloc_closure((void*)(l_Substring_Raw_any___lam__0), 8, 1);
lean_closure_set(v___f_815_, 0, v___x_807_);
v___x_816_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_816_, 0, lean_box(0));
lean_closure_set(v___x_816_, 1, v___f_806_);
v___x_821_ = lean_string_is_valid_pos(v_str_808_, v_startPos_809_);
if (v___x_821_ == 0)
{
lean_del_object(v___x_812_);
lean_dec(v_stopPos_810_);
lean_dec(v_startPos_809_);
lean_dec_ref(v_str_808_);
goto v___jp_817_;
}
else
{
uint8_t v___x_822_; 
v___x_822_ = lean_string_is_valid_pos(v_str_808_, v_stopPos_810_);
if (v___x_822_ == 0)
{
lean_del_object(v___x_812_);
lean_dec(v_stopPos_810_);
lean_dec(v_startPos_809_);
lean_dec_ref(v_str_808_);
goto v___jp_817_;
}
else
{
uint8_t v___x_823_; 
v___x_823_ = lean_nat_dec_le(v_startPos_809_, v_stopPos_810_);
if (v___x_823_ == 0)
{
lean_del_object(v___x_812_);
lean_dec(v_stopPos_810_);
lean_dec(v_startPos_809_);
lean_dec_ref(v_str_808_);
goto v___jp_817_;
}
else
{
lean_object* v___x_825_; 
if (v_isShared_813_ == 0)
{
v___x_825_ = v___x_812_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_str_808_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v_startPos_809_);
lean_ctor_set(v_reuseFailAlloc_827_, 2, v_stopPos_810_);
v___x_825_ = v_reuseFailAlloc_827_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
uint8_t v___x_826_; 
v___x_826_ = l_String_Slice_contains___redArg(v___f_815_, v___x_825_, v___x_816_);
return v___x_826_;
}
}
}
}
v___jp_817_:
{
lean_object* v___x_818_; lean_object* v___x_819_; uint8_t v___x_820_; 
v___x_818_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_819_ = l_panic___redArg(v___x_814_, v___x_818_);
v___x_820_ = l_String_Slice_contains___redArg(v___f_815_, v___x_819_, v___x_816_);
return v___x_820_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_contains___boxed(lean_object* v_s_829_, lean_object* v_c_830_){
_start:
{
uint32_t v_c_boxed_831_; uint8_t v_res_832_; lean_object* v_r_833_; 
v_c_boxed_831_ = lean_unbox_uint32(v_c_830_);
lean_dec(v_c_830_);
v_res_832_ = l_Substring_Raw_contains(v_s_829_, v_c_boxed_831_);
v_r_833_ = lean_box(v_res_832_);
return v_r_833_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux(lean_object* v_s_834_, lean_object* v_stopPos_835_, lean_object* v_p_836_, lean_object* v_i_837_){
_start:
{
uint8_t v___x_838_; 
v___x_838_ = lean_nat_dec_lt(v_i_837_, v_stopPos_835_);
if (v___x_838_ == 0)
{
lean_dec_ref(v_p_836_);
return v_i_837_;
}
else
{
uint32_t v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; uint8_t v___x_842_; 
v___x_839_ = lean_string_utf8_get(v_s_834_, v_i_837_);
v___x_840_ = lean_box_uint32(v___x_839_);
lean_inc_ref(v_p_836_);
v___x_841_ = lean_apply_1(v_p_836_, v___x_840_);
v___x_842_ = lean_unbox(v___x_841_);
if (v___x_842_ == 0)
{
lean_dec_ref(v_p_836_);
return v_i_837_;
}
else
{
lean_object* v___x_843_; 
v___x_843_ = lean_string_utf8_next(v_s_834_, v_i_837_);
lean_dec(v_i_837_);
v_i_837_ = v___x_843_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___boxed(lean_object* v_s_845_, lean_object* v_stopPos_846_, lean_object* v_p_847_, lean_object* v_i_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Substring_Raw_takeWhileAux(v_s_845_, v_stopPos_846_, v_p_847_, v_i_848_);
lean_dec(v_stopPos_846_);
lean_dec_ref(v_s_845_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhile(lean_object* v_x_850_, lean_object* v_x_851_){
_start:
{
lean_object* v_str_852_; lean_object* v_startPos_853_; lean_object* v_stopPos_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_862_; 
v_str_852_ = lean_ctor_get(v_x_850_, 0);
v_startPos_853_ = lean_ctor_get(v_x_850_, 1);
v_stopPos_854_ = lean_ctor_get(v_x_850_, 2);
v_isSharedCheck_862_ = !lean_is_exclusive(v_x_850_);
if (v_isSharedCheck_862_ == 0)
{
v___x_856_ = v_x_850_;
v_isShared_857_ = v_isSharedCheck_862_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_stopPos_854_);
lean_inc(v_startPos_853_);
lean_inc(v_str_852_);
lean_dec(v_x_850_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_862_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v_e_858_; lean_object* v___x_860_; 
lean_inc(v_startPos_853_);
v_e_858_ = l_Substring_Raw_takeWhileAux(v_str_852_, v_stopPos_854_, v_x_851_, v_startPos_853_);
lean_dec(v_stopPos_854_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 2, v_e_858_);
v___x_860_ = v___x_856_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_str_852_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_startPos_853_);
lean_ctor_set(v_reuseFailAlloc_861_, 2, v_e_858_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(lean_object* v_a_863_, lean_object* v_s_864_, lean_object* v_stopPos_865_, lean_object* v_i_866_){
_start:
{
uint8_t v___x_867_; 
v___x_867_ = lean_nat_dec_lt(v_i_866_, v_stopPos_865_);
if (v___x_867_ == 0)
{
lean_dec_ref(v_a_863_);
return v_i_866_;
}
else
{
uint32_t v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; uint8_t v___x_871_; 
v___x_868_ = lean_string_utf8_get(v_s_864_, v_i_866_);
v___x_869_ = lean_box_uint32(v___x_868_);
lean_inc_ref(v_a_863_);
v___x_870_ = lean_apply_1(v_a_863_, v___x_869_);
v___x_871_ = lean_unbox(v___x_870_);
if (v___x_871_ == 0)
{
lean_dec_ref(v_a_863_);
return v_i_866_;
}
else
{
lean_object* v___x_872_; 
v___x_872_ = lean_string_utf8_next(v_s_864_, v_i_866_);
lean_dec(v_i_866_);
v_i_866_ = v___x_872_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0___boxed(lean_object* v_a_874_, lean_object* v_s_875_, lean_object* v_stopPos_876_, lean_object* v_i_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(v_a_874_, v_s_875_, v_stopPos_876_, v_i_877_);
lean_dec(v_stopPos_876_);
lean_dec_ref(v_s_875_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* lean_substring_takewhile(lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
lean_object* v_str_881_; lean_object* v_startPos_882_; lean_object* v_stopPos_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_891_; 
v_str_881_ = lean_ctor_get(v_a_879_, 0);
v_startPos_882_ = lean_ctor_get(v_a_879_, 1);
v_stopPos_883_ = lean_ctor_get(v_a_879_, 2);
v_isSharedCheck_891_ = !lean_is_exclusive(v_a_879_);
if (v_isSharedCheck_891_ == 0)
{
v___x_885_ = v_a_879_;
v_isShared_886_ = v_isSharedCheck_891_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_stopPos_883_);
lean_inc(v_startPos_882_);
lean_inc(v_str_881_);
lean_dec(v_a_879_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_891_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v_e_887_; lean_object* v___x_889_; 
lean_inc(v_startPos_882_);
v_e_887_ = l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(v_a_880_, v_str_881_, v_stopPos_883_, v_startPos_882_);
lean_dec(v_stopPos_883_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 2, v_e_887_);
v___x_889_ = v___x_885_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_str_881_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v_startPos_882_);
lean_ctor_set(v_reuseFailAlloc_890_, 2, v_e_887_);
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
LEAN_EXPORT lean_object* l_Substring_Raw_dropWhile(lean_object* v_x_892_, lean_object* v_x_893_){
_start:
{
lean_object* v_str_894_; lean_object* v_startPos_895_; lean_object* v_stopPos_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_904_; 
v_str_894_ = lean_ctor_get(v_x_892_, 0);
v_startPos_895_ = lean_ctor_get(v_x_892_, 1);
v_stopPos_896_ = lean_ctor_get(v_x_892_, 2);
v_isSharedCheck_904_ = !lean_is_exclusive(v_x_892_);
if (v_isSharedCheck_904_ == 0)
{
v___x_898_ = v_x_892_;
v_isShared_899_ = v_isSharedCheck_904_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_stopPos_896_);
lean_inc(v_startPos_895_);
lean_inc(v_str_894_);
lean_dec(v_x_892_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_904_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v_b_900_; lean_object* v___x_902_; 
v_b_900_ = l_Substring_Raw_takeWhileAux(v_str_894_, v_stopPos_896_, v_x_893_, v_startPos_895_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 1, v_b_900_);
v___x_902_ = v___x_898_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_str_894_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v_b_900_);
lean_ctor_set(v_reuseFailAlloc_903_, 2, v_stopPos_896_);
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
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux(lean_object* v_s_905_, lean_object* v_begPos_906_, lean_object* v_p_907_, lean_object* v_i_908_){
_start:
{
uint8_t v___x_909_; 
v___x_909_ = lean_nat_dec_lt(v_begPos_906_, v_i_908_);
if (v___x_909_ == 0)
{
lean_dec_ref(v_p_907_);
return v_i_908_;
}
else
{
lean_object* v_i_x27_910_; uint32_t v_c_911_; lean_object* v___x_912_; lean_object* v___x_913_; uint8_t v___x_914_; uint8_t v___x_915_; 
v_i_x27_910_ = lean_string_utf8_prev(v_s_905_, v_i_908_);
v_c_911_ = lean_string_utf8_get(v_s_905_, v_i_x27_910_);
v___x_912_ = lean_box_uint32(v_c_911_);
lean_inc_ref(v_p_907_);
v___x_913_ = lean_apply_1(v_p_907_, v___x_912_);
v___x_914_ = lean_unbox(v___x_913_);
v___x_915_ = lean_bool_not(v___x_914_);
if (v___x_915_ == 0)
{
lean_dec(v_i_908_);
v_i_908_ = v_i_x27_910_;
goto _start;
}
else
{
lean_dec(v_i_x27_910_);
lean_dec_ref(v_p_907_);
return v_i_908_;
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
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___lam__0(lean_object* v___y_989_, uint8_t v___x_990_, lean_object* v_it_991_, lean_object* v_acc_992_, lean_object* v_hP_993_, lean_object* v_recur_994_){
_start:
{
lean_object* v_str_995_; lean_object* v_startInclusive_996_; lean_object* v_endExclusive_997_; lean_object* v___x_998_; uint8_t v___x_999_; 
v_str_995_ = lean_ctor_get(v___y_989_, 0);
v_startInclusive_996_ = lean_ctor_get(v___y_989_, 1);
v_endExclusive_997_ = lean_ctor_get(v___y_989_, 2);
v___x_998_ = lean_nat_sub(v_endExclusive_997_, v_startInclusive_996_);
v___x_999_ = lean_nat_dec_eq(v_it_991_, v___x_998_);
lean_dec(v___x_998_);
if (v___x_999_ == 0)
{
lean_object* v_snd_1000_; lean_object* v_snd_1001_; lean_object* v_fst_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1068_; 
v_snd_1000_ = lean_ctor_get(v_acc_992_, 1);
lean_inc(v_snd_1000_);
v_snd_1001_ = lean_ctor_get(v_snd_1000_, 1);
lean_inc(v_snd_1001_);
v_fst_1002_ = lean_ctor_get(v_acc_992_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v_acc_992_);
if (v_isSharedCheck_1068_ == 0)
{
lean_object* v_unused_1069_; 
v_unused_1069_ = lean_ctor_get(v_acc_992_, 1);
lean_dec(v_unused_1069_);
v___x_1004_ = v_acc_992_;
v_isShared_1005_ = v_isSharedCheck_1068_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_fst_1002_);
lean_dec(v_acc_992_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1068_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v_fst_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1066_; 
v_fst_1006_ = lean_ctor_get(v_snd_1000_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_snd_1000_);
if (v_isSharedCheck_1066_ == 0)
{
lean_object* v_unused_1067_; 
v_unused_1067_ = lean_ctor_get(v_snd_1000_, 1);
lean_dec(v_unused_1067_);
v___x_1008_ = v_snd_1000_;
v_isShared_1009_ = v_isSharedCheck_1066_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_fst_1006_);
lean_dec(v_snd_1000_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1066_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v_snd_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1064_; 
v_snd_1010_ = lean_ctor_get(v_snd_1001_, 1);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_snd_1001_);
if (v_isSharedCheck_1064_ == 0)
{
lean_object* v_unused_1065_; 
v_unused_1065_ = lean_ctor_get(v_snd_1001_, 0);
lean_dec(v_unused_1065_);
v___x_1012_ = v_snd_1001_;
v_isShared_1013_ = v_isSharedCheck_1064_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_snd_1010_);
lean_dec(v_snd_1001_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1064_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1014_; uint32_t v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; uint8_t v___y_1019_; uint8_t v___y_1020_; uint8_t v___y_1038_; uint8_t v___y_1039_; uint8_t v___y_1047_; uint8_t v___y_1055_; uint32_t v___x_1060_; uint8_t v___x_1061_; 
v___x_1014_ = lean_nat_add(v_startInclusive_996_, v_it_991_);
v___x_1015_ = lean_string_utf8_get_fast(v_str_995_, v___x_1014_);
v___x_1016_ = lean_string_utf8_next_fast(v_str_995_, v___x_1014_);
lean_dec(v___x_1014_);
v___x_1017_ = lean_nat_sub(v___x_1016_, v_startInclusive_996_);
v___x_1060_ = 48;
v___x_1061_ = lean_uint32_dec_le(v___x_1060_, v___x_1015_);
if (v___x_1061_ == 0)
{
v___y_1055_ = v___x_1061_;
goto v___jp_1054_;
}
else
{
uint32_t v___x_1062_; uint8_t v___x_1063_; 
v___x_1062_ = 57;
v___x_1063_ = lean_uint32_dec_le(v___x_1015_, v___x_1062_);
v___y_1055_ = v___x_1063_;
goto v___jp_1054_;
}
v___jp_1018_:
{
uint32_t v___x_1021_; uint8_t v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1026_; 
v___x_1021_ = 95;
v___x_1022_ = lean_uint32_dec_eq(v___x_1015_, v___x_1021_);
v___x_1023_ = lean_box(v___y_1019_);
v___x_1024_ = lean_box(v___y_1020_);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 1, v___x_1024_);
lean_ctor_set(v___x_1012_, 0, v___x_1023_);
v___x_1026_ = v___x_1012_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1023_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1027_; lean_object* v___x_1029_; 
v___x_1027_ = lean_box(v___x_1022_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 1, v___x_1026_);
lean_ctor_set(v___x_1008_, 0, v___x_1027_);
v___x_1029_ = v___x_1008_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1027_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v___x_1026_);
v___x_1029_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
lean_object* v___x_1030_; lean_object* v___x_1032_; 
v___x_1030_ = lean_box(v___x_990_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 1, v___x_1029_);
lean_ctor_set(v___x_1004_, 0, v___x_1030_);
v___x_1032_ = v___x_1004_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v___x_1029_);
v___x_1032_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
lean_object* v___x_1033_; 
v___x_1033_ = lean_apply_4(v_recur_994_, v___x_1017_, v___x_1032_, lean_box(0), lean_box(0));
return v___x_1033_;
}
}
}
}
v___jp_1037_:
{
if (v___y_1039_ == 0)
{
lean_dec(v_fst_1006_);
v___y_1019_ = v___y_1038_;
v___y_1020_ = v___y_1039_;
goto v___jp_1018_;
}
else
{
uint8_t v___x_1040_; 
v___x_1040_ = lean_unbox(v_fst_1006_);
if (v___x_1040_ == 0)
{
uint8_t v___x_1041_; uint8_t v___x_1042_; 
v___x_1041_ = lean_unbox(v_fst_1006_);
lean_dec(v_fst_1006_);
v___x_1042_ = lean_bool_not(v___x_1041_);
v___y_1019_ = v___y_1038_;
v___y_1020_ = v___x_1042_;
goto v___jp_1018_;
}
else
{
uint32_t v___x_1043_; uint8_t v___x_1044_; uint8_t v___x_1045_; 
lean_dec(v_fst_1006_);
v___x_1043_ = 95;
v___x_1044_ = lean_uint32_dec_eq(v___x_1015_, v___x_1043_);
v___x_1045_ = lean_bool_not(v___x_1044_);
v___y_1019_ = v___y_1038_;
v___y_1020_ = v___x_1045_;
goto v___jp_1018_;
}
}
}
v___jp_1046_:
{
uint8_t v___x_1048_; 
v___x_1048_ = lean_unbox(v_fst_1002_);
if (v___x_1048_ == 0)
{
uint8_t v___x_1049_; uint8_t v___x_1050_; 
v___x_1049_ = lean_unbox(v_fst_1002_);
lean_dec(v_fst_1002_);
v___x_1050_ = lean_bool_not(v___x_1049_);
v___y_1038_ = v___y_1047_;
v___y_1039_ = v___x_1050_;
goto v___jp_1037_;
}
else
{
uint32_t v___x_1051_; uint8_t v___x_1052_; uint8_t v___x_1053_; 
lean_dec(v_fst_1002_);
v___x_1051_ = 95;
v___x_1052_ = lean_uint32_dec_eq(v___x_1015_, v___x_1051_);
v___x_1053_ = lean_bool_not(v___x_1052_);
v___y_1038_ = v___y_1047_;
v___y_1039_ = v___x_1053_;
goto v___jp_1037_;
}
}
v___jp_1054_:
{
uint8_t v___x_1056_; 
v___x_1056_ = lean_unbox(v_snd_1010_);
if (v___x_1056_ == 0)
{
uint8_t v___x_1057_; 
lean_dec(v_fst_1006_);
lean_dec(v_fst_1002_);
v___x_1057_ = lean_unbox(v_snd_1010_);
lean_dec(v_snd_1010_);
v___y_1019_ = v___y_1055_;
v___y_1020_ = v___x_1057_;
goto v___jp_1018_;
}
else
{
lean_dec(v_snd_1010_);
if (v___y_1055_ == 0)
{
uint32_t v___x_1058_; uint8_t v___x_1059_; 
v___x_1058_ = 95;
v___x_1059_ = lean_uint32_dec_eq(v___x_1015_, v___x_1058_);
if (v___x_1059_ == 0)
{
lean_dec(v_fst_1006_);
lean_dec(v_fst_1002_);
v___y_1019_ = v___y_1055_;
v___y_1020_ = v___x_1059_;
goto v___jp_1018_;
}
else
{
v___y_1047_ = v___y_1055_;
goto v___jp_1046_;
}
}
else
{
v___y_1047_ = v___y_1055_;
goto v___jp_1046_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_recur_994_);
return v_acc_992_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___lam__0___boxed(lean_object* v___y_1070_, lean_object* v___x_1071_, lean_object* v_it_1072_, lean_object* v_acc_1073_, lean_object* v_hP_1074_, lean_object* v_recur_1075_){
_start:
{
uint8_t v___x_1053__boxed_1076_; lean_object* v_res_1077_; 
v___x_1053__boxed_1076_ = lean_unbox(v___x_1071_);
v_res_1077_ = l_Substring_Raw_isNat___lam__0(v___y_1070_, v___x_1053__boxed_1076_, v_it_1072_, v_acc_1073_, v_hP_1074_, v_recur_1075_);
lean_dec(v_it_1072_);
lean_dec_ref(v___y_1070_);
return v_res_1077_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_isNat(lean_object* v_s_1078_){
_start:
{
lean_object* v_str_1079_; lean_object* v_startPos_1080_; lean_object* v_stopPos_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1119_; 
v_str_1079_ = lean_ctor_get(v_s_1078_, 0);
v_startPos_1080_ = lean_ctor_get(v_s_1078_, 1);
v_stopPos_1081_ = lean_ctor_get(v_s_1078_, 2);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_s_1078_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1083_ = v_s_1078_;
v_isShared_1084_ = v_isSharedCheck_1119_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_stopPos_1081_);
lean_inc(v_startPos_1080_);
lean_inc(v_str_1079_);
lean_dec(v_s_1078_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1119_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; 
v___x_1085_ = lean_nat_sub(v_stopPos_1081_, v_startPos_1080_);
v___x_1086_ = lean_unsigned_to_nat(0u);
v___x_1087_ = lean_nat_dec_eq(v___x_1085_, v___x_1086_);
lean_dec(v___x_1085_);
if (v___x_1087_ == 0)
{
uint8_t v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___y_1097_; lean_object* v___x_1108_; uint8_t v___x_1112_; 
v___x_1088_ = 1;
v___x_1089_ = lean_box(v___x_1087_);
v___x_1090_ = lean_box(v___x_1088_);
v___x_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1089_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
v___x_1092_ = lean_box(v___x_1087_);
v___x_1093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
lean_ctor_set(v___x_1093_, 1, v___x_1091_);
v___x_1094_ = lean_box(v___x_1088_);
v___x_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
lean_ctor_set(v___x_1095_, 1, v___x_1093_);
v___x_1108_ = l_String_instInhabitedSlice;
v___x_1112_ = lean_string_is_valid_pos(v_str_1079_, v_startPos_1080_);
if (v___x_1112_ == 0)
{
lean_del_object(v___x_1083_);
lean_dec(v_stopPos_1081_);
lean_dec(v_startPos_1080_);
lean_dec_ref(v_str_1079_);
goto v___jp_1109_;
}
else
{
uint8_t v___x_1113_; 
v___x_1113_ = lean_string_is_valid_pos(v_str_1079_, v_stopPos_1081_);
if (v___x_1113_ == 0)
{
lean_del_object(v___x_1083_);
lean_dec(v_stopPos_1081_);
lean_dec(v_startPos_1080_);
lean_dec_ref(v_str_1079_);
goto v___jp_1109_;
}
else
{
uint8_t v___x_1114_; 
v___x_1114_ = lean_nat_dec_le(v_startPos_1080_, v_stopPos_1081_);
if (v___x_1114_ == 0)
{
lean_del_object(v___x_1083_);
lean_dec(v_stopPos_1081_);
lean_dec(v_startPos_1080_);
lean_dec_ref(v_str_1079_);
goto v___jp_1109_;
}
else
{
lean_object* v___x_1116_; 
if (v_isShared_1084_ == 0)
{
v___x_1116_ = v___x_1083_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_str_1079_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v_startPos_1080_);
lean_ctor_set(v_reuseFailAlloc_1117_, 2, v_stopPos_1081_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
v___y_1097_ = v___x_1116_;
goto v___jp_1096_;
}
}
}
}
v___jp_1096_:
{
lean_object* v___x_1098_; lean_object* v___f_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v_snd_1102_; lean_object* v_snd_1103_; lean_object* v_snd_1104_; uint8_t v___x_1105_; 
v___x_1098_ = lean_box(v___x_1087_);
lean_inc_ref(v___y_1097_);
v___f_1099_ = lean_alloc_closure((void*)(l_Substring_Raw_isNat___lam__0___boxed), 6, 2);
lean_closure_set(v___f_1099_, 0, v___y_1097_);
lean_closure_set(v___f_1099_, 1, v___x_1098_);
v___x_1100_ = l_String_Slice_positions(v___y_1097_);
lean_dec_ref(v___y_1097_);
v___x_1101_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1099_, v___x_1100_, v___x_1095_, lean_box(0));
v_snd_1102_ = lean_ctor_get(v___x_1101_, 1);
lean_inc(v_snd_1102_);
lean_dec(v___x_1101_);
v_snd_1103_ = lean_ctor_get(v_snd_1102_, 1);
lean_inc(v_snd_1103_);
lean_dec(v_snd_1102_);
v_snd_1104_ = lean_ctor_get(v_snd_1103_, 1);
v___x_1105_ = lean_unbox(v_snd_1104_);
if (v___x_1105_ == 0)
{
lean_dec(v_snd_1103_);
return v___x_1087_;
}
else
{
lean_object* v_fst_1106_; uint8_t v___x_1107_; 
v_fst_1106_ = lean_ctor_get(v_snd_1103_, 0);
lean_inc(v_fst_1106_);
lean_dec(v_snd_1103_);
v___x_1107_ = lean_unbox(v_fst_1106_);
lean_dec(v_fst_1106_);
return v___x_1107_;
}
}
v___jp_1109_:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_1111_ = l_panic___redArg(v___x_1108_, v___x_1110_);
v___y_1097_ = v___x_1111_;
goto v___jp_1096_;
}
}
else
{
uint8_t v___x_1118_; 
lean_del_object(v___x_1083_);
lean_dec(v_stopPos_1081_);
lean_dec(v_startPos_1080_);
lean_dec_ref(v_str_1079_);
v___x_1118_ = 0;
return v___x_1118_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___boxed(lean_object* v_s_1120_){
_start:
{
uint8_t v_res_1121_; lean_object* v_r_1122_; 
v_res_1121_ = l_Substring_Raw_isNat(v_s_1120_);
v_r_1122_ = lean_box(v_res_1121_);
return v_r_1122_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(lean_object* v___x_1123_, lean_object* v___y_1124_, lean_object* v_a_1125_, lean_object* v_b_1126_){
_start:
{
lean_object* v_str_1127_; lean_object* v_startInclusive_1128_; lean_object* v_endExclusive_1129_; lean_object* v___x_1130_; uint8_t v___x_1131_; 
v_str_1127_ = lean_ctor_get(v___y_1124_, 0);
v_startInclusive_1128_ = lean_ctor_get(v___y_1124_, 1);
v_endExclusive_1129_ = lean_ctor_get(v___y_1124_, 2);
v___x_1130_ = lean_nat_sub(v_endExclusive_1129_, v_startInclusive_1128_);
v___x_1131_ = lean_nat_dec_eq(v_a_1125_, v___x_1130_);
lean_dec(v___x_1130_);
if (v___x_1131_ == 0)
{
lean_object* v_snd_1132_; lean_object* v_snd_1133_; lean_object* v_fst_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1202_; 
v_snd_1132_ = lean_ctor_get(v_b_1126_, 1);
lean_inc(v_snd_1132_);
v_snd_1133_ = lean_ctor_get(v_snd_1132_, 1);
lean_inc(v_snd_1133_);
v_fst_1134_ = lean_ctor_get(v_b_1126_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_b_1126_);
if (v_isSharedCheck_1202_ == 0)
{
lean_object* v_unused_1203_; 
v_unused_1203_ = lean_ctor_get(v_b_1126_, 1);
lean_dec(v_unused_1203_);
v___x_1136_ = v_b_1126_;
v_isShared_1137_ = v_isSharedCheck_1202_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_fst_1134_);
lean_dec(v_b_1126_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1202_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v_fst_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1200_; 
v_fst_1138_ = lean_ctor_get(v_snd_1132_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v_snd_1132_);
if (v_isSharedCheck_1200_ == 0)
{
lean_object* v_unused_1201_; 
v_unused_1201_ = lean_ctor_get(v_snd_1132_, 1);
lean_dec(v_unused_1201_);
v___x_1140_ = v_snd_1132_;
v_isShared_1141_ = v_isSharedCheck_1200_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_fst_1138_);
lean_dec(v_snd_1132_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1200_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v_snd_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1198_; 
v_snd_1142_ = lean_ctor_get(v_snd_1133_, 1);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_snd_1133_);
if (v_isSharedCheck_1198_ == 0)
{
lean_object* v_unused_1199_; 
v_unused_1199_ = lean_ctor_get(v_snd_1133_, 0);
lean_dec(v_unused_1199_);
v___x_1144_ = v_snd_1133_;
v_isShared_1145_ = v_isSharedCheck_1198_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_snd_1142_);
lean_dec(v_snd_1133_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1198_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1146_; uint8_t v___x_1147_; lean_object* v___x_1148_; uint32_t v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; uint8_t v___y_1153_; uint8_t v___y_1154_; uint8_t v___y_1172_; uint8_t v___y_1173_; uint8_t v___y_1181_; uint8_t v___y_1189_; uint32_t v___x_1194_; uint8_t v___x_1195_; 
v___x_1146_ = lean_unsigned_to_nat(0u);
v___x_1147_ = lean_nat_dec_eq(v___x_1123_, v___x_1146_);
v___x_1148_ = lean_nat_add(v_startInclusive_1128_, v_a_1125_);
lean_dec(v_a_1125_);
v___x_1149_ = lean_string_utf8_get_fast(v_str_1127_, v___x_1148_);
v___x_1150_ = lean_string_utf8_next_fast(v_str_1127_, v___x_1148_);
lean_dec(v___x_1148_);
v___x_1151_ = lean_nat_sub(v___x_1150_, v_startInclusive_1128_);
v___x_1194_ = 48;
v___x_1195_ = lean_uint32_dec_le(v___x_1194_, v___x_1149_);
if (v___x_1195_ == 0)
{
v___y_1189_ = v___x_1195_;
goto v___jp_1188_;
}
else
{
uint32_t v___x_1196_; uint8_t v___x_1197_; 
v___x_1196_ = 57;
v___x_1197_ = lean_uint32_dec_le(v___x_1149_, v___x_1196_);
v___y_1189_ = v___x_1197_;
goto v___jp_1188_;
}
v___jp_1152_:
{
uint32_t v___x_1155_; uint8_t v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1160_; 
v___x_1155_ = 95;
v___x_1156_ = lean_uint32_dec_eq(v___x_1149_, v___x_1155_);
v___x_1157_ = lean_box(v___y_1153_);
v___x_1158_ = lean_box(v___y_1154_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 1, v___x_1158_);
lean_ctor_set(v___x_1144_, 0, v___x_1157_);
v___x_1160_ = v___x_1144_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1157_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v___x_1158_);
v___x_1160_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
lean_object* v___x_1161_; lean_object* v___x_1163_; 
v___x_1161_ = lean_box(v___x_1156_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 1, v___x_1160_);
lean_ctor_set(v___x_1140_, 0, v___x_1161_);
v___x_1163_ = v___x_1140_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v___x_1160_);
v___x_1163_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1164_; lean_object* v___x_1166_; 
v___x_1164_ = lean_box(v___x_1147_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 1, v___x_1163_);
lean_ctor_set(v___x_1136_, 0, v___x_1164_);
v___x_1166_ = v___x_1136_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1164_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v___x_1163_);
v___x_1166_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
v_a_1125_ = v___x_1151_;
v_b_1126_ = v___x_1166_;
goto _start;
}
}
}
}
v___jp_1171_:
{
if (v___y_1173_ == 0)
{
lean_dec(v_fst_1138_);
v___y_1153_ = v___y_1172_;
v___y_1154_ = v___y_1173_;
goto v___jp_1152_;
}
else
{
uint8_t v___x_1174_; 
v___x_1174_ = lean_unbox(v_fst_1138_);
if (v___x_1174_ == 0)
{
uint8_t v___x_1175_; uint8_t v___x_1176_; 
v___x_1175_ = lean_unbox(v_fst_1138_);
lean_dec(v_fst_1138_);
v___x_1176_ = lean_bool_not(v___x_1175_);
v___y_1153_ = v___y_1172_;
v___y_1154_ = v___x_1176_;
goto v___jp_1152_;
}
else
{
uint32_t v___x_1177_; uint8_t v___x_1178_; uint8_t v___x_1179_; 
lean_dec(v_fst_1138_);
v___x_1177_ = 95;
v___x_1178_ = lean_uint32_dec_eq(v___x_1149_, v___x_1177_);
v___x_1179_ = lean_bool_not(v___x_1178_);
v___y_1153_ = v___y_1172_;
v___y_1154_ = v___x_1179_;
goto v___jp_1152_;
}
}
}
v___jp_1180_:
{
uint8_t v___x_1182_; 
v___x_1182_ = lean_unbox(v_fst_1134_);
if (v___x_1182_ == 0)
{
uint8_t v___x_1183_; uint8_t v___x_1184_; 
v___x_1183_ = lean_unbox(v_fst_1134_);
lean_dec(v_fst_1134_);
v___x_1184_ = lean_bool_not(v___x_1183_);
v___y_1172_ = v___y_1181_;
v___y_1173_ = v___x_1184_;
goto v___jp_1171_;
}
else
{
uint32_t v___x_1185_; uint8_t v___x_1186_; uint8_t v___x_1187_; 
lean_dec(v_fst_1134_);
v___x_1185_ = 95;
v___x_1186_ = lean_uint32_dec_eq(v___x_1149_, v___x_1185_);
v___x_1187_ = lean_bool_not(v___x_1186_);
v___y_1172_ = v___y_1181_;
v___y_1173_ = v___x_1187_;
goto v___jp_1171_;
}
}
v___jp_1188_:
{
uint8_t v___x_1190_; 
v___x_1190_ = lean_unbox(v_snd_1142_);
if (v___x_1190_ == 0)
{
uint8_t v___x_1191_; 
lean_dec(v_fst_1138_);
lean_dec(v_fst_1134_);
v___x_1191_ = lean_unbox(v_snd_1142_);
lean_dec(v_snd_1142_);
v___y_1153_ = v___y_1189_;
v___y_1154_ = v___x_1191_;
goto v___jp_1152_;
}
else
{
lean_dec(v_snd_1142_);
if (v___y_1189_ == 0)
{
uint32_t v___x_1192_; uint8_t v___x_1193_; 
v___x_1192_ = 95;
v___x_1193_ = lean_uint32_dec_eq(v___x_1149_, v___x_1192_);
if (v___x_1193_ == 0)
{
lean_dec(v_fst_1138_);
lean_dec(v_fst_1134_);
v___y_1153_ = v___y_1189_;
v___y_1154_ = v___x_1193_;
goto v___jp_1152_;
}
else
{
v___y_1181_ = v___y_1189_;
goto v___jp_1180_;
}
}
else
{
v___y_1181_ = v___y_1189_;
goto v___jp_1180_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1125_);
return v_b_1126_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg___boxed(lean_object* v___x_1204_, lean_object* v___y_1205_, lean_object* v_a_1206_, lean_object* v_b_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(v___x_1204_, v___y_1205_, v_a_1206_, v_b_1207_);
lean_dec_ref(v___y_1205_);
lean_dec(v___x_1204_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(lean_object* v___y_1209_, lean_object* v_a_1210_, lean_object* v_b_1211_){
_start:
{
lean_object* v_str_1212_; lean_object* v_startInclusive_1213_; lean_object* v_endExclusive_1214_; lean_object* v___x_1215_; uint8_t v___x_1216_; 
v_str_1212_ = lean_ctor_get(v___y_1209_, 0);
v_startInclusive_1213_ = lean_ctor_get(v___y_1209_, 1);
v_endExclusive_1214_ = lean_ctor_get(v___y_1209_, 2);
v___x_1215_ = lean_nat_sub(v_endExclusive_1214_, v_startInclusive_1213_);
v___x_1216_ = lean_nat_dec_eq(v_a_1210_, v___x_1215_);
lean_dec(v___x_1215_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1217_; uint32_t v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; uint32_t v___x_1221_; uint8_t v___x_1222_; 
v___x_1217_ = lean_nat_add(v_startInclusive_1213_, v_a_1210_);
lean_dec(v_a_1210_);
v___x_1218_ = lean_string_utf8_get_fast(v_str_1212_, v___x_1217_);
v___x_1219_ = lean_string_utf8_next_fast(v_str_1212_, v___x_1217_);
lean_dec(v___x_1217_);
v___x_1220_ = lean_nat_sub(v___x_1219_, v_startInclusive_1213_);
v___x_1221_ = 95;
v___x_1222_ = lean_uint32_dec_eq(v___x_1218_, v___x_1221_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1223_ = lean_unsigned_to_nat(10u);
v___x_1224_ = lean_nat_mul(v_b_1211_, v___x_1223_);
lean_dec(v_b_1211_);
v___x_1225_ = lean_uint32_to_nat(v___x_1218_);
v___x_1226_ = lean_unsigned_to_nat(48u);
v___x_1227_ = lean_nat_sub(v___x_1225_, v___x_1226_);
lean_dec(v___x_1225_);
v___x_1228_ = lean_nat_add(v___x_1224_, v___x_1227_);
lean_dec(v___x_1227_);
lean_dec(v___x_1224_);
v_a_1210_ = v___x_1220_;
v_b_1211_ = v___x_1228_;
goto _start;
}
else
{
v_a_1210_ = v___x_1220_;
goto _start;
}
}
else
{
lean_dec(v_a_1210_);
return v_b_1211_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg___boxed(lean_object* v___y_1231_, lean_object* v_a_1232_, lean_object* v_b_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(v___y_1231_, v_a_1232_, v_b_1233_);
lean_dec_ref(v___y_1231_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toNat_x3f(lean_object* v_s_1235_){
_start:
{
lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1243_; lean_object* v_str_1246_; lean_object* v_startPos_1247_; lean_object* v_stopPos_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1291_; 
v_str_1246_ = lean_ctor_get(v_s_1235_, 0);
v_startPos_1247_ = lean_ctor_get(v_s_1235_, 1);
v_stopPos_1248_ = lean_ctor_get(v_s_1235_, 2);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_s_1235_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1250_ = v_s_1235_;
v_isShared_1251_ = v_isSharedCheck_1291_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_stopPos_1248_);
lean_inc(v_startPos_1247_);
lean_inc(v_str_1246_);
lean_dec(v_s_1235_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1291_;
goto v_resetjp_1249_;
}
v___jp_1236_:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1239_ = l_String_Slice_positions(v___y_1238_);
v___x_1240_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(v___y_1238_, v___x_1239_, v___y_1237_);
lean_dec_ref(v___y_1238_);
v___x_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
return v___x_1241_;
}
v___jp_1242_:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_1245_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_1244_);
v___y_1237_ = v___y_1243_;
v___y_1238_ = v___x_1245_;
goto v___jp_1236_;
}
v_resetjp_1249_:
{
uint8_t v___y_1253_; lean_object* v___x_1262_; lean_object* v___x_1263_; uint8_t v___x_1264_; 
v___x_1262_ = lean_nat_sub(v_stopPos_1248_, v_startPos_1247_);
v___x_1263_ = lean_unsigned_to_nat(0u);
v___x_1264_ = lean_nat_dec_eq(v___x_1262_, v___x_1263_);
if (v___x_1264_ == 0)
{
uint8_t v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___y_1274_; uint8_t v___x_1286_; 
v___x_1265_ = 1;
v___x_1266_ = lean_box(v___x_1264_);
v___x_1267_ = lean_box(v___x_1265_);
v___x_1268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1266_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
v___x_1269_ = lean_box(v___x_1264_);
v___x_1270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
lean_ctor_set(v___x_1270_, 1, v___x_1268_);
v___x_1271_ = lean_box(v___x_1265_);
v___x_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
lean_ctor_set(v___x_1272_, 1, v___x_1270_);
v___x_1286_ = lean_string_is_valid_pos(v_str_1246_, v_startPos_1247_);
if (v___x_1286_ == 0)
{
goto v___jp_1283_;
}
else
{
uint8_t v___x_1287_; 
v___x_1287_ = lean_string_is_valid_pos(v_str_1246_, v_stopPos_1248_);
if (v___x_1287_ == 0)
{
goto v___jp_1283_;
}
else
{
uint8_t v___x_1288_; 
v___x_1288_ = lean_nat_dec_le(v_startPos_1247_, v_stopPos_1248_);
if (v___x_1288_ == 0)
{
goto v___jp_1283_;
}
else
{
lean_object* v___x_1289_; 
lean_inc(v_stopPos_1248_);
lean_inc(v_startPos_1247_);
lean_inc_ref(v_str_1246_);
v___x_1289_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1289_, 0, v_str_1246_);
lean_ctor_set(v___x_1289_, 1, v_startPos_1247_);
lean_ctor_set(v___x_1289_, 2, v_stopPos_1248_);
v___y_1274_ = v___x_1289_;
goto v___jp_1273_;
}
}
}
v___jp_1273_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v_snd_1277_; lean_object* v_snd_1278_; lean_object* v_snd_1279_; uint8_t v___x_1280_; 
v___x_1275_ = l_String_Slice_positions(v___y_1274_);
v___x_1276_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(v___x_1262_, v___y_1274_, v___x_1275_, v___x_1272_);
lean_dec_ref(v___y_1274_);
lean_dec(v___x_1262_);
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
lean_dec(v_snd_1278_);
v___y_1253_ = v___x_1264_;
goto v___jp_1252_;
}
else
{
lean_object* v_fst_1281_; uint8_t v___x_1282_; 
v_fst_1281_ = lean_ctor_get(v_snd_1278_, 0);
lean_inc(v_fst_1281_);
lean_dec(v_snd_1278_);
v___x_1282_ = lean_unbox(v_fst_1281_);
lean_dec(v_fst_1281_);
v___y_1253_ = v___x_1282_;
goto v___jp_1252_;
}
}
v___jp_1283_:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_1285_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_1284_);
v___y_1274_ = v___x_1285_;
goto v___jp_1273_;
}
}
else
{
lean_object* v___x_1290_; 
lean_dec(v___x_1262_);
lean_del_object(v___x_1250_);
lean_dec(v_stopPos_1248_);
lean_dec(v_startPos_1247_);
lean_dec_ref(v_str_1246_);
v___x_1290_ = lean_box(0);
return v___x_1290_;
}
v___jp_1252_:
{
if (v___y_1253_ == 0)
{
lean_object* v___x_1254_; 
lean_del_object(v___x_1250_);
lean_dec(v_stopPos_1248_);
lean_dec(v_startPos_1247_);
lean_dec_ref(v_str_1246_);
v___x_1254_ = lean_box(0);
return v___x_1254_;
}
else
{
lean_object* v___x_1255_; uint8_t v___x_1256_; 
v___x_1255_ = lean_unsigned_to_nat(0u);
v___x_1256_ = lean_string_is_valid_pos(v_str_1246_, v_startPos_1247_);
if (v___x_1256_ == 0)
{
lean_del_object(v___x_1250_);
lean_dec(v_stopPos_1248_);
lean_dec(v_startPos_1247_);
lean_dec_ref(v_str_1246_);
v___y_1243_ = v___x_1255_;
goto v___jp_1242_;
}
else
{
uint8_t v___x_1257_; 
v___x_1257_ = lean_string_is_valid_pos(v_str_1246_, v_stopPos_1248_);
if (v___x_1257_ == 0)
{
lean_del_object(v___x_1250_);
lean_dec(v_stopPos_1248_);
lean_dec(v_startPos_1247_);
lean_dec_ref(v_str_1246_);
v___y_1243_ = v___x_1255_;
goto v___jp_1242_;
}
else
{
uint8_t v___x_1258_; 
v___x_1258_ = lean_nat_dec_le(v_startPos_1247_, v_stopPos_1248_);
if (v___x_1258_ == 0)
{
lean_del_object(v___x_1250_);
lean_dec(v_stopPos_1248_);
lean_dec(v_startPos_1247_);
lean_dec_ref(v_str_1246_);
v___y_1243_ = v___x_1255_;
goto v___jp_1242_;
}
else
{
lean_object* v___x_1260_; 
if (v_isShared_1251_ == 0)
{
v___x_1260_ = v___x_1250_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_str_1246_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_startPos_1247_);
lean_ctor_set(v_reuseFailAlloc_1261_, 2, v_stopPos_1248_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
v___y_1237_ = v___x_1255_;
v___y_1238_ = v___x_1260_;
goto v___jp_1236_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0(lean_object* v___y_1292_, lean_object* v_inst_1293_, lean_object* v_R_1294_, lean_object* v_a_1295_, lean_object* v_b_1296_, lean_object* v_c_1297_){
_start:
{
lean_object* v___x_1298_; 
v___x_1298_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(v___y_1292_, v_a_1295_, v_b_1296_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___boxed(lean_object* v___y_1299_, lean_object* v_inst_1300_, lean_object* v_R_1301_, lean_object* v_a_1302_, lean_object* v_b_1303_, lean_object* v_c_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0(v___y_1299_, v_inst_1300_, v_R_1301_, v_a_1302_, v_b_1303_, v_c_1304_);
lean_dec_ref(v___y_1299_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1(lean_object* v___x_1306_, lean_object* v___y_1307_, lean_object* v_inst_1308_, lean_object* v_R_1309_, lean_object* v_a_1310_, lean_object* v_b_1311_, lean_object* v_c_1312_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(v___x_1306_, v___y_1307_, v_a_1310_, v_b_1311_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___boxed(lean_object* v___x_1314_, lean_object* v___y_1315_, lean_object* v_inst_1316_, lean_object* v_R_1317_, lean_object* v_a_1318_, lean_object* v_b_1319_, lean_object* v_c_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1(v___x_1314_, v___y_1315_, v_inst_1316_, v_R_1317_, v_a_1318_, v_b_1319_, v_c_1320_);
lean_dec_ref(v___y_1315_);
lean_dec(v___x_1314_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_repair(lean_object* v_x_1322_){
_start:
{
lean_object* v_str_1323_; lean_object* v_startPos_1324_; lean_object* v_stopPos_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1341_; 
v_str_1323_ = lean_ctor_get(v_x_1322_, 0);
v_startPos_1324_ = lean_ctor_get(v_x_1322_, 1);
v_stopPos_1325_ = lean_ctor_get(v_x_1322_, 2);
v_isSharedCheck_1341_ = !lean_is_exclusive(v_x_1322_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1327_ = v_x_1322_;
v_isShared_1328_ = v_isSharedCheck_1341_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_stopPos_1325_);
lean_inc(v_startPos_1324_);
lean_inc(v_str_1323_);
lean_dec(v_x_1322_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1341_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___y_1330_; uint8_t v___x_1339_; 
v___x_1339_ = lean_string_is_valid_pos(v_str_1323_, v_startPos_1324_);
if (v___x_1339_ == 0)
{
lean_object* v___x_1340_; 
lean_dec(v_startPos_1324_);
v___x_1340_ = lean_string_utf8_byte_size(v_str_1323_);
v___y_1330_ = v___x_1340_;
goto v___jp_1329_;
}
else
{
v___y_1330_ = v_startPos_1324_;
goto v___jp_1329_;
}
v___jp_1329_:
{
uint8_t v___x_1331_; 
v___x_1331_ = lean_string_is_valid_pos(v_str_1323_, v_stopPos_1325_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; lean_object* v___x_1334_; 
lean_dec(v_stopPos_1325_);
v___x_1332_ = lean_string_utf8_byte_size(v_str_1323_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 2, v___x_1332_);
lean_ctor_set(v___x_1327_, 1, v___y_1330_);
v___x_1334_ = v___x_1327_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_str_1323_);
lean_ctor_set(v_reuseFailAlloc_1335_, 1, v___y_1330_);
lean_ctor_set(v_reuseFailAlloc_1335_, 2, v___x_1332_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
else
{
lean_object* v___x_1337_; 
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 1, v___y_1330_);
v___x_1337_ = v___x_1327_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_str_1323_);
lean_ctor_set(v_reuseFailAlloc_1338_, 1, v___y_1330_);
lean_ctor_set(v_reuseFailAlloc_1338_, 2, v_stopPos_1325_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_beq(lean_object* v_ss1_1342_, lean_object* v_ss2_1343_){
_start:
{
lean_object* v_ss1_1344_; lean_object* v_str_1345_; lean_object* v_startPos_1346_; lean_object* v_stopPos_1347_; lean_object* v_ss2_1348_; lean_object* v_str_1349_; lean_object* v_startPos_1350_; lean_object* v_stopPos_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; uint8_t v___x_1354_; 
v_ss1_1344_ = l_Substring_Raw_repair(v_ss1_1342_);
v_str_1345_ = lean_ctor_get(v_ss1_1344_, 0);
lean_inc_ref(v_str_1345_);
v_startPos_1346_ = lean_ctor_get(v_ss1_1344_, 1);
lean_inc(v_startPos_1346_);
v_stopPos_1347_ = lean_ctor_get(v_ss1_1344_, 2);
lean_inc(v_stopPos_1347_);
lean_dec_ref(v_ss1_1344_);
v_ss2_1348_ = l_Substring_Raw_repair(v_ss2_1343_);
v_str_1349_ = lean_ctor_get(v_ss2_1348_, 0);
lean_inc_ref(v_str_1349_);
v_startPos_1350_ = lean_ctor_get(v_ss2_1348_, 1);
lean_inc(v_startPos_1350_);
v_stopPos_1351_ = lean_ctor_get(v_ss2_1348_, 2);
lean_inc(v_stopPos_1351_);
lean_dec_ref(v_ss2_1348_);
v___x_1352_ = lean_nat_sub(v_stopPos_1347_, v_startPos_1346_);
lean_dec(v_stopPos_1347_);
v___x_1353_ = lean_nat_sub(v_stopPos_1351_, v_startPos_1350_);
lean_dec(v_stopPos_1351_);
v___x_1354_ = lean_nat_dec_eq(v___x_1352_, v___x_1353_);
lean_dec(v___x_1353_);
if (v___x_1354_ == 0)
{
lean_dec(v___x_1352_);
lean_dec(v_startPos_1350_);
lean_dec_ref(v_str_1349_);
lean_dec(v_startPos_1346_);
lean_dec_ref(v_str_1345_);
return v___x_1354_;
}
else
{
uint8_t v___x_1355_; 
v___x_1355_ = l_String_Pos_Raw_substrEq(v_str_1345_, v_startPos_1346_, v_str_1349_, v_startPos_1350_, v___x_1352_);
lean_dec(v___x_1352_);
lean_dec_ref(v_str_1349_);
lean_dec_ref(v_str_1345_);
return v___x_1355_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_beq___boxed(lean_object* v_ss1_1356_, lean_object* v_ss2_1357_){
_start:
{
uint8_t v_res_1358_; lean_object* v_r_1359_; 
v_res_1358_ = l_Substring_Raw_beq(v_ss1_1356_, v_ss2_1357_);
v_r_1359_ = lean_box(v_res_1358_);
return v_r_1359_;
}
}
LEAN_EXPORT uint8_t lean_substring_beq(lean_object* v_ss1_1360_, lean_object* v_ss2_1361_){
_start:
{
uint8_t v___x_1362_; 
v___x_1362_ = l_Substring_Raw_beq(v_ss1_1360_, v_ss2_1361_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_beqImpl___boxed(lean_object* v_ss1_1363_, lean_object* v_ss2_1364_){
_start:
{
uint8_t v_res_1365_; lean_object* v_r_1366_; 
v_res_1365_ = lean_substring_beq(v_ss1_1363_, v_ss2_1364_);
v_r_1366_ = lean_box(v_res_1365_);
return v_r_1366_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_sameAs(lean_object* v_ss1_1369_, lean_object* v_ss2_1370_){
_start:
{
lean_object* v_startPos_1371_; lean_object* v_startPos_1372_; uint8_t v___x_1373_; 
v_startPos_1371_ = lean_ctor_get(v_ss1_1369_, 1);
v_startPos_1372_ = lean_ctor_get(v_ss2_1370_, 1);
v___x_1373_ = lean_nat_dec_eq(v_startPos_1371_, v_startPos_1372_);
if (v___x_1373_ == 0)
{
lean_dec_ref(v_ss2_1370_);
lean_dec_ref(v_ss1_1369_);
return v___x_1373_;
}
else
{
uint8_t v___x_1374_; 
v___x_1374_ = l_Substring_Raw_beq(v_ss1_1369_, v_ss2_1370_);
return v___x_1374_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_sameAs___boxed(lean_object* v_ss1_1375_, lean_object* v_ss2_1376_){
_start:
{
uint8_t v_res_1377_; lean_object* v_r_1378_; 
v_res_1377_ = l_Substring_Raw_sameAs(v_ss1_1375_, v_ss2_1376_);
v_r_1378_ = lean_box(v_res_1377_);
return v_r_1378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(lean_object* v_s_1379_, lean_object* v_t_1380_, lean_object* v_spos_1381_, lean_object* v_tpos_1382_){
_start:
{
lean_object* v_str_1383_; lean_object* v_stopPos_1384_; uint8_t v___x_1385_; 
v_str_1383_ = lean_ctor_get(v_s_1379_, 0);
v_stopPos_1384_ = lean_ctor_get(v_s_1379_, 2);
v___x_1385_ = lean_nat_dec_lt(v_spos_1381_, v_stopPos_1384_);
if (v___x_1385_ == 0)
{
lean_dec(v_tpos_1382_);
return v_spos_1381_;
}
else
{
lean_object* v_str_1386_; lean_object* v_stopPos_1387_; uint8_t v___x_1388_; 
v_str_1386_ = lean_ctor_get(v_t_1380_, 0);
v_stopPos_1387_ = lean_ctor_get(v_t_1380_, 2);
v___x_1388_ = lean_nat_dec_lt(v_tpos_1382_, v_stopPos_1387_);
if (v___x_1388_ == 0)
{
lean_dec(v_tpos_1382_);
return v_spos_1381_;
}
else
{
uint32_t v___x_1389_; uint32_t v___x_1390_; uint8_t v___x_1391_; 
v___x_1389_ = lean_string_utf8_get(v_str_1383_, v_spos_1381_);
v___x_1390_ = lean_string_utf8_get(v_str_1386_, v_tpos_1382_);
v___x_1391_ = lean_uint32_dec_eq(v___x_1389_, v___x_1390_);
if (v___x_1391_ == 0)
{
lean_dec(v_tpos_1382_);
return v_spos_1381_;
}
else
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = lean_string_utf8_next(v_str_1383_, v_spos_1381_);
lean_dec(v_spos_1381_);
v___x_1393_ = lean_string_utf8_next(v_str_1386_, v_tpos_1382_);
lean_dec(v_tpos_1382_);
v_spos_1381_ = v___x_1392_;
v_tpos_1382_ = v___x_1393_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop___boxed(lean_object* v_s_1395_, lean_object* v_t_1396_, lean_object* v_spos_1397_, lean_object* v_tpos_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(v_s_1395_, v_t_1396_, v_spos_1397_, v_tpos_1398_);
lean_dec_ref(v_t_1396_);
lean_dec_ref(v_s_1395_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_commonPrefix(lean_object* v_s_1400_, lean_object* v_t_1401_){
_start:
{
lean_object* v_str_1402_; lean_object* v_startPos_1403_; lean_object* v_startPos_1404_; lean_object* v___x_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
v_str_1402_ = lean_ctor_get(v_s_1400_, 0);
lean_inc_ref(v_str_1402_);
v_startPos_1403_ = lean_ctor_get(v_s_1400_, 1);
lean_inc_n(v_startPos_1403_, 2);
v_startPos_1404_ = lean_ctor_get(v_t_1401_, 1);
lean_inc(v_startPos_1404_);
v___x_1405_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(v_s_1400_, v_t_1401_, v_startPos_1403_, v_startPos_1404_);
lean_dec_ref(v_s_1400_);
v_isSharedCheck_1412_ = !lean_is_exclusive(v_t_1401_);
if (v_isSharedCheck_1412_ == 0)
{
lean_object* v_unused_1413_; lean_object* v_unused_1414_; lean_object* v_unused_1415_; 
v_unused_1413_ = lean_ctor_get(v_t_1401_, 2);
lean_dec(v_unused_1413_);
v_unused_1414_ = lean_ctor_get(v_t_1401_, 1);
lean_dec(v_unused_1414_);
v_unused_1415_ = lean_ctor_get(v_t_1401_, 0);
lean_dec(v_unused_1415_);
v___x_1407_ = v_t_1401_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_dec(v_t_1401_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 2, v___x_1405_);
lean_ctor_set(v___x_1407_, 1, v_startPos_1403_);
lean_ctor_set(v___x_1407_, 0, v_str_1402_);
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_str_1402_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v_startPos_1403_);
lean_ctor_set(v_reuseFailAlloc_1411_, 2, v___x_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(lean_object* v_s_1416_, lean_object* v_t_1417_, lean_object* v_spos_1418_, lean_object* v_tpos_1419_){
_start:
{
lean_object* v_str_1420_; lean_object* v_startPos_1421_; uint8_t v___x_1422_; 
v_str_1420_ = lean_ctor_get(v_s_1416_, 0);
v_startPos_1421_ = lean_ctor_get(v_s_1416_, 1);
v___x_1422_ = lean_nat_dec_lt(v_startPos_1421_, v_spos_1418_);
if (v___x_1422_ == 0)
{
lean_dec(v_tpos_1419_);
return v_spos_1418_;
}
else
{
lean_object* v_str_1423_; lean_object* v_startPos_1424_; uint8_t v___x_1425_; 
v_str_1423_ = lean_ctor_get(v_t_1417_, 0);
v_startPos_1424_ = lean_ctor_get(v_t_1417_, 1);
v___x_1425_ = lean_nat_dec_lt(v_startPos_1424_, v_tpos_1419_);
if (v___x_1425_ == 0)
{
lean_dec(v_tpos_1419_);
return v_spos_1418_;
}
else
{
lean_object* v_spos_x27_1426_; lean_object* v_tpos_x27_1427_; uint32_t v___x_1428_; uint32_t v___x_1429_; uint8_t v___x_1430_; 
v_spos_x27_1426_ = lean_string_utf8_prev(v_str_1420_, v_spos_1418_);
v_tpos_x27_1427_ = lean_string_utf8_prev(v_str_1423_, v_tpos_1419_);
lean_dec(v_tpos_1419_);
v___x_1428_ = lean_string_utf8_get(v_str_1420_, v_spos_x27_1426_);
v___x_1429_ = lean_string_utf8_get(v_str_1423_, v_tpos_x27_1427_);
v___x_1430_ = lean_uint32_dec_eq(v___x_1428_, v___x_1429_);
if (v___x_1430_ == 0)
{
lean_dec(v_tpos_x27_1427_);
lean_dec(v_spos_x27_1426_);
return v_spos_1418_;
}
else
{
lean_dec(v_spos_1418_);
v_spos_1418_ = v_spos_x27_1426_;
v_tpos_1419_ = v_tpos_x27_1427_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop___boxed(lean_object* v_s_1432_, lean_object* v_t_1433_, lean_object* v_spos_1434_, lean_object* v_tpos_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(v_s_1432_, v_t_1433_, v_spos_1434_, v_tpos_1435_);
lean_dec_ref(v_t_1433_);
lean_dec_ref(v_s_1432_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_commonSuffix(lean_object* v_s_1437_, lean_object* v_t_1438_){
_start:
{
lean_object* v_str_1439_; lean_object* v_stopPos_1440_; lean_object* v_stopPos_1441_; lean_object* v___x_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
v_str_1439_ = lean_ctor_get(v_s_1437_, 0);
lean_inc_ref(v_str_1439_);
v_stopPos_1440_ = lean_ctor_get(v_s_1437_, 2);
lean_inc_n(v_stopPos_1440_, 2);
v_stopPos_1441_ = lean_ctor_get(v_t_1438_, 2);
lean_inc(v_stopPos_1441_);
v___x_1442_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(v_s_1437_, v_t_1438_, v_stopPos_1440_, v_stopPos_1441_);
lean_dec_ref(v_s_1437_);
v_isSharedCheck_1449_ = !lean_is_exclusive(v_t_1438_);
if (v_isSharedCheck_1449_ == 0)
{
lean_object* v_unused_1450_; lean_object* v_unused_1451_; lean_object* v_unused_1452_; 
v_unused_1450_ = lean_ctor_get(v_t_1438_, 2);
lean_dec(v_unused_1450_);
v_unused_1451_ = lean_ctor_get(v_t_1438_, 1);
lean_dec(v_unused_1451_);
v_unused_1452_ = lean_ctor_get(v_t_1438_, 0);
lean_dec(v_unused_1452_);
v___x_1444_ = v_t_1438_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_dec(v_t_1438_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 2, v_stopPos_1440_);
lean_ctor_set(v___x_1444_, 1, v___x_1442_);
lean_ctor_set(v___x_1444_, 0, v_str_1439_);
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_str_1439_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1448_, 2, v_stopPos_1440_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropPrefix_x3f(lean_object* v_s_1453_, lean_object* v_pre_1454_){
_start:
{
lean_object* v_t_1455_; lean_object* v_startPos_1456_; lean_object* v_stopPos_1457_; lean_object* v_startPos_1458_; lean_object* v_stopPos_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; uint8_t v___x_1462_; 
lean_inc_ref(v_pre_1454_);
lean_inc_ref(v_s_1453_);
v_t_1455_ = l_Substring_Raw_commonPrefix(v_s_1453_, v_pre_1454_);
v_startPos_1456_ = lean_ctor_get(v_t_1455_, 1);
lean_inc(v_startPos_1456_);
v_stopPos_1457_ = lean_ctor_get(v_t_1455_, 2);
lean_inc(v_stopPos_1457_);
lean_dec_ref(v_t_1455_);
v_startPos_1458_ = lean_ctor_get(v_pre_1454_, 1);
lean_inc(v_startPos_1458_);
v_stopPos_1459_ = lean_ctor_get(v_pre_1454_, 2);
lean_inc(v_stopPos_1459_);
lean_dec_ref(v_pre_1454_);
v___x_1460_ = lean_nat_sub(v_stopPos_1457_, v_startPos_1456_);
lean_dec(v_startPos_1456_);
v___x_1461_ = lean_nat_sub(v_stopPos_1459_, v_startPos_1458_);
lean_dec(v_startPos_1458_);
lean_dec(v_stopPos_1459_);
v___x_1462_ = lean_nat_dec_eq(v___x_1460_, v___x_1461_);
lean_dec(v___x_1461_);
lean_dec(v___x_1460_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; 
lean_dec(v_stopPos_1457_);
lean_dec_ref(v_s_1453_);
v___x_1463_ = lean_box(0);
return v___x_1463_;
}
else
{
lean_object* v_str_1464_; lean_object* v_stopPos_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1473_; 
v_str_1464_ = lean_ctor_get(v_s_1453_, 0);
v_stopPos_1465_ = lean_ctor_get(v_s_1453_, 2);
v_isSharedCheck_1473_ = !lean_is_exclusive(v_s_1453_);
if (v_isSharedCheck_1473_ == 0)
{
lean_object* v_unused_1474_; 
v_unused_1474_ = lean_ctor_get(v_s_1453_, 1);
lean_dec(v_unused_1474_);
v___x_1467_ = v_s_1453_;
v_isShared_1468_ = v_isSharedCheck_1473_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_stopPos_1465_);
lean_inc(v_str_1464_);
lean_dec(v_s_1453_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1473_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 1, v_stopPos_1457_);
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_str_1464_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v_stopPos_1457_);
lean_ctor_set(v_reuseFailAlloc_1472_, 2, v_stopPos_1465_);
v___x_1470_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
lean_object* v___x_1471_; 
v___x_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
return v___x_1471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropSuffix_x3f(lean_object* v_s_1475_, lean_object* v_suff_1476_){
_start:
{
lean_object* v_t_1477_; lean_object* v_startPos_1478_; lean_object* v_stopPos_1479_; lean_object* v_startPos_1480_; lean_object* v_stopPos_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; uint8_t v___x_1484_; 
lean_inc_ref(v_suff_1476_);
lean_inc_ref(v_s_1475_);
v_t_1477_ = l_Substring_Raw_commonSuffix(v_s_1475_, v_suff_1476_);
v_startPos_1478_ = lean_ctor_get(v_t_1477_, 1);
lean_inc(v_startPos_1478_);
v_stopPos_1479_ = lean_ctor_get(v_t_1477_, 2);
lean_inc(v_stopPos_1479_);
lean_dec_ref(v_t_1477_);
v_startPos_1480_ = lean_ctor_get(v_suff_1476_, 1);
lean_inc(v_startPos_1480_);
v_stopPos_1481_ = lean_ctor_get(v_suff_1476_, 2);
lean_inc(v_stopPos_1481_);
lean_dec_ref(v_suff_1476_);
v___x_1482_ = lean_nat_sub(v_stopPos_1479_, v_startPos_1478_);
lean_dec(v_stopPos_1479_);
v___x_1483_ = lean_nat_sub(v_stopPos_1481_, v_startPos_1480_);
lean_dec(v_startPos_1480_);
lean_dec(v_stopPos_1481_);
v___x_1484_ = lean_nat_dec_eq(v___x_1482_, v___x_1483_);
lean_dec(v___x_1483_);
lean_dec(v___x_1482_);
if (v___x_1484_ == 0)
{
lean_object* v___x_1485_; 
lean_dec(v_startPos_1478_);
lean_dec_ref(v_s_1475_);
v___x_1485_ = lean_box(0);
return v___x_1485_;
}
else
{
lean_object* v_str_1486_; lean_object* v_startPos_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1495_; 
v_str_1486_ = lean_ctor_get(v_s_1475_, 0);
v_startPos_1487_ = lean_ctor_get(v_s_1475_, 1);
v_isSharedCheck_1495_ = !lean_is_exclusive(v_s_1475_);
if (v_isSharedCheck_1495_ == 0)
{
lean_object* v_unused_1496_; 
v_unused_1496_ = lean_ctor_get(v_s_1475_, 2);
lean_dec(v_unused_1496_);
v___x_1489_ = v_s_1475_;
v_isShared_1490_ = v_isSharedCheck_1495_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_startPos_1487_);
lean_inc(v_str_1486_);
lean_dec(v_s_1475_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1495_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 2, v_startPos_1478_);
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_str_1486_);
lean_ctor_set(v_reuseFailAlloc_1494_, 1, v_startPos_1487_);
lean_ctor_set(v_reuseFailAlloc_1494_, 2, v_startPos_1478_);
v___x_1492_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
lean_object* v___x_1493_; 
v___x_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1492_);
return v___x_1493_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg(lean_object* v_x_1497_, lean_object* v_x_1498_, lean_object* v_x_1499_, lean_object* v_h__1_1500_, lean_object* v_h__2_1501_){
_start:
{
lean_object* v_zero_1502_; uint8_t v_isZero_1503_; 
v_zero_1502_ = lean_unsigned_to_nat(0u);
v_isZero_1503_ = lean_nat_dec_eq(v_x_1498_, v_zero_1502_);
if (v_isZero_1503_ == 1)
{
lean_object* v___x_1504_; 
lean_dec(v_h__2_1501_);
v___x_1504_ = lean_apply_2(v_h__1_1500_, v_x_1497_, v_x_1499_);
return v___x_1504_;
}
else
{
lean_object* v_one_1505_; lean_object* v_n_1506_; lean_object* v___x_1507_; 
lean_dec(v_h__1_1500_);
v_one_1505_ = lean_unsigned_to_nat(1u);
v_n_1506_ = lean_nat_sub(v_x_1498_, v_one_1505_);
v___x_1507_ = lean_apply_3(v_h__2_1501_, v_x_1497_, v_n_1506_, v_x_1499_);
return v___x_1507_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg___boxed(lean_object* v_x_1508_, lean_object* v_x_1509_, lean_object* v_x_1510_, lean_object* v_h__1_1511_, lean_object* v_h__2_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg(v_x_1508_, v_x_1509_, v_x_1510_, v_h__1_1511_, v_h__2_1512_);
lean_dec(v_x_1509_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter(lean_object* v_motive_1514_, lean_object* v_x_1515_, lean_object* v_x_1516_, lean_object* v_x_1517_, lean_object* v_h__1_1518_, lean_object* v_h__2_1519_){
_start:
{
lean_object* v_zero_1520_; uint8_t v_isZero_1521_; 
v_zero_1520_ = lean_unsigned_to_nat(0u);
v_isZero_1521_ = lean_nat_dec_eq(v_x_1516_, v_zero_1520_);
if (v_isZero_1521_ == 1)
{
lean_object* v___x_1522_; 
lean_dec(v_h__2_1519_);
v___x_1522_ = lean_apply_2(v_h__1_1518_, v_x_1515_, v_x_1517_);
return v___x_1522_;
}
else
{
lean_object* v_one_1523_; lean_object* v_n_1524_; lean_object* v___x_1525_; 
lean_dec(v_h__1_1518_);
v_one_1523_ = lean_unsigned_to_nat(1u);
v_n_1524_ = lean_nat_sub(v_x_1516_, v_one_1523_);
v___x_1525_ = lean_apply_3(v_h__2_1519_, v_x_1515_, v_n_1524_, v_x_1517_);
return v___x_1525_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___boxed(lean_object* v_motive_1526_, lean_object* v_x_1527_, lean_object* v_x_1528_, lean_object* v_x_1529_, lean_object* v_h__1_1530_, lean_object* v_h__2_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter(v_motive_1526_, v_x_1527_, v_x_1528_, v_x_1529_, v_h__1_1530_, v_h__2_1531_);
lean_dec(v_x_1528_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_Substring_bsize(lean_object* v_a_1533_){
_start:
{
lean_object* v_startPos_1534_; lean_object* v_stopPos_1535_; lean_object* v___x_1536_; 
v_startPos_1534_ = lean_ctor_get(v_a_1533_, 1);
v_stopPos_1535_ = lean_ctor_get(v_a_1533_, 2);
v___x_1536_ = lean_nat_sub(v_stopPos_1535_, v_startPos_1534_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Substring_bsize___boxed(lean_object* v_a_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Substring_bsize(v_a_1537_);
lean_dec_ref(v_a_1537_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Substring_toString(lean_object* v_a_1539_){
_start:
{
lean_object* v_str_1540_; lean_object* v_startPos_1541_; lean_object* v_stopPos_1542_; lean_object* v___x_1543_; 
v_str_1540_ = lean_ctor_get(v_a_1539_, 0);
v_startPos_1541_ = lean_ctor_get(v_a_1539_, 1);
v_stopPos_1542_ = lean_ctor_get(v_a_1539_, 2);
v___x_1543_ = lean_string_utf8_extract(v_str_1540_, v_startPos_1541_, v_stopPos_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Substring_toString___boxed(lean_object* v_a_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Substring_toString(v_a_1544_);
lean_dec_ref(v_a_1544_);
return v_res_1545_;
}
}
LEAN_EXPORT uint8_t l_Substring_isEmpty(lean_object* v_ss_1546_){
_start:
{
lean_object* v_startPos_1547_; lean_object* v_stopPos_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; uint8_t v___x_1551_; 
v_startPos_1547_ = lean_ctor_get(v_ss_1546_, 1);
v_stopPos_1548_ = lean_ctor_get(v_ss_1546_, 2);
v___x_1549_ = lean_nat_sub(v_stopPos_1548_, v_startPos_1547_);
v___x_1550_ = lean_unsigned_to_nat(0u);
v___x_1551_ = lean_nat_dec_eq(v___x_1549_, v___x_1550_);
lean_dec(v___x_1549_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Substring_isEmpty___boxed(lean_object* v_ss_1552_){
_start:
{
uint8_t v_res_1553_; lean_object* v_r_1554_; 
v_res_1553_ = l_Substring_isEmpty(v_ss_1552_);
lean_dec_ref(v_ss_1552_);
v_r_1554_ = lean_box(v_res_1553_);
return v_r_1554_;
}
}
LEAN_EXPORT lean_object* l_Substring_next(lean_object* v_a_1555_, lean_object* v_a_1556_){
_start:
{
lean_object* v_str_1557_; lean_object* v_startPos_1558_; lean_object* v_stopPos_1559_; lean_object* v_absP_1560_; uint8_t v___x_1561_; 
v_str_1557_ = lean_ctor_get(v_a_1555_, 0);
v_startPos_1558_ = lean_ctor_get(v_a_1555_, 1);
v_stopPos_1559_ = lean_ctor_get(v_a_1555_, 2);
v_absP_1560_ = lean_nat_add(v_startPos_1558_, v_a_1556_);
v___x_1561_ = lean_nat_dec_eq(v_absP_1560_, v_stopPos_1559_);
if (v___x_1561_ == 0)
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1562_ = lean_string_utf8_next(v_str_1557_, v_absP_1560_);
lean_dec(v_absP_1560_);
v___x_1563_ = lean_nat_sub(v___x_1562_, v_startPos_1558_);
lean_dec(v___x_1562_);
return v___x_1563_;
}
else
{
lean_dec(v_absP_1560_);
lean_inc(v_a_1556_);
return v_a_1556_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_next___boxed(lean_object* v_a_1564_, lean_object* v_a_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Substring_next(v_a_1564_, v_a_1565_);
lean_dec(v_a_1565_);
lean_dec_ref(v_a_1564_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Substring_prev(lean_object* v_a_1567_, lean_object* v_a_1568_){
_start:
{
lean_object* v_str_1569_; lean_object* v_startPos_1570_; lean_object* v_absP_1571_; uint8_t v___x_1572_; 
v_str_1569_ = lean_ctor_get(v_a_1567_, 0);
v_startPos_1570_ = lean_ctor_get(v_a_1567_, 1);
v_absP_1571_ = lean_nat_add(v_startPos_1570_, v_a_1568_);
v___x_1572_ = lean_nat_dec_eq(v_absP_1571_, v_startPos_1570_);
if (v___x_1572_ == 0)
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = lean_string_utf8_prev(v_str_1569_, v_absP_1571_);
lean_dec(v_absP_1571_);
v___x_1574_ = lean_nat_sub(v___x_1573_, v_startPos_1570_);
lean_dec(v___x_1573_);
return v___x_1574_;
}
else
{
lean_dec(v_absP_1571_);
lean_inc(v_a_1568_);
return v_a_1568_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_prev___boxed(lean_object* v_a_1575_, lean_object* v_a_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l_Substring_prev(v_a_1575_, v_a_1576_);
lean_dec(v_a_1576_);
lean_dec_ref(v_a_1575_);
return v_res_1577_;
}
}
LEAN_EXPORT uint8_t l_Substring_atEnd(lean_object* v_a_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v_startPos_1580_; lean_object* v_stopPos_1581_; lean_object* v___x_1582_; uint8_t v___x_1583_; 
v_startPos_1580_ = lean_ctor_get(v_a_1578_, 1);
v_stopPos_1581_ = lean_ctor_get(v_a_1578_, 2);
v___x_1582_ = lean_nat_add(v_startPos_1580_, v_a_1579_);
v___x_1583_ = lean_nat_dec_eq(v___x_1582_, v_stopPos_1581_);
lean_dec(v___x_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Substring_atEnd___boxed(lean_object* v_a_1584_, lean_object* v_a_1585_){
_start:
{
uint8_t v_res_1586_; lean_object* v_r_1587_; 
v_res_1586_ = l_Substring_atEnd(v_a_1584_, v_a_1585_);
lean_dec(v_a_1585_);
lean_dec_ref(v_a_1584_);
v_r_1587_ = lean_box(v_res_1586_);
return v_r_1587_;
}
}
LEAN_EXPORT uint8_t l_Substring_beq(lean_object* v_ss1_1588_, lean_object* v_ss2_1589_){
_start:
{
uint8_t v___x_1590_; 
v___x_1590_ = l_Substring_Raw_beq(v_ss1_1588_, v_ss2_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Substring_beq___boxed(lean_object* v_ss1_1591_, lean_object* v_ss2_1592_){
_start:
{
uint8_t v_res_1593_; lean_object* v_r_1594_; 
v_res_1593_ = l_Substring_beq(v_ss1_1591_, v_ss2_1592_);
v_r_1594_ = lean_box(v_res_1593_);
return v_r_1594_;
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

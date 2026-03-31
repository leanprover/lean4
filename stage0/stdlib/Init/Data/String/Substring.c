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
uint8_t l_String_instDecidableLtRaw___aux__1(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
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
lean_dec_ref(v___x_223_);
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
v___x_419_ = lean_nat_add(v_startPos_412_, v___y_416_);
lean_dec(v___y_416_);
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
v___y_407_ = v___y_417_;
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
v___y_407_ = v___y_417_;
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
v___y_416_ = v___x_429_;
v___y_417_ = v___x_428_;
v___y_418_ = v___x_431_;
goto v___jp_414_;
}
else
{
lean_dec(v___x_431_);
lean_inc(v_stopPos_413_);
v___y_415_ = v___y_424_;
v___y_416_ = v___x_429_;
v___y_417_ = v___x_428_;
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
lean_object* v___y_705_; lean_object* v_startInclusive_706_; lean_object* v_endExclusive_707_; lean_object* v_str_714_; lean_object* v_startPos_715_; lean_object* v_stopPos_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_732_; 
v_str_714_ = lean_ctor_get(v_s_702_, 0);
v_startPos_715_ = lean_ctor_get(v_s_702_, 1);
v_stopPos_716_ = lean_ctor_get(v_s_702_, 2);
v_isSharedCheck_732_ = !lean_is_exclusive(v_s_702_);
if (v_isSharedCheck_732_ == 0)
{
v___x_718_ = v_s_702_;
v_isShared_719_ = v_isSharedCheck_732_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_stopPos_716_);
lean_inc(v_startPos_715_);
lean_inc(v_str_714_);
lean_dec(v_s_702_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_732_;
goto v_resetjp_717_;
}
v___jp_704_:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_708_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v_p_703_);
v___x_709_ = lean_unsigned_to_nat(0u);
v___x_710_ = l_String_Slice_Pos_skipWhile___redArg(v___y_705_, v___x_709_, v___x_708_);
lean_dec_ref(v___y_705_);
v___x_711_ = lean_nat_add(v_startInclusive_706_, v___x_710_);
lean_dec(v___x_710_);
lean_dec(v_startInclusive_706_);
v___x_712_ = lean_nat_sub(v_endExclusive_707_, v___x_711_);
lean_dec(v___x_711_);
lean_dec(v_endExclusive_707_);
v___x_713_ = lean_nat_dec_eq(v___x_712_, v___x_709_);
lean_dec(v___x_712_);
return v___x_713_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; uint8_t v___x_726_; 
v___x_720_ = l_String_instInhabitedSlice;
v___x_726_ = lean_string_is_valid_pos(v_str_714_, v_startPos_715_);
if (v___x_726_ == 0)
{
lean_del_object(v___x_718_);
lean_dec(v_stopPos_716_);
lean_dec(v_startPos_715_);
lean_dec_ref(v_str_714_);
goto v___jp_721_;
}
else
{
uint8_t v___x_727_; 
v___x_727_ = lean_string_is_valid_pos(v_str_714_, v_stopPos_716_);
if (v___x_727_ == 0)
{
lean_del_object(v___x_718_);
lean_dec(v_stopPos_716_);
lean_dec(v_startPos_715_);
lean_dec_ref(v_str_714_);
goto v___jp_721_;
}
else
{
uint8_t v___x_728_; 
v___x_728_ = lean_nat_dec_le(v_startPos_715_, v_stopPos_716_);
if (v___x_728_ == 0)
{
lean_del_object(v___x_718_);
lean_dec(v_stopPos_716_);
lean_dec(v_startPos_715_);
lean_dec_ref(v_str_714_);
goto v___jp_721_;
}
else
{
lean_object* v___x_730_; 
lean_inc(v_stopPos_716_);
lean_inc(v_startPos_715_);
if (v_isShared_719_ == 0)
{
v___x_730_ = v___x_718_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_str_714_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_startPos_715_);
lean_ctor_set(v_reuseFailAlloc_731_, 2, v_stopPos_716_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
v___y_705_ = v___x_730_;
v_startInclusive_706_ = v_startPos_715_;
v_endExclusive_707_ = v_stopPos_716_;
goto v___jp_704_;
}
}
}
}
v___jp_721_:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v_startInclusive_724_; lean_object* v_endExclusive_725_; 
v___x_722_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_723_ = l_panic___redArg(v___x_720_, v___x_722_);
v_startInclusive_724_ = lean_ctor_get(v___x_723_, 1);
lean_inc(v_startInclusive_724_);
v_endExclusive_725_ = lean_ctor_get(v___x_723_, 2);
lean_inc(v_endExclusive_725_);
v___y_705_ = v___x_723_;
v_startInclusive_706_ = v_startInclusive_724_;
v_endExclusive_707_ = v_endExclusive_725_;
goto v___jp_704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_all___boxed(lean_object* v_s_733_, lean_object* v_p_734_){
_start:
{
uint8_t v_res_735_; lean_object* v_r_736_; 
v_res_735_ = l_Substring_Raw_all(v_s_733_, v_p_734_);
v_r_736_ = lean_box(v_res_735_);
return v_r_736_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(lean_object* v_msg_737_){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_738_ = l_String_instInhabitedSlice;
v___x_739_ = lean_panic_fn_borrowed(v___x_738_, v_msg_737_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0(lean_object* v_p_740_, lean_object* v_s_741_, lean_object* v_pos_742_){
_start:
{
lean_object* v_str_743_; lean_object* v_startInclusive_744_; lean_object* v_endExclusive_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; uint8_t v___x_749_; 
v_str_743_ = lean_ctor_get(v_s_741_, 0);
v_startInclusive_744_ = lean_ctor_get(v_s_741_, 1);
v_endExclusive_745_ = lean_ctor_get(v_s_741_, 2);
v___x_746_ = lean_nat_add(v_startInclusive_744_, v_pos_742_);
v___x_747_ = lean_unsigned_to_nat(0u);
v___x_748_ = lean_nat_sub(v_endExclusive_745_, v___x_746_);
v___x_749_ = lean_nat_dec_eq(v___x_747_, v___x_748_);
lean_dec(v___x_748_);
if (v___x_749_ == 0)
{
uint32_t v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; uint8_t v___x_753_; 
v___x_750_ = lean_string_utf8_get_fast(v_str_743_, v___x_746_);
v___x_751_ = lean_box_uint32(v___x_750_);
lean_inc_ref(v_p_740_);
v___x_752_ = lean_apply_1(v_p_740_, v___x_751_);
v___x_753_ = lean_unbox(v___x_752_);
if (v___x_753_ == 0)
{
lean_dec(v___x_746_);
lean_dec_ref(v_p_740_);
return v_pos_742_;
}
else
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_754_ = lean_string_utf8_next_fast(v_str_743_, v___x_746_);
v___x_755_ = lean_nat_sub(v___x_754_, v___x_746_);
lean_dec(v___x_746_);
v___x_756_ = lean_nat_add(v_pos_742_, v___x_755_);
lean_dec(v___x_755_);
v___x_757_ = l_String_instDecidableLtRaw___aux__1(v_pos_742_, v___x_756_);
if (v___x_757_ == 0)
{
lean_dec(v___x_756_);
lean_dec_ref(v_p_740_);
return v_pos_742_;
}
else
{
lean_dec(v_pos_742_);
v_pos_742_ = v___x_756_;
goto _start;
}
}
}
else
{
lean_dec(v___x_746_);
lean_dec_ref(v_p_740_);
return v_pos_742_;
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
lean_object* v___y_766_; lean_object* v_startInclusive_767_; lean_object* v_endExclusive_768_; lean_object* v_str_779_; lean_object* v_startPos_780_; lean_object* v_stopPos_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_791_; 
v_str_779_ = lean_ctor_get(v_s_763_, 0);
v_startPos_780_ = lean_ctor_get(v_s_763_, 1);
v_stopPos_781_ = lean_ctor_get(v_s_763_, 2);
v_isSharedCheck_791_ = !lean_is_exclusive(v_s_763_);
if (v_isSharedCheck_791_ == 0)
{
v___x_783_ = v_s_763_;
v_isShared_784_ = v_isSharedCheck_791_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_stopPos_781_);
lean_inc(v_startPos_780_);
lean_inc(v_str_779_);
lean_dec(v_s_763_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_791_;
goto v_resetjp_782_;
}
v___jp_765_:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_769_ = lean_unsigned_to_nat(0u);
v___x_770_ = l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0(v_p_764_, v___y_766_, v___x_769_);
lean_dec_ref(v___y_766_);
v___x_771_ = lean_nat_add(v_startInclusive_767_, v___x_770_);
lean_dec(v___x_770_);
lean_dec(v_startInclusive_767_);
v___x_772_ = lean_nat_sub(v_endExclusive_768_, v___x_771_);
lean_dec(v___x_771_);
lean_dec(v_endExclusive_768_);
v___x_773_ = lean_nat_dec_eq(v___x_772_, v___x_769_);
lean_dec(v___x_772_);
return v___x_773_;
}
v___jp_774_:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v_startInclusive_777_; lean_object* v_endExclusive_778_; 
v___x_775_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_776_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_775_);
v_startInclusive_777_ = lean_ctor_get(v___x_776_, 1);
lean_inc(v_startInclusive_777_);
v_endExclusive_778_ = lean_ctor_get(v___x_776_, 2);
lean_inc(v_endExclusive_778_);
v___y_766_ = v___x_776_;
v_startInclusive_767_ = v_startInclusive_777_;
v_endExclusive_768_ = v_endExclusive_778_;
goto v___jp_765_;
}
v_resetjp_782_:
{
uint8_t v___x_785_; 
v___x_785_ = lean_string_is_valid_pos(v_str_779_, v_startPos_780_);
if (v___x_785_ == 0)
{
lean_del_object(v___x_783_);
lean_dec(v_stopPos_781_);
lean_dec(v_startPos_780_);
lean_dec_ref(v_str_779_);
goto v___jp_774_;
}
else
{
uint8_t v___x_786_; 
v___x_786_ = lean_string_is_valid_pos(v_str_779_, v_stopPos_781_);
if (v___x_786_ == 0)
{
lean_del_object(v___x_783_);
lean_dec(v_stopPos_781_);
lean_dec(v_startPos_780_);
lean_dec_ref(v_str_779_);
goto v___jp_774_;
}
else
{
uint8_t v___x_787_; 
v___x_787_ = lean_nat_dec_le(v_startPos_780_, v_stopPos_781_);
if (v___x_787_ == 0)
{
lean_del_object(v___x_783_);
lean_dec(v_stopPos_781_);
lean_dec(v_startPos_780_);
lean_dec_ref(v_str_779_);
goto v___jp_774_;
}
else
{
lean_object* v___x_789_; 
lean_inc(v_stopPos_781_);
lean_inc(v_startPos_780_);
if (v_isShared_784_ == 0)
{
v___x_789_ = v___x_783_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_str_779_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v_startPos_780_);
lean_ctor_set(v_reuseFailAlloc_790_, 2, v_stopPos_781_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
v___y_766_ = v___x_789_;
v_startInclusive_767_ = v_startPos_780_;
v_endExclusive_768_ = v_stopPos_781_;
goto v___jp_765_;
}
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
lean_object* v___x_807_; lean_object* v___f_808_; lean_object* v___x_809_; lean_object* v_str_810_; lean_object* v_startPos_811_; lean_object* v_stopPos_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_830_; 
v___x_807_ = lean_box_uint32(v_c_806_);
v___f_808_ = lean_alloc_closure((void*)(l_Substring_Raw_contains___lam__0___boxed), 2, 1);
lean_closure_set(v___f_808_, 0, v___x_807_);
lean_inc_ref(v___f_808_);
v___x_809_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___f_808_);
v_str_810_ = lean_ctor_get(v_s_805_, 0);
v_startPos_811_ = lean_ctor_get(v_s_805_, 1);
v_stopPos_812_ = lean_ctor_get(v_s_805_, 2);
v_isSharedCheck_830_ = !lean_is_exclusive(v_s_805_);
if (v_isSharedCheck_830_ == 0)
{
v___x_814_ = v_s_805_;
v_isShared_815_ = v_isSharedCheck_830_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_stopPos_812_);
lean_inc(v_startPos_811_);
lean_inc(v_str_810_);
lean_dec(v_s_805_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_830_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; lean_object* v___f_817_; lean_object* v___x_818_; uint8_t v___x_823_; 
v___x_816_ = l_String_instInhabitedSlice;
v___f_817_ = lean_alloc_closure((void*)(l_Substring_Raw_any___lam__0), 8, 1);
lean_closure_set(v___f_817_, 0, v___x_809_);
v___x_818_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_818_, 0, lean_box(0));
lean_closure_set(v___x_818_, 1, v___f_808_);
v___x_823_ = lean_string_is_valid_pos(v_str_810_, v_startPos_811_);
if (v___x_823_ == 0)
{
lean_del_object(v___x_814_);
lean_dec(v_stopPos_812_);
lean_dec(v_startPos_811_);
lean_dec_ref(v_str_810_);
goto v___jp_819_;
}
else
{
uint8_t v___x_824_; 
v___x_824_ = lean_string_is_valid_pos(v_str_810_, v_stopPos_812_);
if (v___x_824_ == 0)
{
lean_del_object(v___x_814_);
lean_dec(v_stopPos_812_);
lean_dec(v_startPos_811_);
lean_dec_ref(v_str_810_);
goto v___jp_819_;
}
else
{
uint8_t v___x_825_; 
v___x_825_ = lean_nat_dec_le(v_startPos_811_, v_stopPos_812_);
if (v___x_825_ == 0)
{
lean_del_object(v___x_814_);
lean_dec(v_stopPos_812_);
lean_dec(v_startPos_811_);
lean_dec_ref(v_str_810_);
goto v___jp_819_;
}
else
{
lean_object* v___x_827_; 
if (v_isShared_815_ == 0)
{
v___x_827_ = v___x_814_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_str_810_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v_startPos_811_);
lean_ctor_set(v_reuseFailAlloc_829_, 2, v_stopPos_812_);
v___x_827_ = v_reuseFailAlloc_829_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
uint8_t v___x_828_; 
v___x_828_ = l_String_Slice_contains___redArg(v___f_817_, v___x_827_, v___x_818_);
return v___x_828_;
}
}
}
}
v___jp_819_:
{
lean_object* v___x_820_; lean_object* v___x_821_; uint8_t v___x_822_; 
v___x_820_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_821_ = l_panic___redArg(v___x_816_, v___x_820_);
v___x_822_ = l_String_Slice_contains___redArg(v___f_817_, v___x_821_, v___x_818_);
return v___x_822_;
}
}
}
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
uint8_t v___x_840_; 
v___x_840_ = l_String_instDecidableLtRaw___aux__1(v_i_839_, v_stopPos_837_);
if (v___x_840_ == 0)
{
lean_dec_ref(v_p_838_);
return v_i_839_;
}
else
{
uint32_t v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; uint8_t v___x_844_; 
v___x_841_ = lean_string_utf8_get(v_s_836_, v_i_839_);
v___x_842_ = lean_box_uint32(v___x_841_);
lean_inc_ref(v_p_838_);
v___x_843_ = lean_apply_1(v_p_838_, v___x_842_);
v___x_844_ = lean_unbox(v___x_843_);
if (v___x_844_ == 0)
{
lean_dec_ref(v_p_838_);
return v_i_839_;
}
else
{
lean_object* v___x_845_; 
v___x_845_ = lean_string_utf8_next(v_s_836_, v_i_839_);
lean_dec(v_i_839_);
v_i_839_ = v___x_845_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___boxed(lean_object* v_s_847_, lean_object* v_stopPos_848_, lean_object* v_p_849_, lean_object* v_i_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Substring_Raw_takeWhileAux(v_s_847_, v_stopPos_848_, v_p_849_, v_i_850_);
lean_dec(v_stopPos_848_);
lean_dec_ref(v_s_847_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhile(lean_object* v_x_852_, lean_object* v_x_853_){
_start:
{
lean_object* v_str_854_; lean_object* v_startPos_855_; lean_object* v_stopPos_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_864_; 
v_str_854_ = lean_ctor_get(v_x_852_, 0);
v_startPos_855_ = lean_ctor_get(v_x_852_, 1);
v_stopPos_856_ = lean_ctor_get(v_x_852_, 2);
v_isSharedCheck_864_ = !lean_is_exclusive(v_x_852_);
if (v_isSharedCheck_864_ == 0)
{
v___x_858_ = v_x_852_;
v_isShared_859_ = v_isSharedCheck_864_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_stopPos_856_);
lean_inc(v_startPos_855_);
lean_inc(v_str_854_);
lean_dec(v_x_852_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_864_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v_e_860_; lean_object* v___x_862_; 
lean_inc(v_startPos_855_);
v_e_860_ = l_Substring_Raw_takeWhileAux(v_str_854_, v_stopPos_856_, v_x_853_, v_startPos_855_);
lean_dec(v_stopPos_856_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 2, v_e_860_);
v___x_862_ = v___x_858_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_str_854_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v_startPos_855_);
lean_ctor_set(v_reuseFailAlloc_863_, 2, v_e_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(lean_object* v_a_865_, lean_object* v_s_866_, lean_object* v_stopPos_867_, lean_object* v_i_868_){
_start:
{
uint8_t v___x_869_; 
v___x_869_ = l_String_instDecidableLtRaw___aux__1(v_i_868_, v_stopPos_867_);
if (v___x_869_ == 0)
{
lean_dec_ref(v_a_865_);
return v_i_868_;
}
else
{
uint32_t v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; uint8_t v___x_873_; 
v___x_870_ = lean_string_utf8_get(v_s_866_, v_i_868_);
v___x_871_ = lean_box_uint32(v___x_870_);
lean_inc_ref(v_a_865_);
v___x_872_ = lean_apply_1(v_a_865_, v___x_871_);
v___x_873_ = lean_unbox(v___x_872_);
if (v___x_873_ == 0)
{
lean_dec_ref(v_a_865_);
return v_i_868_;
}
else
{
lean_object* v___x_874_; 
v___x_874_ = lean_string_utf8_next(v_s_866_, v_i_868_);
lean_dec(v_i_868_);
v_i_868_ = v___x_874_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0___boxed(lean_object* v_a_876_, lean_object* v_s_877_, lean_object* v_stopPos_878_, lean_object* v_i_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(v_a_876_, v_s_877_, v_stopPos_878_, v_i_879_);
lean_dec(v_stopPos_878_);
lean_dec_ref(v_s_877_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* lean_substring_takewhile(lean_object* v_a_881_, lean_object* v_a_882_){
_start:
{
lean_object* v_str_883_; lean_object* v_startPos_884_; lean_object* v_stopPos_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_893_; 
v_str_883_ = lean_ctor_get(v_a_881_, 0);
v_startPos_884_ = lean_ctor_get(v_a_881_, 1);
v_stopPos_885_ = lean_ctor_get(v_a_881_, 2);
v_isSharedCheck_893_ = !lean_is_exclusive(v_a_881_);
if (v_isSharedCheck_893_ == 0)
{
v___x_887_ = v_a_881_;
v_isShared_888_ = v_isSharedCheck_893_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_stopPos_885_);
lean_inc(v_startPos_884_);
lean_inc(v_str_883_);
lean_dec(v_a_881_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_893_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v_e_889_; lean_object* v___x_891_; 
lean_inc(v_startPos_884_);
v_e_889_ = l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(v_a_882_, v_str_883_, v_stopPos_885_, v_startPos_884_);
lean_dec(v_stopPos_885_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 2, v_e_889_);
v___x_891_ = v___x_887_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_str_883_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_startPos_884_);
lean_ctor_set(v_reuseFailAlloc_892_, 2, v_e_889_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropWhile(lean_object* v_x_894_, lean_object* v_x_895_){
_start:
{
lean_object* v_str_896_; lean_object* v_startPos_897_; lean_object* v_stopPos_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_906_; 
v_str_896_ = lean_ctor_get(v_x_894_, 0);
v_startPos_897_ = lean_ctor_get(v_x_894_, 1);
v_stopPos_898_ = lean_ctor_get(v_x_894_, 2);
v_isSharedCheck_906_ = !lean_is_exclusive(v_x_894_);
if (v_isSharedCheck_906_ == 0)
{
v___x_900_ = v_x_894_;
v_isShared_901_ = v_isSharedCheck_906_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_stopPos_898_);
lean_inc(v_startPos_897_);
lean_inc(v_str_896_);
lean_dec(v_x_894_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_906_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v_b_902_; lean_object* v___x_904_; 
v_b_902_ = l_Substring_Raw_takeWhileAux(v_str_896_, v_stopPos_898_, v_x_895_, v_startPos_897_);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 1, v_b_902_);
v___x_904_ = v___x_900_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_str_896_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_b_902_);
lean_ctor_set(v_reuseFailAlloc_905_, 2, v_stopPos_898_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux(lean_object* v_s_907_, lean_object* v_begPos_908_, lean_object* v_p_909_, lean_object* v_i_910_){
_start:
{
uint8_t v___x_911_; 
v___x_911_ = l_String_instDecidableLtRaw___aux__1(v_begPos_908_, v_i_910_);
if (v___x_911_ == 0)
{
lean_dec_ref(v_p_909_);
return v_i_910_;
}
else
{
lean_object* v_i_x27_912_; uint32_t v_c_913_; lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v_i_x27_912_ = lean_string_utf8_prev(v_s_907_, v_i_910_);
v_c_913_ = lean_string_utf8_get(v_s_907_, v_i_x27_912_);
v___x_914_ = lean_box_uint32(v_c_913_);
lean_inc_ref(v_p_909_);
v___x_915_ = lean_apply_1(v_p_909_, v___x_914_);
v___x_916_ = lean_unbox(v___x_915_);
if (v___x_916_ == 0)
{
lean_dec(v_i_x27_912_);
lean_dec_ref(v_p_909_);
return v_i_910_;
}
else
{
lean_dec(v_i_910_);
v_i_910_ = v_i_x27_912_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux___boxed(lean_object* v_s_918_, lean_object* v_begPos_919_, lean_object* v_p_920_, lean_object* v_i_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Substring_Raw_takeRightWhileAux(v_s_918_, v_begPos_919_, v_p_920_, v_i_921_);
lean_dec(v_begPos_919_);
lean_dec_ref(v_s_918_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhile(lean_object* v_x_923_, lean_object* v_x_924_){
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
lean_inc(v_stopPos_927_);
v_b_931_ = l_Substring_Raw_takeRightWhileAux(v_str_925_, v_startPos_926_, v_x_924_, v_stopPos_927_);
lean_dec(v_startPos_926_);
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
LEAN_EXPORT lean_object* l_Substring_Raw_dropRightWhile(lean_object* v_x_936_, lean_object* v_x_937_){
_start:
{
lean_object* v_str_938_; lean_object* v_startPos_939_; lean_object* v_stopPos_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_948_; 
v_str_938_ = lean_ctor_get(v_x_936_, 0);
v_startPos_939_ = lean_ctor_get(v_x_936_, 1);
v_stopPos_940_ = lean_ctor_get(v_x_936_, 2);
v_isSharedCheck_948_ = !lean_is_exclusive(v_x_936_);
if (v_isSharedCheck_948_ == 0)
{
v___x_942_ = v_x_936_;
v_isShared_943_ = v_isSharedCheck_948_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_stopPos_940_);
lean_inc(v_startPos_939_);
lean_inc(v_str_938_);
lean_dec(v_x_936_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_948_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v_e_944_; lean_object* v___x_946_; 
v_e_944_ = l_Substring_Raw_takeRightWhileAux(v_str_938_, v_startPos_939_, v_x_937_, v_stopPos_940_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 2, v_e_944_);
v___x_946_ = v___x_942_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_str_938_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_startPos_939_);
lean_ctor_set(v_reuseFailAlloc_947_, 2, v_e_944_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_trimLeft(lean_object* v_s_950_){
_start:
{
lean_object* v_str_951_; lean_object* v_startPos_952_; lean_object* v_stopPos_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_962_; 
v_str_951_ = lean_ctor_get(v_s_950_, 0);
v_startPos_952_ = lean_ctor_get(v_s_950_, 1);
v_stopPos_953_ = lean_ctor_get(v_s_950_, 2);
v_isSharedCheck_962_ = !lean_is_exclusive(v_s_950_);
if (v_isSharedCheck_962_ == 0)
{
v___x_955_ = v_s_950_;
v_isShared_956_ = v_isSharedCheck_962_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_stopPos_953_);
lean_inc(v_startPos_952_);
lean_inc(v_str_951_);
lean_dec(v_s_950_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_962_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_957_; lean_object* v_b_958_; lean_object* v___x_960_; 
v___x_957_ = ((lean_object*)(l_Substring_Raw_trimLeft___closed__0));
v_b_958_ = l_Substring_Raw_takeWhileAux(v_str_951_, v_stopPos_953_, v___x_957_, v_startPos_952_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 1, v_b_958_);
v___x_960_ = v___x_955_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_str_951_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v_b_958_);
lean_ctor_set(v_reuseFailAlloc_961_, 2, v_stopPos_953_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_trimRight(lean_object* v_s_963_){
_start:
{
lean_object* v_str_964_; lean_object* v_startPos_965_; lean_object* v_stopPos_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_975_; 
v_str_964_ = lean_ctor_get(v_s_963_, 0);
v_startPos_965_ = lean_ctor_get(v_s_963_, 1);
v_stopPos_966_ = lean_ctor_get(v_s_963_, 2);
v_isSharedCheck_975_ = !lean_is_exclusive(v_s_963_);
if (v_isSharedCheck_975_ == 0)
{
v___x_968_ = v_s_963_;
v_isShared_969_ = v_isSharedCheck_975_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_stopPos_966_);
lean_inc(v_startPos_965_);
lean_inc(v_str_964_);
lean_dec(v_s_963_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_975_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_970_; lean_object* v_e_971_; lean_object* v___x_973_; 
v___x_970_ = ((lean_object*)(l_Substring_Raw_trimLeft___closed__0));
v_e_971_ = l_Substring_Raw_takeRightWhileAux(v_str_964_, v_startPos_965_, v___x_970_, v_stopPos_966_);
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 2, v_e_971_);
v___x_973_ = v___x_968_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_str_964_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v_startPos_965_);
lean_ctor_set(v_reuseFailAlloc_974_, 2, v_e_971_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_trim(lean_object* v_x_976_){
_start:
{
lean_object* v_str_977_; lean_object* v_startPos_978_; lean_object* v_stopPos_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_989_; 
v_str_977_ = lean_ctor_get(v_x_976_, 0);
v_startPos_978_ = lean_ctor_get(v_x_976_, 1);
v_stopPos_979_ = lean_ctor_get(v_x_976_, 2);
v_isSharedCheck_989_ = !lean_is_exclusive(v_x_976_);
if (v_isSharedCheck_989_ == 0)
{
v___x_981_ = v_x_976_;
v_isShared_982_ = v_isSharedCheck_989_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_stopPos_979_);
lean_inc(v_startPos_978_);
lean_inc(v_str_977_);
lean_dec(v_x_976_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_989_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_983_; lean_object* v_b_984_; lean_object* v_e_985_; lean_object* v___x_987_; 
v___x_983_ = ((lean_object*)(l_Substring_Raw_trimLeft___closed__0));
v_b_984_ = l_Substring_Raw_takeWhileAux(v_str_977_, v_stopPos_979_, v___x_983_, v_startPos_978_);
v_e_985_ = l_Substring_Raw_takeRightWhileAux(v_str_977_, v_b_984_, v___x_983_, v_stopPos_979_);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 2, v_e_985_);
lean_ctor_set(v___x_981_, 1, v_b_984_);
v___x_987_ = v___x_981_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_str_977_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v_b_984_);
lean_ctor_set(v_reuseFailAlloc_988_, 2, v_e_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___lam__0(lean_object* v___y_990_, uint8_t v___x_991_, uint8_t v___x_992_, lean_object* v_it_993_, lean_object* v_acc_994_, lean_object* v_hP_995_, lean_object* v_recur_996_){
_start:
{
lean_object* v_str_997_; lean_object* v_startInclusive_998_; lean_object* v_endExclusive_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; 
v_str_997_ = lean_ctor_get(v___y_990_, 0);
v_startInclusive_998_ = lean_ctor_get(v___y_990_, 1);
v_endExclusive_999_ = lean_ctor_get(v___y_990_, 2);
v___x_1000_ = lean_nat_sub(v_endExclusive_999_, v_startInclusive_998_);
v___x_1001_ = lean_nat_dec_eq(v_it_993_, v___x_1000_);
lean_dec(v___x_1000_);
if (v___x_1001_ == 0)
{
lean_object* v_snd_1002_; lean_object* v_snd_1003_; lean_object* v_fst_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1065_; 
v_snd_1002_ = lean_ctor_get(v_acc_994_, 1);
lean_inc(v_snd_1002_);
v_snd_1003_ = lean_ctor_get(v_snd_1002_, 1);
lean_inc(v_snd_1003_);
v_fst_1004_ = lean_ctor_get(v_acc_994_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v_acc_994_);
if (v_isSharedCheck_1065_ == 0)
{
lean_object* v_unused_1066_; 
v_unused_1066_ = lean_ctor_get(v_acc_994_, 1);
lean_dec(v_unused_1066_);
v___x_1006_ = v_acc_994_;
v_isShared_1007_ = v_isSharedCheck_1065_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_fst_1004_);
lean_dec(v_acc_994_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1065_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v_fst_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1063_; 
v_fst_1008_ = lean_ctor_get(v_snd_1002_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v_snd_1002_);
if (v_isSharedCheck_1063_ == 0)
{
lean_object* v_unused_1064_; 
v_unused_1064_ = lean_ctor_get(v_snd_1002_, 1);
lean_dec(v_unused_1064_);
v___x_1010_ = v_snd_1002_;
v_isShared_1011_ = v_isSharedCheck_1063_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_fst_1008_);
lean_dec(v_snd_1002_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1063_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v_snd_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1061_; 
v_snd_1012_ = lean_ctor_get(v_snd_1003_, 1);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_snd_1003_);
if (v_isSharedCheck_1061_ == 0)
{
lean_object* v_unused_1062_; 
v_unused_1062_ = lean_ctor_get(v_snd_1003_, 0);
lean_dec(v_unused_1062_);
v___x_1014_ = v_snd_1003_;
v_isShared_1015_ = v_isSharedCheck_1061_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_snd_1012_);
lean_dec(v_snd_1003_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1061_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1016_; uint32_t v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; uint8_t v___y_1021_; uint8_t v___y_1022_; uint8_t v___y_1040_; uint8_t v___y_1041_; uint8_t v___y_1046_; uint8_t v___y_1047_; uint8_t v___y_1052_; uint32_t v___x_1057_; uint8_t v___x_1058_; 
v___x_1016_ = lean_nat_add(v_startInclusive_998_, v_it_993_);
v___x_1017_ = lean_string_utf8_get_fast(v_str_997_, v___x_1016_);
v___x_1018_ = lean_string_utf8_next_fast(v_str_997_, v___x_1016_);
lean_dec(v___x_1016_);
v___x_1019_ = lean_nat_sub(v___x_1018_, v_startInclusive_998_);
v___x_1057_ = 48;
v___x_1058_ = lean_uint32_dec_le(v___x_1057_, v___x_1017_);
if (v___x_1058_ == 0)
{
v___y_1052_ = v___x_1058_;
goto v___jp_1051_;
}
else
{
uint32_t v___x_1059_; uint8_t v___x_1060_; 
v___x_1059_ = 57;
v___x_1060_ = lean_uint32_dec_le(v___x_1017_, v___x_1059_);
v___y_1052_ = v___x_1060_;
goto v___jp_1051_;
}
v___jp_1020_:
{
uint32_t v___x_1023_; uint8_t v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1023_ = 95;
v___x_1024_ = lean_uint32_dec_eq(v___x_1017_, v___x_1023_);
v___x_1025_ = lean_box(v___y_1021_);
v___x_1026_ = lean_box(v___y_1022_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 1, v___x_1026_);
lean_ctor_set(v___x_1014_, 0, v___x_1025_);
v___x_1028_ = v___x_1014_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1025_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v___x_1026_);
v___x_1028_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_object* v___x_1029_; lean_object* v___x_1031_; 
v___x_1029_ = lean_box(v___x_1024_);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 1, v___x_1028_);
lean_ctor_set(v___x_1010_, 0, v___x_1029_);
v___x_1031_ = v___x_1010_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1029_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v___x_1028_);
v___x_1031_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
lean_object* v___x_1032_; lean_object* v___x_1034_; 
v___x_1032_ = lean_box(v___x_991_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 1, v___x_1031_);
lean_ctor_set(v___x_1006_, 0, v___x_1032_);
v___x_1034_ = v___x_1006_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1032_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v___x_1031_);
v___x_1034_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1035_; 
v___x_1035_ = lean_apply_4(v_recur_996_, v___x_1019_, v___x_1034_, lean_box(0), lean_box(0));
return v___x_1035_;
}
}
}
}
v___jp_1039_:
{
uint8_t v___x_1042_; 
v___x_1042_ = lean_unbox(v_fst_1008_);
lean_dec(v_fst_1008_);
if (v___x_1042_ == 0)
{
v___y_1021_ = v___y_1040_;
v___y_1022_ = v___y_1041_;
goto v___jp_1020_;
}
else
{
uint32_t v___x_1043_; uint8_t v___x_1044_; 
v___x_1043_ = 95;
v___x_1044_ = lean_uint32_dec_eq(v___x_1017_, v___x_1043_);
if (v___x_1044_ == 0)
{
v___y_1021_ = v___y_1040_;
v___y_1022_ = v___y_1041_;
goto v___jp_1020_;
}
else
{
v___y_1021_ = v___y_1040_;
v___y_1022_ = v___x_991_;
goto v___jp_1020_;
}
}
}
v___jp_1045_:
{
uint8_t v___x_1048_; 
v___x_1048_ = lean_unbox(v_fst_1004_);
lean_dec(v_fst_1004_);
if (v___x_1048_ == 0)
{
v___y_1040_ = v___y_1046_;
v___y_1041_ = v___y_1047_;
goto v___jp_1039_;
}
else
{
uint32_t v___x_1049_; uint8_t v___x_1050_; 
v___x_1049_ = 95;
v___x_1050_ = lean_uint32_dec_eq(v___x_1017_, v___x_1049_);
if (v___x_1050_ == 0)
{
v___y_1040_ = v___y_1046_;
v___y_1041_ = v___y_1047_;
goto v___jp_1039_;
}
else
{
if (v___x_991_ == 0)
{
lean_dec(v_fst_1008_);
v___y_1021_ = v___y_1046_;
v___y_1022_ = v___x_991_;
goto v___jp_1020_;
}
else
{
v___y_1040_ = v___y_1046_;
v___y_1041_ = v___x_991_;
goto v___jp_1039_;
}
}
}
}
v___jp_1051_:
{
uint8_t v___x_1053_; 
v___x_1053_ = lean_unbox(v_snd_1012_);
if (v___x_1053_ == 0)
{
uint8_t v___x_1054_; 
lean_dec(v_fst_1008_);
lean_dec(v_fst_1004_);
v___x_1054_ = lean_unbox(v_snd_1012_);
lean_dec(v_snd_1012_);
v___y_1021_ = v___y_1052_;
v___y_1022_ = v___x_1054_;
goto v___jp_1020_;
}
else
{
lean_dec(v_snd_1012_);
if (v___y_1052_ == 0)
{
uint32_t v___x_1055_; uint8_t v___x_1056_; 
v___x_1055_ = 95;
v___x_1056_ = lean_uint32_dec_eq(v___x_1017_, v___x_1055_);
if (v___x_1056_ == 0)
{
lean_dec(v_fst_1008_);
lean_dec(v_fst_1004_);
v___y_1021_ = v___y_1052_;
v___y_1022_ = v___x_1056_;
goto v___jp_1020_;
}
else
{
v___y_1046_ = v___y_1052_;
v___y_1047_ = v___x_1056_;
goto v___jp_1045_;
}
}
else
{
v___y_1046_ = v___y_1052_;
v___y_1047_ = v___x_992_;
goto v___jp_1045_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_recur_996_);
return v_acc_994_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___lam__0___boxed(lean_object* v___y_1067_, lean_object* v___x_1068_, lean_object* v___x_1069_, lean_object* v_it_1070_, lean_object* v_acc_1071_, lean_object* v_hP_1072_, lean_object* v_recur_1073_){
_start:
{
uint8_t v___x_1077__boxed_1074_; uint8_t v___x_1078__boxed_1075_; lean_object* v_res_1076_; 
v___x_1077__boxed_1074_ = lean_unbox(v___x_1068_);
v___x_1078__boxed_1075_ = lean_unbox(v___x_1069_);
v_res_1076_ = l_Substring_Raw_isNat___lam__0(v___y_1067_, v___x_1077__boxed_1074_, v___x_1078__boxed_1075_, v_it_1070_, v_acc_1071_, v_hP_1072_, v_recur_1073_);
lean_dec(v_it_1070_);
lean_dec_ref(v___y_1067_);
return v_res_1076_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_isNat(lean_object* v_s_1077_){
_start:
{
lean_object* v_str_1078_; lean_object* v_startPos_1079_; lean_object* v_stopPos_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1119_; 
v_str_1078_ = lean_ctor_get(v_s_1077_, 0);
v_startPos_1079_ = lean_ctor_get(v_s_1077_, 1);
v_stopPos_1080_ = lean_ctor_get(v_s_1077_, 2);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_s_1077_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1082_ = v_s_1077_;
v_isShared_1083_ = v_isSharedCheck_1119_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_stopPos_1080_);
lean_inc(v_startPos_1079_);
lean_inc(v_str_1078_);
lean_dec(v_s_1077_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1119_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; 
v___x_1084_ = lean_nat_sub(v_stopPos_1080_, v_startPos_1079_);
v___x_1085_ = lean_unsigned_to_nat(0u);
v___x_1086_ = lean_nat_dec_eq(v___x_1084_, v___x_1085_);
lean_dec(v___x_1084_);
if (v___x_1086_ == 0)
{
uint8_t v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___y_1096_; lean_object* v___x_1108_; uint8_t v___x_1112_; 
v___x_1087_ = 1;
v___x_1088_ = lean_box(v___x_1086_);
v___x_1089_ = lean_box(v___x_1087_);
v___x_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1088_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
v___x_1091_ = lean_box(v___x_1086_);
v___x_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1091_);
lean_ctor_set(v___x_1092_, 1, v___x_1090_);
v___x_1093_ = lean_box(v___x_1087_);
v___x_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
lean_ctor_set(v___x_1094_, 1, v___x_1092_);
v___x_1108_ = l_String_instInhabitedSlice;
v___x_1112_ = lean_string_is_valid_pos(v_str_1078_, v_startPos_1079_);
if (v___x_1112_ == 0)
{
lean_del_object(v___x_1082_);
lean_dec(v_stopPos_1080_);
lean_dec(v_startPos_1079_);
lean_dec_ref(v_str_1078_);
goto v___jp_1109_;
}
else
{
uint8_t v___x_1113_; 
v___x_1113_ = lean_string_is_valid_pos(v_str_1078_, v_stopPos_1080_);
if (v___x_1113_ == 0)
{
lean_del_object(v___x_1082_);
lean_dec(v_stopPos_1080_);
lean_dec(v_startPos_1079_);
lean_dec_ref(v_str_1078_);
goto v___jp_1109_;
}
else
{
uint8_t v___x_1114_; 
v___x_1114_ = lean_nat_dec_le(v_startPos_1079_, v_stopPos_1080_);
if (v___x_1114_ == 0)
{
lean_del_object(v___x_1082_);
lean_dec(v_stopPos_1080_);
lean_dec(v_startPos_1079_);
lean_dec_ref(v_str_1078_);
goto v___jp_1109_;
}
else
{
lean_object* v___x_1116_; 
if (v_isShared_1083_ == 0)
{
v___x_1116_ = v___x_1082_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_str_1078_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v_startPos_1079_);
lean_ctor_set(v_reuseFailAlloc_1117_, 2, v_stopPos_1080_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
v___y_1096_ = v___x_1116_;
goto v___jp_1095_;
}
}
}
}
v___jp_1095_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___f_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v_snd_1102_; lean_object* v_snd_1103_; lean_object* v_snd_1104_; uint8_t v___x_1105_; 
v___x_1097_ = lean_box(v___x_1086_);
v___x_1098_ = lean_box(v___x_1087_);
lean_inc_ref(v___y_1096_);
v___f_1099_ = lean_alloc_closure((void*)(l_Substring_Raw_isNat___lam__0___boxed), 7, 3);
lean_closure_set(v___f_1099_, 0, v___y_1096_);
lean_closure_set(v___f_1099_, 1, v___x_1097_);
lean_closure_set(v___f_1099_, 2, v___x_1098_);
v___x_1100_ = l_String_Slice_positions(v___y_1096_);
lean_dec_ref(v___y_1096_);
v___x_1101_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1099_, v___x_1100_, v___x_1094_, lean_box(0));
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
return v___x_1086_;
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
v___y_1096_ = v___x_1111_;
goto v___jp_1095_;
}
}
else
{
uint8_t v___x_1118_; 
lean_del_object(v___x_1082_);
lean_dec(v_stopPos_1080_);
lean_dec(v_startPos_1079_);
lean_dec_ref(v_str_1078_);
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
lean_object* v_snd_1132_; lean_object* v_snd_1133_; lean_object* v_fst_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1198_; 
v_snd_1132_ = lean_ctor_get(v_b_1126_, 1);
lean_inc(v_snd_1132_);
v_snd_1133_ = lean_ctor_get(v_snd_1132_, 1);
lean_inc(v_snd_1133_);
v_fst_1134_ = lean_ctor_get(v_b_1126_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_b_1126_);
if (v_isSharedCheck_1198_ == 0)
{
lean_object* v_unused_1199_; 
v_unused_1199_ = lean_ctor_get(v_b_1126_, 1);
lean_dec(v_unused_1199_);
v___x_1136_ = v_b_1126_;
v_isShared_1137_ = v_isSharedCheck_1198_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_fst_1134_);
lean_dec(v_b_1126_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1198_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v_fst_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1196_; 
v_fst_1138_ = lean_ctor_get(v_snd_1132_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v_snd_1132_);
if (v_isSharedCheck_1196_ == 0)
{
lean_object* v_unused_1197_; 
v_unused_1197_ = lean_ctor_get(v_snd_1132_, 1);
lean_dec(v_unused_1197_);
v___x_1140_ = v_snd_1132_;
v_isShared_1141_ = v_isSharedCheck_1196_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_fst_1138_);
lean_dec(v_snd_1132_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1196_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v_snd_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1194_; 
v_snd_1142_ = lean_ctor_get(v_snd_1133_, 1);
v_isSharedCheck_1194_ = !lean_is_exclusive(v_snd_1133_);
if (v_isSharedCheck_1194_ == 0)
{
lean_object* v_unused_1195_; 
v_unused_1195_ = lean_ctor_get(v_snd_1133_, 0);
lean_dec(v_unused_1195_);
v___x_1144_ = v_snd_1133_;
v_isShared_1145_ = v_isSharedCheck_1194_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_snd_1142_);
lean_dec(v_snd_1133_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1194_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1146_; uint8_t v___x_1147_; uint8_t v___x_1148_; lean_object* v___x_1149_; uint32_t v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; uint8_t v___y_1154_; uint8_t v___y_1155_; uint8_t v___y_1173_; uint8_t v___y_1174_; uint8_t v___y_1179_; uint8_t v___y_1180_; uint8_t v___y_1185_; uint32_t v___x_1190_; uint8_t v___x_1191_; 
v___x_1146_ = lean_unsigned_to_nat(0u);
v___x_1147_ = lean_nat_dec_eq(v___x_1123_, v___x_1146_);
v___x_1148_ = 1;
v___x_1149_ = lean_nat_add(v_startInclusive_1128_, v_a_1125_);
lean_dec(v_a_1125_);
v___x_1150_ = lean_string_utf8_get_fast(v_str_1127_, v___x_1149_);
v___x_1151_ = lean_string_utf8_next_fast(v_str_1127_, v___x_1149_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_nat_sub(v___x_1151_, v_startInclusive_1128_);
v___x_1190_ = 48;
v___x_1191_ = lean_uint32_dec_le(v___x_1190_, v___x_1150_);
if (v___x_1191_ == 0)
{
v___y_1185_ = v___x_1191_;
goto v___jp_1184_;
}
else
{
uint32_t v___x_1192_; uint8_t v___x_1193_; 
v___x_1192_ = 57;
v___x_1193_ = lean_uint32_dec_le(v___x_1150_, v___x_1192_);
v___y_1185_ = v___x_1193_;
goto v___jp_1184_;
}
v___jp_1153_:
{
uint32_t v___x_1156_; uint8_t v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1156_ = 95;
v___x_1157_ = lean_uint32_dec_eq(v___x_1150_, v___x_1156_);
v___x_1158_ = lean_box(v___y_1154_);
v___x_1159_ = lean_box(v___y_1155_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 1, v___x_1159_);
lean_ctor_set(v___x_1144_, 0, v___x_1158_);
v___x_1161_ = v___x_1144_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1158_);
lean_ctor_set(v_reuseFailAlloc_1171_, 1, v___x_1159_);
v___x_1161_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1162_; lean_object* v___x_1164_; 
v___x_1162_ = lean_box(v___x_1157_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 1, v___x_1161_);
lean_ctor_set(v___x_1140_, 0, v___x_1162_);
v___x_1164_ = v___x_1140_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v___x_1161_);
v___x_1164_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
lean_object* v___x_1165_; lean_object* v___x_1167_; 
v___x_1165_ = lean_box(v___x_1147_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 1, v___x_1164_);
lean_ctor_set(v___x_1136_, 0, v___x_1165_);
v___x_1167_ = v___x_1136_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1165_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v___x_1164_);
v___x_1167_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
v_a_1125_ = v___x_1152_;
v_b_1126_ = v___x_1167_;
goto _start;
}
}
}
}
v___jp_1172_:
{
uint8_t v___x_1175_; 
v___x_1175_ = lean_unbox(v_fst_1138_);
lean_dec(v_fst_1138_);
if (v___x_1175_ == 0)
{
v___y_1154_ = v___y_1173_;
v___y_1155_ = v___y_1174_;
goto v___jp_1153_;
}
else
{
uint32_t v___x_1176_; uint8_t v___x_1177_; 
v___x_1176_ = 95;
v___x_1177_ = lean_uint32_dec_eq(v___x_1150_, v___x_1176_);
if (v___x_1177_ == 0)
{
v___y_1154_ = v___y_1173_;
v___y_1155_ = v___y_1174_;
goto v___jp_1153_;
}
else
{
v___y_1154_ = v___y_1173_;
v___y_1155_ = v___x_1147_;
goto v___jp_1153_;
}
}
}
v___jp_1178_:
{
uint8_t v___x_1181_; 
v___x_1181_ = lean_unbox(v_fst_1134_);
lean_dec(v_fst_1134_);
if (v___x_1181_ == 0)
{
v___y_1173_ = v___y_1179_;
v___y_1174_ = v___y_1180_;
goto v___jp_1172_;
}
else
{
uint32_t v___x_1182_; uint8_t v___x_1183_; 
v___x_1182_ = 95;
v___x_1183_ = lean_uint32_dec_eq(v___x_1150_, v___x_1182_);
if (v___x_1183_ == 0)
{
v___y_1173_ = v___y_1179_;
v___y_1174_ = v___y_1180_;
goto v___jp_1172_;
}
else
{
if (v___x_1147_ == 0)
{
lean_dec(v_fst_1138_);
v___y_1154_ = v___y_1179_;
v___y_1155_ = v___x_1147_;
goto v___jp_1153_;
}
else
{
v___y_1173_ = v___y_1179_;
v___y_1174_ = v___x_1147_;
goto v___jp_1172_;
}
}
}
}
v___jp_1184_:
{
uint8_t v___x_1186_; 
v___x_1186_ = lean_unbox(v_snd_1142_);
if (v___x_1186_ == 0)
{
uint8_t v___x_1187_; 
lean_dec(v_fst_1138_);
lean_dec(v_fst_1134_);
v___x_1187_ = lean_unbox(v_snd_1142_);
lean_dec(v_snd_1142_);
v___y_1154_ = v___y_1185_;
v___y_1155_ = v___x_1187_;
goto v___jp_1153_;
}
else
{
lean_dec(v_snd_1142_);
if (v___y_1185_ == 0)
{
uint32_t v___x_1188_; uint8_t v___x_1189_; 
v___x_1188_ = 95;
v___x_1189_ = lean_uint32_dec_eq(v___x_1150_, v___x_1188_);
if (v___x_1189_ == 0)
{
lean_dec(v_fst_1138_);
lean_dec(v_fst_1134_);
v___y_1154_ = v___y_1185_;
v___y_1155_ = v___x_1189_;
goto v___jp_1153_;
}
else
{
v___y_1179_ = v___y_1185_;
v___y_1180_ = v___x_1189_;
goto v___jp_1178_;
}
}
else
{
v___y_1179_ = v___y_1185_;
v___y_1180_ = v___x_1148_;
goto v___jp_1178_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg___boxed(lean_object* v___x_1200_, lean_object* v___y_1201_, lean_object* v_a_1202_, lean_object* v_b_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(v___x_1200_, v___y_1201_, v_a_1202_, v_b_1203_);
lean_dec_ref(v___y_1201_);
lean_dec(v___x_1200_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(lean_object* v___y_1205_, lean_object* v_a_1206_, lean_object* v_b_1207_){
_start:
{
lean_object* v_str_1208_; lean_object* v_startInclusive_1209_; lean_object* v_endExclusive_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; 
v_str_1208_ = lean_ctor_get(v___y_1205_, 0);
v_startInclusive_1209_ = lean_ctor_get(v___y_1205_, 1);
v_endExclusive_1210_ = lean_ctor_get(v___y_1205_, 2);
v___x_1211_ = lean_nat_sub(v_endExclusive_1210_, v_startInclusive_1209_);
v___x_1212_ = lean_nat_dec_eq(v_a_1206_, v___x_1211_);
lean_dec(v___x_1211_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; uint32_t v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; uint32_t v___x_1217_; uint8_t v___x_1218_; 
v___x_1213_ = lean_nat_add(v_startInclusive_1209_, v_a_1206_);
lean_dec(v_a_1206_);
v___x_1214_ = lean_string_utf8_get_fast(v_str_1208_, v___x_1213_);
v___x_1215_ = lean_string_utf8_next_fast(v_str_1208_, v___x_1213_);
lean_dec(v___x_1213_);
v___x_1216_ = lean_nat_sub(v___x_1215_, v_startInclusive_1209_);
v___x_1217_ = 95;
v___x_1218_ = lean_uint32_dec_eq(v___x_1214_, v___x_1217_);
if (v___x_1218_ == 0)
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1219_ = lean_unsigned_to_nat(10u);
v___x_1220_ = lean_nat_mul(v_b_1207_, v___x_1219_);
lean_dec(v_b_1207_);
v___x_1221_ = lean_uint32_to_nat(v___x_1214_);
v___x_1222_ = lean_unsigned_to_nat(48u);
v___x_1223_ = lean_nat_sub(v___x_1221_, v___x_1222_);
lean_dec(v___x_1221_);
v___x_1224_ = lean_nat_add(v___x_1220_, v___x_1223_);
lean_dec(v___x_1223_);
lean_dec(v___x_1220_);
v_a_1206_ = v___x_1216_;
v_b_1207_ = v___x_1224_;
goto _start;
}
else
{
v_a_1206_ = v___x_1216_;
goto _start;
}
}
else
{
lean_dec(v_a_1206_);
return v_b_1207_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg___boxed(lean_object* v___y_1227_, lean_object* v_a_1228_, lean_object* v_b_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(v___y_1227_, v_a_1228_, v_b_1229_);
lean_dec_ref(v___y_1227_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toNat_x3f(lean_object* v_s_1231_){
_start:
{
lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1239_; lean_object* v_str_1242_; lean_object* v_startPos_1243_; lean_object* v_stopPos_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1287_; 
v_str_1242_ = lean_ctor_get(v_s_1231_, 0);
v_startPos_1243_ = lean_ctor_get(v_s_1231_, 1);
v_stopPos_1244_ = lean_ctor_get(v_s_1231_, 2);
v_isSharedCheck_1287_ = !lean_is_exclusive(v_s_1231_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1246_ = v_s_1231_;
v_isShared_1247_ = v_isSharedCheck_1287_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_stopPos_1244_);
lean_inc(v_startPos_1243_);
lean_inc(v_str_1242_);
lean_dec(v_s_1231_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1287_;
goto v_resetjp_1245_;
}
v___jp_1232_:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1235_ = l_String_Slice_positions(v___y_1234_);
v___x_1236_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(v___y_1234_, v___x_1235_, v___y_1233_);
lean_dec_ref(v___y_1234_);
v___x_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
return v___x_1237_;
}
v___jp_1238_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_1241_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_1240_);
v___y_1233_ = v___y_1239_;
v___y_1234_ = v___x_1241_;
goto v___jp_1232_;
}
v_resetjp_1245_:
{
uint8_t v___y_1249_; lean_object* v___x_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; 
v___x_1258_ = lean_nat_sub(v_stopPos_1244_, v_startPos_1243_);
v___x_1259_ = lean_unsigned_to_nat(0u);
v___x_1260_ = lean_nat_dec_eq(v___x_1258_, v___x_1259_);
if (v___x_1260_ == 0)
{
uint8_t v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___y_1270_; uint8_t v___x_1282_; 
v___x_1261_ = 1;
v___x_1262_ = lean_box(v___x_1260_);
v___x_1263_ = lean_box(v___x_1261_);
v___x_1264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1262_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
v___x_1265_ = lean_box(v___x_1260_);
v___x_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
lean_ctor_set(v___x_1266_, 1, v___x_1264_);
v___x_1267_ = lean_box(v___x_1261_);
v___x_1268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1267_);
lean_ctor_set(v___x_1268_, 1, v___x_1266_);
v___x_1282_ = lean_string_is_valid_pos(v_str_1242_, v_startPos_1243_);
if (v___x_1282_ == 0)
{
goto v___jp_1279_;
}
else
{
uint8_t v___x_1283_; 
v___x_1283_ = lean_string_is_valid_pos(v_str_1242_, v_stopPos_1244_);
if (v___x_1283_ == 0)
{
goto v___jp_1279_;
}
else
{
uint8_t v___x_1284_; 
v___x_1284_ = lean_nat_dec_le(v_startPos_1243_, v_stopPos_1244_);
if (v___x_1284_ == 0)
{
goto v___jp_1279_;
}
else
{
lean_object* v___x_1285_; 
lean_inc(v_stopPos_1244_);
lean_inc(v_startPos_1243_);
lean_inc_ref(v_str_1242_);
v___x_1285_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1285_, 0, v_str_1242_);
lean_ctor_set(v___x_1285_, 1, v_startPos_1243_);
lean_ctor_set(v___x_1285_, 2, v_stopPos_1244_);
v___y_1270_ = v___x_1285_;
goto v___jp_1269_;
}
}
}
v___jp_1269_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v_snd_1273_; lean_object* v_snd_1274_; lean_object* v_snd_1275_; uint8_t v___x_1276_; 
v___x_1271_ = l_String_Slice_positions(v___y_1270_);
v___x_1272_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(v___x_1258_, v___y_1270_, v___x_1271_, v___x_1268_);
lean_dec_ref(v___y_1270_);
lean_dec(v___x_1258_);
v_snd_1273_ = lean_ctor_get(v___x_1272_, 1);
lean_inc(v_snd_1273_);
lean_dec_ref(v___x_1272_);
v_snd_1274_ = lean_ctor_get(v_snd_1273_, 1);
lean_inc(v_snd_1274_);
lean_dec(v_snd_1273_);
v_snd_1275_ = lean_ctor_get(v_snd_1274_, 1);
v___x_1276_ = lean_unbox(v_snd_1275_);
if (v___x_1276_ == 0)
{
lean_dec(v_snd_1274_);
v___y_1249_ = v___x_1260_;
goto v___jp_1248_;
}
else
{
lean_object* v_fst_1277_; uint8_t v___x_1278_; 
v_fst_1277_ = lean_ctor_get(v_snd_1274_, 0);
lean_inc(v_fst_1277_);
lean_dec(v_snd_1274_);
v___x_1278_ = lean_unbox(v_fst_1277_);
lean_dec(v_fst_1277_);
v___y_1249_ = v___x_1278_;
goto v___jp_1248_;
}
}
v___jp_1279_:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_1281_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_1280_);
v___y_1270_ = v___x_1281_;
goto v___jp_1269_;
}
}
else
{
lean_object* v___x_1286_; 
lean_dec(v___x_1258_);
lean_del_object(v___x_1246_);
lean_dec(v_stopPos_1244_);
lean_dec(v_startPos_1243_);
lean_dec_ref(v_str_1242_);
v___x_1286_ = lean_box(0);
return v___x_1286_;
}
v___jp_1248_:
{
if (v___y_1249_ == 0)
{
lean_object* v___x_1250_; 
lean_del_object(v___x_1246_);
lean_dec(v_stopPos_1244_);
lean_dec(v_startPos_1243_);
lean_dec_ref(v_str_1242_);
v___x_1250_ = lean_box(0);
return v___x_1250_;
}
else
{
lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1251_ = lean_unsigned_to_nat(0u);
v___x_1252_ = lean_string_is_valid_pos(v_str_1242_, v_startPos_1243_);
if (v___x_1252_ == 0)
{
lean_del_object(v___x_1246_);
lean_dec(v_stopPos_1244_);
lean_dec(v_startPos_1243_);
lean_dec_ref(v_str_1242_);
v___y_1239_ = v___x_1251_;
goto v___jp_1238_;
}
else
{
uint8_t v___x_1253_; 
v___x_1253_ = lean_string_is_valid_pos(v_str_1242_, v_stopPos_1244_);
if (v___x_1253_ == 0)
{
lean_del_object(v___x_1246_);
lean_dec(v_stopPos_1244_);
lean_dec(v_startPos_1243_);
lean_dec_ref(v_str_1242_);
v___y_1239_ = v___x_1251_;
goto v___jp_1238_;
}
else
{
uint8_t v___x_1254_; 
v___x_1254_ = lean_nat_dec_le(v_startPos_1243_, v_stopPos_1244_);
if (v___x_1254_ == 0)
{
lean_del_object(v___x_1246_);
lean_dec(v_stopPos_1244_);
lean_dec(v_startPos_1243_);
lean_dec_ref(v_str_1242_);
v___y_1239_ = v___x_1251_;
goto v___jp_1238_;
}
else
{
lean_object* v___x_1256_; 
if (v_isShared_1247_ == 0)
{
v___x_1256_ = v___x_1246_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_str_1242_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v_startPos_1243_);
lean_ctor_set(v_reuseFailAlloc_1257_, 2, v_stopPos_1244_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
v___y_1233_ = v___x_1251_;
v___y_1234_ = v___x_1256_;
goto v___jp_1232_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0(lean_object* v___y_1288_, lean_object* v_inst_1289_, lean_object* v_R_1290_, lean_object* v_a_1291_, lean_object* v_b_1292_, lean_object* v_c_1293_){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(v___y_1288_, v_a_1291_, v_b_1292_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___boxed(lean_object* v___y_1295_, lean_object* v_inst_1296_, lean_object* v_R_1297_, lean_object* v_a_1298_, lean_object* v_b_1299_, lean_object* v_c_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0(v___y_1295_, v_inst_1296_, v_R_1297_, v_a_1298_, v_b_1299_, v_c_1300_);
lean_dec_ref(v___y_1295_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1(lean_object* v___x_1302_, lean_object* v___y_1303_, lean_object* v_inst_1304_, lean_object* v_R_1305_, lean_object* v_a_1306_, lean_object* v_b_1307_, lean_object* v_c_1308_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(v___x_1302_, v___y_1303_, v_a_1306_, v_b_1307_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___boxed(lean_object* v___x_1310_, lean_object* v___y_1311_, lean_object* v_inst_1312_, lean_object* v_R_1313_, lean_object* v_a_1314_, lean_object* v_b_1315_, lean_object* v_c_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1(v___x_1310_, v___y_1311_, v_inst_1312_, v_R_1313_, v_a_1314_, v_b_1315_, v_c_1316_);
lean_dec_ref(v___y_1311_);
lean_dec(v___x_1310_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_repair(lean_object* v_x_1318_){
_start:
{
lean_object* v_str_1319_; lean_object* v_startPos_1320_; lean_object* v_stopPos_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1337_; 
v_str_1319_ = lean_ctor_get(v_x_1318_, 0);
v_startPos_1320_ = lean_ctor_get(v_x_1318_, 1);
v_stopPos_1321_ = lean_ctor_get(v_x_1318_, 2);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_x_1318_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1323_ = v_x_1318_;
v_isShared_1324_ = v_isSharedCheck_1337_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_stopPos_1321_);
lean_inc(v_startPos_1320_);
lean_inc(v_str_1319_);
lean_dec(v_x_1318_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1337_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___y_1326_; uint8_t v___x_1335_; 
v___x_1335_ = lean_string_is_valid_pos(v_str_1319_, v_startPos_1320_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; 
lean_dec(v_startPos_1320_);
v___x_1336_ = lean_string_utf8_byte_size(v_str_1319_);
v___y_1326_ = v___x_1336_;
goto v___jp_1325_;
}
else
{
v___y_1326_ = v_startPos_1320_;
goto v___jp_1325_;
}
v___jp_1325_:
{
uint8_t v___x_1327_; 
v___x_1327_ = lean_string_is_valid_pos(v_str_1319_, v_stopPos_1321_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; lean_object* v___x_1330_; 
lean_dec(v_stopPos_1321_);
v___x_1328_ = lean_string_utf8_byte_size(v_str_1319_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 2, v___x_1328_);
lean_ctor_set(v___x_1323_, 1, v___y_1326_);
v___x_1330_ = v___x_1323_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_str_1319_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v___y_1326_);
lean_ctor_set(v_reuseFailAlloc_1331_, 2, v___x_1328_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
else
{
lean_object* v___x_1333_; 
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 1, v___y_1326_);
v___x_1333_ = v___x_1323_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_str_1319_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v___y_1326_);
lean_ctor_set(v_reuseFailAlloc_1334_, 2, v_stopPos_1321_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_beq(lean_object* v_ss1_1338_, lean_object* v_ss2_1339_){
_start:
{
lean_object* v_ss1_1340_; lean_object* v_str_1341_; lean_object* v_startPos_1342_; lean_object* v_stopPos_1343_; lean_object* v_ss2_1344_; lean_object* v_str_1345_; lean_object* v_startPos_1346_; lean_object* v_stopPos_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; uint8_t v___x_1350_; 
v_ss1_1340_ = l_Substring_Raw_repair(v_ss1_1338_);
v_str_1341_ = lean_ctor_get(v_ss1_1340_, 0);
lean_inc_ref(v_str_1341_);
v_startPos_1342_ = lean_ctor_get(v_ss1_1340_, 1);
lean_inc(v_startPos_1342_);
v_stopPos_1343_ = lean_ctor_get(v_ss1_1340_, 2);
lean_inc(v_stopPos_1343_);
lean_dec_ref(v_ss1_1340_);
v_ss2_1344_ = l_Substring_Raw_repair(v_ss2_1339_);
v_str_1345_ = lean_ctor_get(v_ss2_1344_, 0);
lean_inc_ref(v_str_1345_);
v_startPos_1346_ = lean_ctor_get(v_ss2_1344_, 1);
lean_inc(v_startPos_1346_);
v_stopPos_1347_ = lean_ctor_get(v_ss2_1344_, 2);
lean_inc(v_stopPos_1347_);
lean_dec_ref(v_ss2_1344_);
v___x_1348_ = lean_nat_sub(v_stopPos_1343_, v_startPos_1342_);
lean_dec(v_stopPos_1343_);
v___x_1349_ = lean_nat_sub(v_stopPos_1347_, v_startPos_1346_);
lean_dec(v_stopPos_1347_);
v___x_1350_ = lean_nat_dec_eq(v___x_1348_, v___x_1349_);
lean_dec(v___x_1349_);
if (v___x_1350_ == 0)
{
lean_dec(v___x_1348_);
lean_dec(v_startPos_1346_);
lean_dec_ref(v_str_1345_);
lean_dec(v_startPos_1342_);
lean_dec_ref(v_str_1341_);
return v___x_1350_;
}
else
{
uint8_t v___x_1351_; 
v___x_1351_ = l_String_Pos_Raw_substrEq(v_str_1341_, v_startPos_1342_, v_str_1345_, v_startPos_1346_, v___x_1348_);
lean_dec(v___x_1348_);
lean_dec_ref(v_str_1345_);
lean_dec_ref(v_str_1341_);
return v___x_1351_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_beq___boxed(lean_object* v_ss1_1352_, lean_object* v_ss2_1353_){
_start:
{
uint8_t v_res_1354_; lean_object* v_r_1355_; 
v_res_1354_ = l_Substring_Raw_beq(v_ss1_1352_, v_ss2_1353_);
v_r_1355_ = lean_box(v_res_1354_);
return v_r_1355_;
}
}
LEAN_EXPORT uint8_t lean_substring_beq(lean_object* v_ss1_1356_, lean_object* v_ss2_1357_){
_start:
{
uint8_t v___x_1358_; 
v___x_1358_ = l_Substring_Raw_beq(v_ss1_1356_, v_ss2_1357_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_beqImpl___boxed(lean_object* v_ss1_1359_, lean_object* v_ss2_1360_){
_start:
{
uint8_t v_res_1361_; lean_object* v_r_1362_; 
v_res_1361_ = lean_substring_beq(v_ss1_1359_, v_ss2_1360_);
v_r_1362_ = lean_box(v_res_1361_);
return v_r_1362_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_sameAs(lean_object* v_ss1_1365_, lean_object* v_ss2_1366_){
_start:
{
lean_object* v_startPos_1367_; lean_object* v_startPos_1368_; uint8_t v___x_1369_; 
v_startPos_1367_ = lean_ctor_get(v_ss1_1365_, 1);
v_startPos_1368_ = lean_ctor_get(v_ss2_1366_, 1);
v___x_1369_ = lean_nat_dec_eq(v_startPos_1367_, v_startPos_1368_);
if (v___x_1369_ == 0)
{
lean_dec_ref(v_ss2_1366_);
lean_dec_ref(v_ss1_1365_);
return v___x_1369_;
}
else
{
uint8_t v___x_1370_; 
v___x_1370_ = l_Substring_Raw_beq(v_ss1_1365_, v_ss2_1366_);
return v___x_1370_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_sameAs___boxed(lean_object* v_ss1_1371_, lean_object* v_ss2_1372_){
_start:
{
uint8_t v_res_1373_; lean_object* v_r_1374_; 
v_res_1373_ = l_Substring_Raw_sameAs(v_ss1_1371_, v_ss2_1372_);
v_r_1374_ = lean_box(v_res_1373_);
return v_r_1374_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(lean_object* v_s_1375_, lean_object* v_t_1376_, lean_object* v_spos_1377_, lean_object* v_tpos_1378_){
_start:
{
lean_object* v_str_1379_; lean_object* v_stopPos_1380_; uint8_t v___x_1381_; 
v_str_1379_ = lean_ctor_get(v_s_1375_, 0);
v_stopPos_1380_ = lean_ctor_get(v_s_1375_, 2);
v___x_1381_ = l_String_instDecidableLtRaw___aux__1(v_spos_1377_, v_stopPos_1380_);
if (v___x_1381_ == 0)
{
lean_dec(v_tpos_1378_);
return v_spos_1377_;
}
else
{
lean_object* v_str_1382_; lean_object* v_stopPos_1383_; uint8_t v___x_1384_; 
v_str_1382_ = lean_ctor_get(v_t_1376_, 0);
v_stopPos_1383_ = lean_ctor_get(v_t_1376_, 2);
v___x_1384_ = l_String_instDecidableLtRaw___aux__1(v_tpos_1378_, v_stopPos_1383_);
if (v___x_1384_ == 0)
{
lean_dec(v_tpos_1378_);
return v_spos_1377_;
}
else
{
uint32_t v___x_1385_; uint32_t v___x_1386_; uint8_t v___x_1387_; 
v___x_1385_ = lean_string_utf8_get(v_str_1379_, v_spos_1377_);
v___x_1386_ = lean_string_utf8_get(v_str_1382_, v_tpos_1378_);
v___x_1387_ = lean_uint32_dec_eq(v___x_1385_, v___x_1386_);
if (v___x_1387_ == 0)
{
lean_dec(v_tpos_1378_);
return v_spos_1377_;
}
else
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = lean_string_utf8_next(v_str_1379_, v_spos_1377_);
lean_dec(v_spos_1377_);
v___x_1389_ = lean_string_utf8_next(v_str_1382_, v_tpos_1378_);
lean_dec(v_tpos_1378_);
v_spos_1377_ = v___x_1388_;
v_tpos_1378_ = v___x_1389_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop___boxed(lean_object* v_s_1391_, lean_object* v_t_1392_, lean_object* v_spos_1393_, lean_object* v_tpos_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(v_s_1391_, v_t_1392_, v_spos_1393_, v_tpos_1394_);
lean_dec_ref(v_t_1392_);
lean_dec_ref(v_s_1391_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_commonPrefix(lean_object* v_s_1396_, lean_object* v_t_1397_){
_start:
{
lean_object* v_str_1398_; lean_object* v_startPos_1399_; lean_object* v_startPos_1400_; lean_object* v___x_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1408_; 
v_str_1398_ = lean_ctor_get(v_s_1396_, 0);
lean_inc_ref(v_str_1398_);
v_startPos_1399_ = lean_ctor_get(v_s_1396_, 1);
lean_inc_n(v_startPos_1399_, 2);
v_startPos_1400_ = lean_ctor_get(v_t_1397_, 1);
lean_inc(v_startPos_1400_);
v___x_1401_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(v_s_1396_, v_t_1397_, v_startPos_1399_, v_startPos_1400_);
lean_dec_ref(v_s_1396_);
v_isSharedCheck_1408_ = !lean_is_exclusive(v_t_1397_);
if (v_isSharedCheck_1408_ == 0)
{
lean_object* v_unused_1409_; lean_object* v_unused_1410_; lean_object* v_unused_1411_; 
v_unused_1409_ = lean_ctor_get(v_t_1397_, 2);
lean_dec(v_unused_1409_);
v_unused_1410_ = lean_ctor_get(v_t_1397_, 1);
lean_dec(v_unused_1410_);
v_unused_1411_ = lean_ctor_get(v_t_1397_, 0);
lean_dec(v_unused_1411_);
v___x_1403_ = v_t_1397_;
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
else
{
lean_dec(v_t_1397_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 2, v___x_1401_);
lean_ctor_set(v___x_1403_, 1, v_startPos_1399_);
lean_ctor_set(v___x_1403_, 0, v_str_1398_);
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_str_1398_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v_startPos_1399_);
lean_ctor_set(v_reuseFailAlloc_1407_, 2, v___x_1401_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(lean_object* v_s_1412_, lean_object* v_t_1413_, lean_object* v_spos_1414_, lean_object* v_tpos_1415_){
_start:
{
lean_object* v_str_1416_; lean_object* v_startPos_1417_; uint8_t v___x_1418_; 
v_str_1416_ = lean_ctor_get(v_s_1412_, 0);
v_startPos_1417_ = lean_ctor_get(v_s_1412_, 1);
v___x_1418_ = l_String_instDecidableLtRaw___aux__1(v_startPos_1417_, v_spos_1414_);
if (v___x_1418_ == 0)
{
lean_dec(v_tpos_1415_);
return v_spos_1414_;
}
else
{
lean_object* v_str_1419_; lean_object* v_startPos_1420_; uint8_t v___x_1421_; 
v_str_1419_ = lean_ctor_get(v_t_1413_, 0);
v_startPos_1420_ = lean_ctor_get(v_t_1413_, 1);
v___x_1421_ = l_String_instDecidableLtRaw___aux__1(v_startPos_1420_, v_tpos_1415_);
if (v___x_1421_ == 0)
{
lean_dec(v_tpos_1415_);
return v_spos_1414_;
}
else
{
lean_object* v_spos_x27_1422_; lean_object* v_tpos_x27_1423_; uint32_t v___x_1424_; uint32_t v___x_1425_; uint8_t v___x_1426_; 
v_spos_x27_1422_ = lean_string_utf8_prev(v_str_1416_, v_spos_1414_);
v_tpos_x27_1423_ = lean_string_utf8_prev(v_str_1419_, v_tpos_1415_);
lean_dec(v_tpos_1415_);
v___x_1424_ = lean_string_utf8_get(v_str_1416_, v_spos_x27_1422_);
v___x_1425_ = lean_string_utf8_get(v_str_1419_, v_tpos_x27_1423_);
v___x_1426_ = lean_uint32_dec_eq(v___x_1424_, v___x_1425_);
if (v___x_1426_ == 0)
{
lean_dec(v_tpos_x27_1423_);
lean_dec(v_spos_x27_1422_);
return v_spos_1414_;
}
else
{
lean_dec(v_spos_1414_);
v_spos_1414_ = v_spos_x27_1422_;
v_tpos_1415_ = v_tpos_x27_1423_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop___boxed(lean_object* v_s_1428_, lean_object* v_t_1429_, lean_object* v_spos_1430_, lean_object* v_tpos_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(v_s_1428_, v_t_1429_, v_spos_1430_, v_tpos_1431_);
lean_dec_ref(v_t_1429_);
lean_dec_ref(v_s_1428_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_commonSuffix(lean_object* v_s_1433_, lean_object* v_t_1434_){
_start:
{
lean_object* v_str_1435_; lean_object* v_stopPos_1436_; lean_object* v_stopPos_1437_; lean_object* v___x_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
v_str_1435_ = lean_ctor_get(v_s_1433_, 0);
lean_inc_ref(v_str_1435_);
v_stopPos_1436_ = lean_ctor_get(v_s_1433_, 2);
lean_inc_n(v_stopPos_1436_, 2);
v_stopPos_1437_ = lean_ctor_get(v_t_1434_, 2);
lean_inc(v_stopPos_1437_);
v___x_1438_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(v_s_1433_, v_t_1434_, v_stopPos_1436_, v_stopPos_1437_);
lean_dec_ref(v_s_1433_);
v_isSharedCheck_1445_ = !lean_is_exclusive(v_t_1434_);
if (v_isSharedCheck_1445_ == 0)
{
lean_object* v_unused_1446_; lean_object* v_unused_1447_; lean_object* v_unused_1448_; 
v_unused_1446_ = lean_ctor_get(v_t_1434_, 2);
lean_dec(v_unused_1446_);
v_unused_1447_ = lean_ctor_get(v_t_1434_, 1);
lean_dec(v_unused_1447_);
v_unused_1448_ = lean_ctor_get(v_t_1434_, 0);
lean_dec(v_unused_1448_);
v___x_1440_ = v_t_1434_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_dec(v_t_1434_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 2, v_stopPos_1436_);
lean_ctor_set(v___x_1440_, 1, v___x_1438_);
lean_ctor_set(v___x_1440_, 0, v_str_1435_);
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_str_1435_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1444_, 2, v_stopPos_1436_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropPrefix_x3f(lean_object* v_s_1449_, lean_object* v_pre_1450_){
_start:
{
lean_object* v_t_1451_; lean_object* v_startPos_1452_; lean_object* v_stopPos_1453_; lean_object* v_startPos_1454_; lean_object* v_stopPos_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; uint8_t v___x_1458_; 
lean_inc_ref(v_pre_1450_);
lean_inc_ref(v_s_1449_);
v_t_1451_ = l_Substring_Raw_commonPrefix(v_s_1449_, v_pre_1450_);
v_startPos_1452_ = lean_ctor_get(v_t_1451_, 1);
lean_inc(v_startPos_1452_);
v_stopPos_1453_ = lean_ctor_get(v_t_1451_, 2);
lean_inc(v_stopPos_1453_);
lean_dec_ref(v_t_1451_);
v_startPos_1454_ = lean_ctor_get(v_pre_1450_, 1);
lean_inc(v_startPos_1454_);
v_stopPos_1455_ = lean_ctor_get(v_pre_1450_, 2);
lean_inc(v_stopPos_1455_);
lean_dec_ref(v_pre_1450_);
v___x_1456_ = lean_nat_sub(v_stopPos_1453_, v_startPos_1452_);
lean_dec(v_startPos_1452_);
v___x_1457_ = lean_nat_sub(v_stopPos_1455_, v_startPos_1454_);
lean_dec(v_startPos_1454_);
lean_dec(v_stopPos_1455_);
v___x_1458_ = lean_nat_dec_eq(v___x_1456_, v___x_1457_);
lean_dec(v___x_1457_);
lean_dec(v___x_1456_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1459_; 
lean_dec(v_stopPos_1453_);
lean_dec_ref(v_s_1449_);
v___x_1459_ = lean_box(0);
return v___x_1459_;
}
else
{
lean_object* v_str_1460_; lean_object* v_stopPos_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1469_; 
v_str_1460_ = lean_ctor_get(v_s_1449_, 0);
v_stopPos_1461_ = lean_ctor_get(v_s_1449_, 2);
v_isSharedCheck_1469_ = !lean_is_exclusive(v_s_1449_);
if (v_isSharedCheck_1469_ == 0)
{
lean_object* v_unused_1470_; 
v_unused_1470_ = lean_ctor_get(v_s_1449_, 1);
lean_dec(v_unused_1470_);
v___x_1463_ = v_s_1449_;
v_isShared_1464_ = v_isSharedCheck_1469_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_stopPos_1461_);
lean_inc(v_str_1460_);
lean_dec(v_s_1449_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1469_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 1, v_stopPos_1453_);
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_str_1460_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_stopPos_1453_);
lean_ctor_set(v_reuseFailAlloc_1468_, 2, v_stopPos_1461_);
v___x_1466_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
lean_object* v___x_1467_; 
v___x_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
return v___x_1467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropSuffix_x3f(lean_object* v_s_1471_, lean_object* v_suff_1472_){
_start:
{
lean_object* v_t_1473_; lean_object* v_startPos_1474_; lean_object* v_stopPos_1475_; lean_object* v_startPos_1476_; lean_object* v_stopPos_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; uint8_t v___x_1480_; 
lean_inc_ref(v_suff_1472_);
lean_inc_ref(v_s_1471_);
v_t_1473_ = l_Substring_Raw_commonSuffix(v_s_1471_, v_suff_1472_);
v_startPos_1474_ = lean_ctor_get(v_t_1473_, 1);
lean_inc(v_startPos_1474_);
v_stopPos_1475_ = lean_ctor_get(v_t_1473_, 2);
lean_inc(v_stopPos_1475_);
lean_dec_ref(v_t_1473_);
v_startPos_1476_ = lean_ctor_get(v_suff_1472_, 1);
lean_inc(v_startPos_1476_);
v_stopPos_1477_ = lean_ctor_get(v_suff_1472_, 2);
lean_inc(v_stopPos_1477_);
lean_dec_ref(v_suff_1472_);
v___x_1478_ = lean_nat_sub(v_stopPos_1475_, v_startPos_1474_);
lean_dec(v_stopPos_1475_);
v___x_1479_ = lean_nat_sub(v_stopPos_1477_, v_startPos_1476_);
lean_dec(v_startPos_1476_);
lean_dec(v_stopPos_1477_);
v___x_1480_ = lean_nat_dec_eq(v___x_1478_, v___x_1479_);
lean_dec(v___x_1479_);
lean_dec(v___x_1478_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; 
lean_dec(v_startPos_1474_);
lean_dec_ref(v_s_1471_);
v___x_1481_ = lean_box(0);
return v___x_1481_;
}
else
{
lean_object* v_str_1482_; lean_object* v_startPos_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1491_; 
v_str_1482_ = lean_ctor_get(v_s_1471_, 0);
v_startPos_1483_ = lean_ctor_get(v_s_1471_, 1);
v_isSharedCheck_1491_ = !lean_is_exclusive(v_s_1471_);
if (v_isSharedCheck_1491_ == 0)
{
lean_object* v_unused_1492_; 
v_unused_1492_ = lean_ctor_get(v_s_1471_, 2);
lean_dec(v_unused_1492_);
v___x_1485_ = v_s_1471_;
v_isShared_1486_ = v_isSharedCheck_1491_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_startPos_1483_);
lean_inc(v_str_1482_);
lean_dec(v_s_1471_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1491_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 2, v_startPos_1474_);
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_str_1482_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_startPos_1483_);
lean_ctor_set(v_reuseFailAlloc_1490_, 2, v_startPos_1474_);
v___x_1488_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
lean_object* v___x_1489_; 
v___x_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
return v___x_1489_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg(lean_object* v_x_1493_, lean_object* v_x_1494_, lean_object* v_x_1495_, lean_object* v_h__1_1496_, lean_object* v_h__2_1497_){
_start:
{
lean_object* v_zero_1498_; uint8_t v_isZero_1499_; 
v_zero_1498_ = lean_unsigned_to_nat(0u);
v_isZero_1499_ = lean_nat_dec_eq(v_x_1494_, v_zero_1498_);
if (v_isZero_1499_ == 1)
{
lean_object* v___x_1500_; 
lean_dec(v_h__2_1497_);
v___x_1500_ = lean_apply_2(v_h__1_1496_, v_x_1493_, v_x_1495_);
return v___x_1500_;
}
else
{
lean_object* v_one_1501_; lean_object* v_n_1502_; lean_object* v___x_1503_; 
lean_dec(v_h__1_1496_);
v_one_1501_ = lean_unsigned_to_nat(1u);
v_n_1502_ = lean_nat_sub(v_x_1494_, v_one_1501_);
v___x_1503_ = lean_apply_3(v_h__2_1497_, v_x_1493_, v_n_1502_, v_x_1495_);
return v___x_1503_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg___boxed(lean_object* v_x_1504_, lean_object* v_x_1505_, lean_object* v_x_1506_, lean_object* v_h__1_1507_, lean_object* v_h__2_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg(v_x_1504_, v_x_1505_, v_x_1506_, v_h__1_1507_, v_h__2_1508_);
lean_dec(v_x_1505_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter(lean_object* v_motive_1510_, lean_object* v_x_1511_, lean_object* v_x_1512_, lean_object* v_x_1513_, lean_object* v_h__1_1514_, lean_object* v_h__2_1515_){
_start:
{
lean_object* v_zero_1516_; uint8_t v_isZero_1517_; 
v_zero_1516_ = lean_unsigned_to_nat(0u);
v_isZero_1517_ = lean_nat_dec_eq(v_x_1512_, v_zero_1516_);
if (v_isZero_1517_ == 1)
{
lean_object* v___x_1518_; 
lean_dec(v_h__2_1515_);
v___x_1518_ = lean_apply_2(v_h__1_1514_, v_x_1511_, v_x_1513_);
return v___x_1518_;
}
else
{
lean_object* v_one_1519_; lean_object* v_n_1520_; lean_object* v___x_1521_; 
lean_dec(v_h__1_1514_);
v_one_1519_ = lean_unsigned_to_nat(1u);
v_n_1520_ = lean_nat_sub(v_x_1512_, v_one_1519_);
v___x_1521_ = lean_apply_3(v_h__2_1515_, v_x_1511_, v_n_1520_, v_x_1513_);
return v___x_1521_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___boxed(lean_object* v_motive_1522_, lean_object* v_x_1523_, lean_object* v_x_1524_, lean_object* v_x_1525_, lean_object* v_h__1_1526_, lean_object* v_h__2_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter(v_motive_1522_, v_x_1523_, v_x_1524_, v_x_1525_, v_h__1_1526_, v_h__2_1527_);
lean_dec(v_x_1524_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Substring_bsize(lean_object* v_a_1529_){
_start:
{
lean_object* v_startPos_1530_; lean_object* v_stopPos_1531_; lean_object* v___x_1532_; 
v_startPos_1530_ = lean_ctor_get(v_a_1529_, 1);
v_stopPos_1531_ = lean_ctor_get(v_a_1529_, 2);
v___x_1532_ = lean_nat_sub(v_stopPos_1531_, v_startPos_1530_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Substring_bsize___boxed(lean_object* v_a_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Substring_bsize(v_a_1533_);
lean_dec_ref(v_a_1533_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Substring_toString(lean_object* v_a_1535_){
_start:
{
lean_object* v_str_1536_; lean_object* v_startPos_1537_; lean_object* v_stopPos_1538_; lean_object* v___x_1539_; 
v_str_1536_ = lean_ctor_get(v_a_1535_, 0);
v_startPos_1537_ = lean_ctor_get(v_a_1535_, 1);
v_stopPos_1538_ = lean_ctor_get(v_a_1535_, 2);
v___x_1539_ = lean_string_utf8_extract(v_str_1536_, v_startPos_1537_, v_stopPos_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Substring_toString___boxed(lean_object* v_a_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Substring_toString(v_a_1540_);
lean_dec_ref(v_a_1540_);
return v_res_1541_;
}
}
LEAN_EXPORT uint8_t l_Substring_isEmpty(lean_object* v_ss_1542_){
_start:
{
lean_object* v_startPos_1543_; lean_object* v_stopPos_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; uint8_t v___x_1547_; 
v_startPos_1543_ = lean_ctor_get(v_ss_1542_, 1);
v_stopPos_1544_ = lean_ctor_get(v_ss_1542_, 2);
v___x_1545_ = lean_nat_sub(v_stopPos_1544_, v_startPos_1543_);
v___x_1546_ = lean_unsigned_to_nat(0u);
v___x_1547_ = lean_nat_dec_eq(v___x_1545_, v___x_1546_);
lean_dec(v___x_1545_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Substring_isEmpty___boxed(lean_object* v_ss_1548_){
_start:
{
uint8_t v_res_1549_; lean_object* v_r_1550_; 
v_res_1549_ = l_Substring_isEmpty(v_ss_1548_);
lean_dec_ref(v_ss_1548_);
v_r_1550_ = lean_box(v_res_1549_);
return v_r_1550_;
}
}
LEAN_EXPORT lean_object* l_Substring_next(lean_object* v_a_1551_, lean_object* v_a_1552_){
_start:
{
lean_object* v_str_1553_; lean_object* v_startPos_1554_; lean_object* v_stopPos_1555_; lean_object* v_absP_1556_; uint8_t v___x_1557_; 
v_str_1553_ = lean_ctor_get(v_a_1551_, 0);
v_startPos_1554_ = lean_ctor_get(v_a_1551_, 1);
v_stopPos_1555_ = lean_ctor_get(v_a_1551_, 2);
v_absP_1556_ = lean_nat_add(v_startPos_1554_, v_a_1552_);
v___x_1557_ = lean_nat_dec_eq(v_absP_1556_, v_stopPos_1555_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = lean_string_utf8_next(v_str_1553_, v_absP_1556_);
lean_dec(v_absP_1556_);
v___x_1559_ = lean_nat_sub(v___x_1558_, v_startPos_1554_);
lean_dec(v___x_1558_);
return v___x_1559_;
}
else
{
lean_dec(v_absP_1556_);
lean_inc(v_a_1552_);
return v_a_1552_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_next___boxed(lean_object* v_a_1560_, lean_object* v_a_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l_Substring_next(v_a_1560_, v_a_1561_);
lean_dec(v_a_1561_);
lean_dec_ref(v_a_1560_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_Substring_prev(lean_object* v_a_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v_str_1565_; lean_object* v_startPos_1566_; lean_object* v_absP_1567_; uint8_t v___x_1568_; 
v_str_1565_ = lean_ctor_get(v_a_1563_, 0);
v_startPos_1566_ = lean_ctor_get(v_a_1563_, 1);
v_absP_1567_ = lean_nat_add(v_startPos_1566_, v_a_1564_);
v___x_1568_ = lean_nat_dec_eq(v_absP_1567_, v_startPos_1566_);
if (v___x_1568_ == 0)
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = lean_string_utf8_prev(v_str_1565_, v_absP_1567_);
lean_dec(v_absP_1567_);
v___x_1570_ = lean_nat_sub(v___x_1569_, v_startPos_1566_);
lean_dec(v___x_1569_);
return v___x_1570_;
}
else
{
lean_dec(v_absP_1567_);
lean_inc(v_a_1564_);
return v_a_1564_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_prev___boxed(lean_object* v_a_1571_, lean_object* v_a_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Substring_prev(v_a_1571_, v_a_1572_);
lean_dec(v_a_1572_);
lean_dec_ref(v_a_1571_);
return v_res_1573_;
}
}
LEAN_EXPORT uint8_t l_Substring_atEnd(lean_object* v_a_1574_, lean_object* v_a_1575_){
_start:
{
lean_object* v_startPos_1576_; lean_object* v_stopPos_1577_; lean_object* v___x_1578_; uint8_t v___x_1579_; 
v_startPos_1576_ = lean_ctor_get(v_a_1574_, 1);
v_stopPos_1577_ = lean_ctor_get(v_a_1574_, 2);
v___x_1578_ = lean_nat_add(v_startPos_1576_, v_a_1575_);
v___x_1579_ = lean_nat_dec_eq(v___x_1578_, v_stopPos_1577_);
lean_dec(v___x_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Substring_atEnd___boxed(lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
uint8_t v_res_1582_; lean_object* v_r_1583_; 
v_res_1582_ = l_Substring_atEnd(v_a_1580_, v_a_1581_);
lean_dec(v_a_1581_);
lean_dec_ref(v_a_1580_);
v_r_1583_ = lean_box(v_res_1582_);
return v_r_1583_;
}
}
LEAN_EXPORT uint8_t l_Substring_beq(lean_object* v_ss1_1584_, lean_object* v_ss2_1585_){
_start:
{
uint8_t v___x_1586_; 
v___x_1586_ = l_Substring_Raw_beq(v_ss1_1584_, v_ss2_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Substring_beq___boxed(lean_object* v_ss1_1587_, lean_object* v_ss2_1588_){
_start:
{
uint8_t v_res_1589_; lean_object* v_r_1590_; 
v_res_1589_ = l_Substring_beq(v_ss1_1587_, v_ss2_1588_);
v_r_1590_ = lean_box(v_res_1589_);
return v_r_1590_;
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

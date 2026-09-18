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
static lean_object* _init_l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__0(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = ((lean_object*)(l_Substring_Raw_extract___closed__0));
v___x_390_ = lean_string_utf8_byte_size(v___x_389_);
return v___x_390_;
}
}
static lean_object* _init_l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__1(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_391_ = lean_obj_once(&l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__0, &l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__0_once, _init_l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__0);
v___x_392_ = lean_unsigned_to_nat(0u);
v___x_393_ = ((lean_object*)(l_Substring_Raw_extract___closed__0));
v___x_394_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v___x_392_);
lean_ctor_set(v___x_394_, 2, v___x_391_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop(lean_object* v_s_395_, lean_object* v_sep_396_, lean_object* v_b_397_, lean_object* v_i_398_, lean_object* v_j_399_, lean_object* v_r_400_){
_start:
{
lean_object* v___y_402_; lean_object* v___y_406_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v_str_415_; lean_object* v_startPos_416_; lean_object* v_stopPos_417_; lean_object* v___y_419_; lean_object* v___y_420_; lean_object* v___y_421_; lean_object* v___y_422_; lean_object* v___y_428_; lean_object* v___y_439_; lean_object* v___x_444_; uint8_t v___x_445_; 
v_str_415_ = lean_ctor_get(v_s_395_, 0);
v_startPos_416_ = lean_ctor_get(v_s_395_, 1);
v_stopPos_417_ = lean_ctor_get(v_s_395_, 2);
v___x_444_ = lean_nat_sub(v_stopPos_417_, v_startPos_416_);
v___x_445_ = lean_nat_dec_lt(v_i_398_, v___x_444_);
lean_dec(v___x_444_);
if (v___x_445_ == 0)
{
lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_475_; 
lean_inc(v_stopPos_417_);
lean_inc(v_startPos_416_);
lean_inc_ref(v_str_415_);
v_isSharedCheck_475_ = !lean_is_exclusive(v_s_395_);
if (v_isSharedCheck_475_ == 0)
{
lean_object* v_unused_476_; lean_object* v_unused_477_; lean_object* v_unused_478_; 
v_unused_476_ = lean_ctor_get(v_s_395_, 2);
lean_dec(v_unused_476_);
v_unused_477_ = lean_ctor_get(v_s_395_, 1);
lean_dec(v_unused_477_);
v_unused_478_ = lean_ctor_get(v_s_395_, 0);
lean_dec(v_unused_478_);
v___x_447_ = v_s_395_;
v_isShared_448_ = v_isSharedCheck_475_;
goto v_resetjp_446_;
}
else
{
lean_dec(v_s_395_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_475_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
uint8_t v___x_449_; 
v___x_449_ = lean_string_utf8_at_end(v_sep_396_, v_j_399_);
if (v___x_449_ == 0)
{
uint8_t v___x_450_; 
lean_del_object(v___x_447_);
lean_dec(v_j_399_);
v___x_450_ = lean_nat_dec_le(v_i_398_, v_b_397_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_451_ = lean_nat_add(v_startPos_416_, v_b_397_);
lean_dec(v_b_397_);
v___x_452_ = lean_nat_dec_le(v_stopPos_417_, v___x_451_);
if (v___x_452_ == 0)
{
v___y_439_ = v___x_451_;
goto v___jp_438_;
}
else
{
lean_dec(v___x_451_);
lean_inc(v_stopPos_417_);
v___y_439_ = v_stopPos_417_;
goto v___jp_438_;
}
}
else
{
lean_object* v___x_453_; 
lean_dec(v_stopPos_417_);
lean_dec(v_startPos_416_);
lean_dec_ref(v_str_415_);
lean_dec(v_i_398_);
lean_dec(v_b_397_);
v___x_453_ = ((lean_object*)(l_Substring_Raw_extract___closed__1));
v___y_402_ = v___x_453_;
goto v___jp_401_;
}
}
else
{
lean_object* v___x_454_; lean_object* v___y_456_; lean_object* v___x_460_; lean_object* v___y_462_; uint8_t v___x_471_; 
v___x_454_ = lean_obj_once(&l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__1, &l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__1_once, _init_l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___closed__1);
v___x_460_ = lean_nat_sub(v_i_398_, v_j_399_);
lean_dec(v_j_399_);
lean_dec(v_i_398_);
v___x_471_ = lean_nat_dec_le(v___x_460_, v_b_397_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_472_ = lean_nat_add(v_startPos_416_, v_b_397_);
lean_dec(v_b_397_);
v___x_473_ = lean_nat_dec_le(v_stopPos_417_, v___x_472_);
if (v___x_473_ == 0)
{
v___y_462_ = v___x_472_;
goto v___jp_461_;
}
else
{
lean_dec(v___x_472_);
lean_inc(v_stopPos_417_);
v___y_462_ = v_stopPos_417_;
goto v___jp_461_;
}
}
else
{
lean_object* v___x_474_; 
lean_dec(v___x_460_);
lean_del_object(v___x_447_);
lean_dec(v_stopPos_417_);
lean_dec(v_startPos_416_);
lean_dec_ref(v_str_415_);
lean_dec(v_b_397_);
v___x_474_ = ((lean_object*)(l_Substring_Raw_extract___closed__1));
v___y_456_ = v___x_474_;
goto v___jp_455_;
}
v___jp_455_:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_457_, 0, v___y_456_);
lean_ctor_set(v___x_457_, 1, v_r_400_);
v___x_458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_454_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
v___x_459_ = l_List_reverse___redArg(v___x_458_);
return v___x_459_;
}
v___jp_461_:
{
lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_463_ = lean_nat_add(v_startPos_416_, v___x_460_);
lean_dec(v___x_460_);
lean_dec(v_startPos_416_);
v___x_464_ = lean_nat_dec_le(v_stopPos_417_, v___x_463_);
if (v___x_464_ == 0)
{
lean_object* v___x_466_; 
lean_dec(v_stopPos_417_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 2, v___x_463_);
lean_ctor_set(v___x_447_, 1, v___y_462_);
v___x_466_ = v___x_447_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_str_415_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v___y_462_);
lean_ctor_set(v_reuseFailAlloc_467_, 2, v___x_463_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
v___y_456_ = v___x_466_;
goto v___jp_455_;
}
}
else
{
lean_object* v___x_469_; 
lean_dec(v___x_463_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 1, v___y_462_);
v___x_469_ = v___x_447_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_str_415_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v___y_462_);
lean_ctor_set(v_reuseFailAlloc_470_, 2, v_stopPos_417_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
v___y_456_ = v___x_469_;
goto v___jp_455_;
}
}
}
}
}
}
else
{
lean_object* v___x_479_; uint32_t v___x_480_; uint32_t v___x_481_; uint8_t v___x_482_; 
v___x_479_ = lean_nat_add(v_startPos_416_, v_i_398_);
v___x_480_ = lean_string_utf8_get(v_str_415_, v___x_479_);
v___x_481_ = lean_string_utf8_get(v_sep_396_, v_j_399_);
v___x_482_ = lean_uint32_dec_eq(v___x_480_, v___x_481_);
if (v___x_482_ == 0)
{
uint8_t v_decide_483_; 
lean_dec(v_j_399_);
v_decide_483_ = lean_nat_dec_eq(v___x_479_, v_stopPos_417_);
if (v_decide_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; 
lean_dec(v_i_398_);
v___x_484_ = lean_string_utf8_next(v_str_415_, v___x_479_);
lean_dec(v___x_479_);
v___x_485_ = lean_nat_sub(v___x_484_, v_startPos_416_);
lean_dec(v___x_484_);
v___y_406_ = v___x_485_;
goto v___jp_405_;
}
else
{
lean_dec(v___x_479_);
v___y_406_ = v_i_398_;
goto v___jp_405_;
}
}
else
{
uint8_t v_decide_486_; 
v_decide_486_ = lean_nat_dec_eq(v___x_479_, v_stopPos_417_);
if (v_decide_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_488_; 
lean_dec(v_i_398_);
v___x_487_ = lean_string_utf8_next(v_str_415_, v___x_479_);
lean_dec(v___x_479_);
v___x_488_ = lean_nat_sub(v___x_487_, v_startPos_416_);
lean_dec(v___x_487_);
v___y_428_ = v___x_488_;
goto v___jp_427_;
}
else
{
lean_dec(v___x_479_);
v___y_428_ = v_i_398_;
goto v___jp_427_;
}
}
}
v___jp_401_:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_403_, 0, v___y_402_);
lean_ctor_set(v___x_403_, 1, v_r_400_);
v___x_404_ = l_List_reverse___redArg(v___x_403_);
return v___x_404_;
}
v___jp_405_:
{
lean_object* v___x_407_; 
v___x_407_ = lean_unsigned_to_nat(0u);
v_i_398_ = v___y_406_;
v_j_399_ = v___x_407_;
goto _start;
}
v___jp_409_:
{
lean_object* v___x_413_; 
v___x_413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_413_, 0, v___y_412_);
lean_ctor_set(v___x_413_, 1, v_r_400_);
lean_inc(v___y_411_);
v_b_397_ = v___y_411_;
v_i_398_ = v___y_411_;
v_j_399_ = v___y_410_;
v_r_400_ = v___x_413_;
goto _start;
}
v___jp_418_:
{
lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_423_ = lean_nat_add(v_startPos_416_, v___y_420_);
lean_dec(v___y_420_);
v___x_424_ = lean_nat_dec_le(v_stopPos_417_, v___x_423_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; 
lean_inc_ref(v_str_415_);
v___x_425_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_425_, 0, v_str_415_);
lean_ctor_set(v___x_425_, 1, v___y_422_);
lean_ctor_set(v___x_425_, 2, v___x_423_);
v___y_410_ = v___y_419_;
v___y_411_ = v___y_421_;
v___y_412_ = v___x_425_;
goto v___jp_409_;
}
else
{
lean_object* v___x_426_; 
lean_dec(v___x_423_);
lean_inc(v_stopPos_417_);
lean_inc_ref(v_str_415_);
v___x_426_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_426_, 0, v_str_415_);
lean_ctor_set(v___x_426_, 1, v___y_422_);
lean_ctor_set(v___x_426_, 2, v_stopPos_417_);
v___y_410_ = v___y_419_;
v___y_411_ = v___y_421_;
v___y_412_ = v___x_426_;
goto v___jp_409_;
}
}
v___jp_427_:
{
lean_object* v_j_429_; uint8_t v___x_430_; 
v_j_429_ = lean_string_utf8_next(v_sep_396_, v_j_399_);
lean_dec(v_j_399_);
v___x_430_ = lean_string_utf8_at_end(v_sep_396_, v_j_429_);
if (v___x_430_ == 0)
{
v_i_398_ = v___y_428_;
v_j_399_ = v_j_429_;
goto _start;
}
else
{
lean_object* v___x_432_; lean_object* v___x_433_; uint8_t v___x_434_; 
v___x_432_ = lean_unsigned_to_nat(0u);
v___x_433_ = lean_nat_sub(v___y_428_, v_j_429_);
lean_dec(v_j_429_);
v___x_434_ = lean_nat_dec_le(v___x_433_, v_b_397_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; uint8_t v___x_436_; 
v___x_435_ = lean_nat_add(v_startPos_416_, v_b_397_);
lean_dec(v_b_397_);
v___x_436_ = lean_nat_dec_le(v_stopPos_417_, v___x_435_);
if (v___x_436_ == 0)
{
v___y_419_ = v___x_432_;
v___y_420_ = v___x_433_;
v___y_421_ = v___y_428_;
v___y_422_ = v___x_435_;
goto v___jp_418_;
}
else
{
lean_dec(v___x_435_);
lean_inc(v_stopPos_417_);
v___y_419_ = v___x_432_;
v___y_420_ = v___x_433_;
v___y_421_ = v___y_428_;
v___y_422_ = v_stopPos_417_;
goto v___jp_418_;
}
}
else
{
lean_object* v___x_437_; 
lean_dec(v___x_433_);
lean_dec(v_b_397_);
v___x_437_ = ((lean_object*)(l_Substring_Raw_extract___closed__1));
v___y_410_ = v___x_432_;
v___y_411_ = v___y_428_;
v___y_412_ = v___x_437_;
goto v___jp_409_;
}
}
}
v___jp_438_:
{
lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_440_ = lean_nat_add(v_startPos_416_, v_i_398_);
lean_dec(v_i_398_);
lean_dec(v_startPos_416_);
v___x_441_ = lean_nat_dec_le(v_stopPos_417_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; 
lean_dec(v_stopPos_417_);
v___x_442_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_442_, 0, v_str_415_);
lean_ctor_set(v___x_442_, 1, v___y_439_);
lean_ctor_set(v___x_442_, 2, v___x_440_);
v___y_402_ = v___x_442_;
goto v___jp_401_;
}
else
{
lean_object* v___x_443_; 
lean_dec(v___x_440_);
v___x_443_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_443_, 0, v_str_415_);
lean_ctor_set(v___x_443_, 1, v___y_439_);
lean_ctor_set(v___x_443_, 2, v_stopPos_417_);
v___y_402_ = v___x_443_;
goto v___jp_401_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop___boxed(lean_object* v_s_489_, lean_object* v_sep_490_, lean_object* v_b_491_, lean_object* v_i_492_, lean_object* v_j_493_, lean_object* v_r_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop(v_s_489_, v_sep_490_, v_b_491_, v_i_492_, v_j_493_, v_r_494_);
lean_dec_ref(v_sep_490_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_splitOn(lean_object* v_s_496_, lean_object* v_sep_497_){
_start:
{
lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_498_ = ((lean_object*)(l_Substring_Raw_extract___closed__0));
v___x_499_ = lean_string_dec_eq(v_sep_497_, v___x_498_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_500_ = lean_unsigned_to_nat(0u);
v___x_501_ = lean_box(0);
v___x_502_ = l___private_Init_Data_String_Substring_0__Substring_Raw_splitOn_loop(v_s_496_, v_sep_497_, v___x_500_, v___x_500_, v___x_500_, v___x_501_);
return v___x_502_;
}
else
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = lean_box(0);
v___x_504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_504_, 0, v_s_496_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
return v___x_504_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_splitOn___boxed(lean_object* v_s_505_, lean_object* v_sep_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Substring_Raw_splitOn(v_s_505_, v_sep_506_);
lean_dec_ref(v_sep_506_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldl___redArg___lam__0(lean_object* v___y_508_, lean_object* v_f_509_, lean_object* v_it_510_, lean_object* v_acc_511_, lean_object* v_hP_512_, lean_object* v_recur_513_){
_start:
{
lean_object* v_str_514_; lean_object* v_startInclusive_515_; lean_object* v_endExclusive_516_; lean_object* v___x_517_; uint8_t v_decide_518_; 
v_str_514_ = lean_ctor_get(v___y_508_, 0);
v_startInclusive_515_ = lean_ctor_get(v___y_508_, 1);
v_endExclusive_516_ = lean_ctor_get(v___y_508_, 2);
v___x_517_ = lean_nat_sub(v_endExclusive_516_, v_startInclusive_515_);
v_decide_518_ = lean_nat_dec_eq(v_it_510_, v___x_517_);
lean_dec(v___x_517_);
if (v_decide_518_ == 0)
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; uint32_t v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_519_ = lean_nat_add(v_startInclusive_515_, v_it_510_);
v___x_520_ = lean_string_utf8_next_fast(v_str_514_, v___x_519_);
v___x_521_ = lean_nat_sub(v___x_520_, v_startInclusive_515_);
v___x_522_ = lean_string_utf8_get_fast(v_str_514_, v___x_519_);
lean_dec(v___x_519_);
v___x_523_ = lean_box_uint32(v___x_522_);
v___x_524_ = lean_apply_2(v_f_509_, v_acc_511_, v___x_523_);
v___x_525_ = lean_apply_4(v_recur_513_, v___x_521_, v___x_524_, lean_box(0), lean_box(0));
return v___x_525_;
}
else
{
lean_dec(v_recur_513_);
lean_dec(v_f_509_);
return v_acc_511_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldl___redArg___lam__0___boxed(lean_object* v___y_526_, lean_object* v_f_527_, lean_object* v_it_528_, lean_object* v_acc_529_, lean_object* v_hP_530_, lean_object* v_recur_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Substring_Raw_foldl___redArg___lam__0(v___y_526_, v_f_527_, v_it_528_, v_acc_529_, v_hP_530_, v_recur_531_);
lean_dec(v_it_528_);
lean_dec_ref(v___y_526_);
return v_res_532_;
}
}
static lean_object* _init_l_Substring_Raw_foldl___redArg___closed__3(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_536_ = ((lean_object*)(l_Substring_Raw_foldl___redArg___closed__2));
v___x_537_ = lean_unsigned_to_nat(14u);
v___x_538_ = lean_unsigned_to_nat(22u);
v___x_539_ = ((lean_object*)(l_Substring_Raw_foldl___redArg___closed__1));
v___x_540_ = ((lean_object*)(l_Substring_Raw_foldl___redArg___closed__0));
v___x_541_ = l_mkPanicMessageWithDecl(v___x_540_, v___x_539_, v___x_538_, v___x_537_, v___x_536_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldl___redArg(lean_object* v_f_542_, lean_object* v_init_543_, lean_object* v_s_544_){
_start:
{
lean_object* v___y_546_; lean_object* v_str_550_; lean_object* v_startPos_551_; lean_object* v_stopPos_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_569_; 
v_str_550_ = lean_ctor_get(v_s_544_, 0);
v_startPos_551_ = lean_ctor_get(v_s_544_, 1);
v_stopPos_552_ = lean_ctor_get(v_s_544_, 2);
v_isSharedCheck_569_ = !lean_is_exclusive(v_s_544_);
if (v_isSharedCheck_569_ == 0)
{
v___x_554_ = v_s_544_;
v_isShared_555_ = v_isSharedCheck_569_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_stopPos_552_);
lean_inc(v_startPos_551_);
lean_inc(v_str_550_);
lean_dec(v_s_544_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_569_;
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
lean_object* v___x_556_; uint8_t v___y_558_; uint8_t v___x_564_; uint8_t v___y_566_; uint8_t v___x_567_; 
v___x_556_ = l_String_instInhabitedSlice;
v___x_564_ = lean_string_is_valid_pos(v_str_550_, v_startPos_551_);
v___x_567_ = lean_string_is_valid_pos(v_str_550_, v_stopPos_552_);
if (v___x_567_ == 0)
{
v___y_566_ = v___x_567_;
goto v___jp_565_;
}
else
{
uint8_t v___x_568_; 
v___x_568_ = lean_nat_dec_le(v_startPos_551_, v_stopPos_552_);
v___y_566_ = v___x_568_;
goto v___jp_565_;
}
v___jp_557_:
{
if (v___y_558_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; 
lean_del_object(v___x_554_);
lean_dec(v_stopPos_552_);
lean_dec(v_startPos_551_);
lean_dec_ref(v_str_550_);
v___x_559_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_560_ = l_panic___redArg(v___x_556_, v___x_559_);
v___y_546_ = v___x_560_;
goto v___jp_545_;
}
else
{
lean_object* v___x_562_; 
if (v_isShared_555_ == 0)
{
v___x_562_ = v___x_554_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_str_550_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_startPos_551_);
lean_ctor_set(v_reuseFailAlloc_563_, 2, v_stopPos_552_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
v___y_546_ = v___x_562_;
goto v___jp_545_;
}
}
}
v___jp_565_:
{
if (v___x_564_ == 0)
{
v___y_558_ = v___x_564_;
goto v___jp_557_;
}
else
{
v___y_558_ = v___y_566_;
goto v___jp_557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldl(lean_object* v_00_u03b1_570_, lean_object* v_f_571_, lean_object* v_init_572_, lean_object* v_s_573_){
_start:
{
lean_object* v___y_575_; lean_object* v_str_579_; lean_object* v_startPos_580_; lean_object* v_stopPos_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_598_; 
v_str_579_ = lean_ctor_get(v_s_573_, 0);
v_startPos_580_ = lean_ctor_get(v_s_573_, 1);
v_stopPos_581_ = lean_ctor_get(v_s_573_, 2);
v_isSharedCheck_598_ = !lean_is_exclusive(v_s_573_);
if (v_isSharedCheck_598_ == 0)
{
v___x_583_ = v_s_573_;
v_isShared_584_ = v_isSharedCheck_598_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_stopPos_581_);
lean_inc(v_startPos_580_);
lean_inc(v_str_579_);
lean_dec(v_s_573_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_598_;
goto v_resetjp_582_;
}
v___jp_574_:
{
lean_object* v___f_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___f_576_ = lean_alloc_closure((void*)(l_Substring_Raw_foldl___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_576_, 0, v___y_575_);
lean_closure_set(v___f_576_, 1, v_f_571_);
v___x_577_ = lean_unsigned_to_nat(0u);
v___x_578_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_576_, v___x_577_, v_init_572_, lean_box(0));
return v___x_578_;
}
v_resetjp_582_:
{
lean_object* v___x_585_; uint8_t v___y_587_; uint8_t v___x_593_; uint8_t v___y_595_; uint8_t v___x_596_; 
v___x_585_ = l_String_instInhabitedSlice;
v___x_593_ = lean_string_is_valid_pos(v_str_579_, v_startPos_580_);
v___x_596_ = lean_string_is_valid_pos(v_str_579_, v_stopPos_581_);
if (v___x_596_ == 0)
{
v___y_595_ = v___x_596_;
goto v___jp_594_;
}
else
{
uint8_t v___x_597_; 
v___x_597_ = lean_nat_dec_le(v_startPos_580_, v_stopPos_581_);
v___y_595_ = v___x_597_;
goto v___jp_594_;
}
v___jp_586_:
{
if (v___y_587_ == 0)
{
lean_object* v___x_588_; lean_object* v___x_589_; 
lean_del_object(v___x_583_);
lean_dec(v_stopPos_581_);
lean_dec(v_startPos_580_);
lean_dec_ref(v_str_579_);
v___x_588_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_589_ = l_panic___redArg(v___x_585_, v___x_588_);
v___y_575_ = v___x_589_;
goto v___jp_574_;
}
else
{
lean_object* v___x_591_; 
if (v_isShared_584_ == 0)
{
v___x_591_ = v___x_583_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_str_579_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v_startPos_580_);
lean_ctor_set(v_reuseFailAlloc_592_, 2, v_stopPos_581_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
v___y_575_ = v___x_591_;
goto v___jp_574_;
}
}
}
v___jp_594_:
{
if (v___x_593_ == 0)
{
v___y_587_ = v___x_593_;
goto v___jp_586_;
}
else
{
v___y_587_ = v___y_595_;
goto v___jp_586_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr___redArg___lam__0(lean_object* v___y_599_, lean_object* v_f_600_, lean_object* v_it_601_, lean_object* v_acc_602_, lean_object* v_hP_603_, lean_object* v_recur_604_){
_start:
{
lean_object* v___x_605_; uint8_t v_decide_606_; 
v___x_605_ = lean_unsigned_to_nat(0u);
v_decide_606_ = lean_nat_dec_eq(v_it_601_, v___x_605_);
if (v_decide_606_ == 0)
{
lean_object* v_str_607_; lean_object* v_startInclusive_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v_prevPos_611_; lean_object* v___x_612_; uint32_t v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v_str_607_ = lean_ctor_get(v___y_599_, 0);
v_startInclusive_608_ = lean_ctor_get(v___y_599_, 1);
v___x_609_ = lean_unsigned_to_nat(1u);
v___x_610_ = lean_nat_sub(v_it_601_, v___x_609_);
v_prevPos_611_ = l_String_Slice_posLE(v___y_599_, v___x_610_);
v___x_612_ = lean_nat_add(v_startInclusive_608_, v_prevPos_611_);
v___x_613_ = lean_string_utf8_get_fast(v_str_607_, v___x_612_);
lean_dec(v___x_612_);
v___x_614_ = lean_box_uint32(v___x_613_);
v___x_615_ = lean_apply_2(v_f_600_, v___x_614_, v_acc_602_);
v___x_616_ = lean_apply_4(v_recur_604_, v_prevPos_611_, v___x_615_, lean_box(0), lean_box(0));
return v___x_616_;
}
else
{
lean_dec(v_recur_604_);
lean_dec(v_f_600_);
return v_acc_602_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr___redArg___lam__0___boxed(lean_object* v___y_617_, lean_object* v_f_618_, lean_object* v_it_619_, lean_object* v_acc_620_, lean_object* v_hP_621_, lean_object* v_recur_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Substring_Raw_foldr___redArg___lam__0(v___y_617_, v_f_618_, v_it_619_, v_acc_620_, v_hP_621_, v_recur_622_);
lean_dec(v_it_619_);
lean_dec_ref(v___y_617_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr___redArg(lean_object* v_f_624_, lean_object* v_init_625_, lean_object* v_s_626_){
_start:
{
lean_object* v___y_628_; lean_object* v_str_632_; lean_object* v_startPos_633_; lean_object* v_stopPos_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_651_; 
v_str_632_ = lean_ctor_get(v_s_626_, 0);
v_startPos_633_ = lean_ctor_get(v_s_626_, 1);
v_stopPos_634_ = lean_ctor_get(v_s_626_, 2);
v_isSharedCheck_651_ = !lean_is_exclusive(v_s_626_);
if (v_isSharedCheck_651_ == 0)
{
v___x_636_ = v_s_626_;
v_isShared_637_ = v_isSharedCheck_651_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_stopPos_634_);
lean_inc(v_startPos_633_);
lean_inc(v_str_632_);
lean_dec(v_s_626_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_651_;
goto v_resetjp_635_;
}
v___jp_627_:
{
lean_object* v___f_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
lean_inc_ref(v___y_628_);
v___f_629_ = lean_alloc_closure((void*)(l_Substring_Raw_foldr___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_629_, 0, v___y_628_);
lean_closure_set(v___f_629_, 1, v_f_624_);
v___x_630_ = l_String_Slice_revPositions(v___y_628_);
lean_dec_ref(v___y_628_);
v___x_631_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_629_, v___x_630_, v_init_625_, lean_box(0));
return v___x_631_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; uint8_t v___y_640_; uint8_t v___x_646_; uint8_t v___y_648_; uint8_t v___x_649_; 
v___x_638_ = l_String_instInhabitedSlice;
v___x_646_ = lean_string_is_valid_pos(v_str_632_, v_startPos_633_);
v___x_649_ = lean_string_is_valid_pos(v_str_632_, v_stopPos_634_);
if (v___x_649_ == 0)
{
v___y_648_ = v___x_649_;
goto v___jp_647_;
}
else
{
uint8_t v___x_650_; 
v___x_650_ = lean_nat_dec_le(v_startPos_633_, v_stopPos_634_);
v___y_648_ = v___x_650_;
goto v___jp_647_;
}
v___jp_639_:
{
if (v___y_640_ == 0)
{
lean_object* v___x_641_; lean_object* v___x_642_; 
lean_del_object(v___x_636_);
lean_dec(v_stopPos_634_);
lean_dec(v_startPos_633_);
lean_dec_ref(v_str_632_);
v___x_641_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_642_ = l_panic___redArg(v___x_638_, v___x_641_);
v___y_628_ = v___x_642_;
goto v___jp_627_;
}
else
{
lean_object* v___x_644_; 
if (v_isShared_637_ == 0)
{
v___x_644_ = v___x_636_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_str_632_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v_startPos_633_);
lean_ctor_set(v_reuseFailAlloc_645_, 2, v_stopPos_634_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
v___y_628_ = v___x_644_;
goto v___jp_627_;
}
}
}
v___jp_647_:
{
if (v___x_646_ == 0)
{
v___y_640_ = v___x_646_;
goto v___jp_639_;
}
else
{
v___y_640_ = v___y_648_;
goto v___jp_639_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr(lean_object* v_00_u03b1_652_, lean_object* v_f_653_, lean_object* v_init_654_, lean_object* v_s_655_){
_start:
{
lean_object* v___y_657_; lean_object* v_str_661_; lean_object* v_startPos_662_; lean_object* v_stopPos_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_680_; 
v_str_661_ = lean_ctor_get(v_s_655_, 0);
v_startPos_662_ = lean_ctor_get(v_s_655_, 1);
v_stopPos_663_ = lean_ctor_get(v_s_655_, 2);
v_isSharedCheck_680_ = !lean_is_exclusive(v_s_655_);
if (v_isSharedCheck_680_ == 0)
{
v___x_665_ = v_s_655_;
v_isShared_666_ = v_isSharedCheck_680_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_stopPos_663_);
lean_inc(v_startPos_662_);
lean_inc(v_str_661_);
lean_dec(v_s_655_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_680_;
goto v_resetjp_664_;
}
v___jp_656_:
{
lean_object* v___f_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
lean_inc_ref(v___y_657_);
v___f_658_ = lean_alloc_closure((void*)(l_Substring_Raw_foldr___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_658_, 0, v___y_657_);
lean_closure_set(v___f_658_, 1, v_f_653_);
v___x_659_ = l_String_Slice_revPositions(v___y_657_);
lean_dec_ref(v___y_657_);
v___x_660_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_658_, v___x_659_, v_init_654_, lean_box(0));
return v___x_660_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; uint8_t v___y_669_; uint8_t v___x_675_; uint8_t v___y_677_; uint8_t v___x_678_; 
v___x_667_ = l_String_instInhabitedSlice;
v___x_675_ = lean_string_is_valid_pos(v_str_661_, v_startPos_662_);
v___x_678_ = lean_string_is_valid_pos(v_str_661_, v_stopPos_663_);
if (v___x_678_ == 0)
{
v___y_677_ = v___x_678_;
goto v___jp_676_;
}
else
{
uint8_t v___x_679_; 
v___x_679_ = lean_nat_dec_le(v_startPos_662_, v_stopPos_663_);
v___y_677_ = v___x_679_;
goto v___jp_676_;
}
v___jp_668_:
{
if (v___y_669_ == 0)
{
lean_object* v___x_670_; lean_object* v___x_671_; 
lean_del_object(v___x_665_);
lean_dec(v_stopPos_663_);
lean_dec(v_startPos_662_);
lean_dec_ref(v_str_661_);
v___x_670_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_671_ = l_panic___redArg(v___x_667_, v___x_670_);
v___y_657_ = v___x_671_;
goto v___jp_656_;
}
else
{
lean_object* v___x_673_; 
if (v_isShared_666_ == 0)
{
v___x_673_ = v___x_665_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_str_661_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_startPos_662_);
lean_ctor_set(v_reuseFailAlloc_674_, 2, v_stopPos_663_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
v___y_657_ = v___x_673_;
goto v___jp_656_;
}
}
}
v___jp_676_:
{
if (v___x_675_ == 0)
{
v___y_669_ = v___x_675_;
goto v___jp_668_;
}
else
{
v___y_669_ = v___y_677_;
goto v___jp_668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_any___lam__0(lean_object* v___x_681_, lean_object* v_s_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(v_s_682_, v___x_681_, v___y_683_, lean_box(0), lean_box(0), v___y_686_, v___y_687_, v___y_688_);
return v___x_689_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_any(lean_object* v_s_690_, lean_object* v_p_691_){
_start:
{
lean_object* v___x_692_; lean_object* v_str_693_; lean_object* v_startPos_694_; lean_object* v_stopPos_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_716_; 
lean_inc_ref(v_p_691_);
v___x_692_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v_p_691_);
v_str_693_ = lean_ctor_get(v_s_690_, 0);
v_startPos_694_ = lean_ctor_get(v_s_690_, 1);
v_stopPos_695_ = lean_ctor_get(v_s_690_, 2);
v_isSharedCheck_716_ = !lean_is_exclusive(v_s_690_);
if (v_isSharedCheck_716_ == 0)
{
v___x_697_ = v_s_690_;
v_isShared_698_ = v_isSharedCheck_716_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_stopPos_695_);
lean_inc(v_startPos_694_);
lean_inc(v_str_693_);
lean_dec(v_s_690_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_716_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_699_; lean_object* v___f_700_; lean_object* v___x_701_; uint8_t v___y_703_; uint8_t v___x_711_; uint8_t v___y_713_; uint8_t v___x_714_; 
v___x_699_ = l_String_instInhabitedSlice;
v___f_700_ = lean_alloc_closure((void*)(l_Substring_Raw_any___lam__0), 8, 1);
lean_closure_set(v___f_700_, 0, v___x_692_);
v___x_701_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_701_, 0, lean_box(0));
lean_closure_set(v___x_701_, 1, v_p_691_);
v___x_711_ = lean_string_is_valid_pos(v_str_693_, v_startPos_694_);
v___x_714_ = lean_string_is_valid_pos(v_str_693_, v_stopPos_695_);
if (v___x_714_ == 0)
{
v___y_713_ = v___x_714_;
goto v___jp_712_;
}
else
{
uint8_t v___x_715_; 
v___x_715_ = lean_nat_dec_le(v_startPos_694_, v_stopPos_695_);
v___y_713_ = v___x_715_;
goto v___jp_712_;
}
v___jp_702_:
{
if (v___y_703_ == 0)
{
lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
lean_del_object(v___x_697_);
lean_dec(v_stopPos_695_);
lean_dec(v_startPos_694_);
lean_dec_ref(v_str_693_);
v___x_704_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_705_ = l_panic___redArg(v___x_699_, v___x_704_);
v___x_706_ = l_String_Slice_contains___redArg(v___f_700_, v___x_705_, v___x_701_);
return v___x_706_;
}
else
{
lean_object* v___x_708_; 
if (v_isShared_698_ == 0)
{
v___x_708_ = v___x_697_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_str_693_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_startPos_694_);
lean_ctor_set(v_reuseFailAlloc_710_, 2, v_stopPos_695_);
v___x_708_ = v_reuseFailAlloc_710_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
uint8_t v___x_709_; 
v___x_709_ = l_String_Slice_contains___redArg(v___f_700_, v___x_708_, v___x_701_);
return v___x_709_;
}
}
}
v___jp_712_:
{
if (v___x_711_ == 0)
{
v___y_703_ = v___x_711_;
goto v___jp_702_;
}
else
{
v___y_703_ = v___y_713_;
goto v___jp_702_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_any___boxed(lean_object* v_s_717_, lean_object* v_p_718_){
_start:
{
uint8_t v_res_719_; lean_object* v_r_720_; 
v_res_719_ = l_Substring_Raw_any(v_s_717_, v_p_718_);
v_r_720_ = lean_box(v_res_719_);
return v_r_720_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_all(lean_object* v_s_721_, lean_object* v_p_722_){
_start:
{
lean_object* v___y_724_; lean_object* v_startInclusive_725_; lean_object* v_endExclusive_726_; lean_object* v_str_732_; lean_object* v_startPos_733_; lean_object* v_stopPos_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_753_; 
v_str_732_ = lean_ctor_get(v_s_721_, 0);
v_startPos_733_ = lean_ctor_get(v_s_721_, 1);
v_stopPos_734_ = lean_ctor_get(v_s_721_, 2);
v_isSharedCheck_753_ = !lean_is_exclusive(v_s_721_);
if (v_isSharedCheck_753_ == 0)
{
v___x_736_ = v_s_721_;
v_isShared_737_ = v_isSharedCheck_753_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_stopPos_734_);
lean_inc(v_startPos_733_);
lean_inc(v_str_732_);
lean_dec(v_s_721_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_753_;
goto v_resetjp_735_;
}
v___jp_723_:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; uint8_t v_decide_731_; 
v___x_727_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v_p_722_);
v___x_728_ = lean_unsigned_to_nat(0u);
v___x_729_ = l_String_Slice_Pos_skipWhile___redArg(v___y_724_, v___x_728_, v___x_727_);
lean_dec_ref(v___y_724_);
v___x_730_ = lean_nat_sub(v_endExclusive_726_, v_startInclusive_725_);
lean_dec(v_startInclusive_725_);
lean_dec(v_endExclusive_726_);
v_decide_731_ = lean_nat_dec_eq(v___x_729_, v___x_730_);
lean_dec(v___x_730_);
lean_dec(v___x_729_);
return v_decide_731_;
}
v_resetjp_735_:
{
lean_object* v___x_738_; uint8_t v___y_740_; uint8_t v___x_748_; uint8_t v___y_750_; uint8_t v___x_751_; 
v___x_738_ = l_String_instInhabitedSlice;
v___x_748_ = lean_string_is_valid_pos(v_str_732_, v_startPos_733_);
v___x_751_ = lean_string_is_valid_pos(v_str_732_, v_stopPos_734_);
if (v___x_751_ == 0)
{
v___y_750_ = v___x_751_;
goto v___jp_749_;
}
else
{
uint8_t v___x_752_; 
v___x_752_ = lean_nat_dec_le(v_startPos_733_, v_stopPos_734_);
v___y_750_ = v___x_752_;
goto v___jp_749_;
}
v___jp_739_:
{
if (v___y_740_ == 0)
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v_startInclusive_743_; lean_object* v_endExclusive_744_; 
lean_del_object(v___x_736_);
lean_dec(v_stopPos_734_);
lean_dec(v_startPos_733_);
lean_dec_ref(v_str_732_);
v___x_741_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_742_ = l_panic___redArg(v___x_738_, v___x_741_);
v_startInclusive_743_ = lean_ctor_get(v___x_742_, 1);
lean_inc(v_startInclusive_743_);
v_endExclusive_744_ = lean_ctor_get(v___x_742_, 2);
lean_inc(v_endExclusive_744_);
v___y_724_ = v___x_742_;
v_startInclusive_725_ = v_startInclusive_743_;
v_endExclusive_726_ = v_endExclusive_744_;
goto v___jp_723_;
}
else
{
lean_object* v___x_746_; 
lean_inc(v_stopPos_734_);
lean_inc(v_startPos_733_);
if (v_isShared_737_ == 0)
{
v___x_746_ = v___x_736_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_str_732_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_startPos_733_);
lean_ctor_set(v_reuseFailAlloc_747_, 2, v_stopPos_734_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
v___y_724_ = v___x_746_;
v_startInclusive_725_ = v_startPos_733_;
v_endExclusive_726_ = v_stopPos_734_;
goto v___jp_723_;
}
}
}
v___jp_749_:
{
if (v___x_748_ == 0)
{
v___y_740_ = v___x_748_;
goto v___jp_739_;
}
else
{
v___y_740_ = v___y_750_;
goto v___jp_739_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_all___boxed(lean_object* v_s_754_, lean_object* v_p_755_){
_start:
{
uint8_t v_res_756_; lean_object* v_r_757_; 
v_res_756_ = l_Substring_Raw_all(v_s_754_, v_p_755_);
v_r_757_ = lean_box(v_res_756_);
return v_r_757_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(lean_object* v_msg_758_){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = l_String_instInhabitedSlice;
v___x_760_ = lean_panic_fn_borrowed(v___x_759_, v_msg_758_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0(lean_object* v_p_761_, lean_object* v_s_762_, lean_object* v_pos_763_){
_start:
{
lean_object* v_str_764_; lean_object* v_startInclusive_765_; lean_object* v_endExclusive_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; uint8_t v_decide_770_; 
v_str_764_ = lean_ctor_get(v_s_762_, 0);
v_startInclusive_765_ = lean_ctor_get(v_s_762_, 1);
v_endExclusive_766_ = lean_ctor_get(v_s_762_, 2);
v___x_767_ = lean_nat_add(v_startInclusive_765_, v_pos_763_);
v___x_768_ = lean_unsigned_to_nat(0u);
v___x_769_ = lean_nat_sub(v_endExclusive_766_, v___x_767_);
v_decide_770_ = lean_nat_dec_eq(v___x_768_, v___x_769_);
lean_dec(v___x_769_);
if (v_decide_770_ == 0)
{
uint32_t v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_771_ = lean_string_utf8_get_fast(v_str_764_, v___x_767_);
v___x_772_ = lean_box_uint32(v___x_771_);
lean_inc_ref(v_p_761_);
v___x_773_ = lean_apply_1(v_p_761_, v___x_772_);
v___x_774_ = lean_unbox(v___x_773_);
if (v___x_774_ == 0)
{
lean_dec(v___x_767_);
lean_dec_ref(v_p_761_);
return v_pos_763_;
}
else
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_775_ = lean_string_utf8_next_fast(v_str_764_, v___x_767_);
v___x_776_ = lean_nat_sub(v___x_775_, v___x_767_);
lean_dec(v___x_767_);
v___x_777_ = lean_nat_add(v_pos_763_, v___x_776_);
lean_dec(v___x_776_);
v___x_778_ = lean_unsigned_to_nat(1u);
v___x_779_ = lean_nat_add(v_pos_763_, v___x_778_);
v___x_780_ = lean_nat_dec_le(v___x_779_, v___x_777_);
lean_dec(v___x_779_);
if (v___x_780_ == 0)
{
lean_dec(v___x_777_);
lean_dec_ref(v_p_761_);
return v_pos_763_;
}
else
{
lean_dec(v_pos_763_);
v_pos_763_ = v___x_777_;
goto _start;
}
}
}
else
{
lean_dec(v___x_767_);
lean_dec_ref(v_p_761_);
return v_pos_763_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0___boxed(lean_object* v_p_782_, lean_object* v_s_783_, lean_object* v_pos_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0(v_p_782_, v_s_783_, v_pos_784_);
lean_dec_ref(v_s_783_);
return v_res_785_;
}
}
LEAN_EXPORT uint8_t lean_substring_all(lean_object* v_s_786_, lean_object* v_p_787_){
_start:
{
lean_object* v___y_789_; lean_object* v_startInclusive_790_; lean_object* v_endExclusive_791_; lean_object* v_str_796_; lean_object* v_startPos_797_; lean_object* v_stopPos_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_816_; 
v_str_796_ = lean_ctor_get(v_s_786_, 0);
v_startPos_797_ = lean_ctor_get(v_s_786_, 1);
v_stopPos_798_ = lean_ctor_get(v_s_786_, 2);
v_isSharedCheck_816_ = !lean_is_exclusive(v_s_786_);
if (v_isSharedCheck_816_ == 0)
{
v___x_800_ = v_s_786_;
v_isShared_801_ = v_isSharedCheck_816_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_stopPos_798_);
lean_inc(v_startPos_797_);
lean_inc(v_str_796_);
lean_dec(v_s_786_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_816_;
goto v_resetjp_799_;
}
v___jp_788_:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; uint8_t v_decide_795_; 
v___x_792_ = lean_unsigned_to_nat(0u);
v___x_793_ = l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0(v_p_787_, v___y_789_, v___x_792_);
lean_dec_ref(v___y_789_);
v___x_794_ = lean_nat_sub(v_endExclusive_791_, v_startInclusive_790_);
lean_dec(v_startInclusive_790_);
lean_dec(v_endExclusive_791_);
v_decide_795_ = lean_nat_dec_eq(v___x_793_, v___x_794_);
lean_dec(v___x_794_);
lean_dec(v___x_793_);
return v_decide_795_;
}
v_resetjp_799_:
{
uint8_t v___y_803_; uint8_t v___x_811_; uint8_t v___y_813_; uint8_t v___x_814_; 
v___x_811_ = lean_string_is_valid_pos(v_str_796_, v_startPos_797_);
v___x_814_ = lean_string_is_valid_pos(v_str_796_, v_stopPos_798_);
if (v___x_814_ == 0)
{
v___y_813_ = v___x_814_;
goto v___jp_812_;
}
else
{
uint8_t v___x_815_; 
v___x_815_ = lean_nat_dec_le(v_startPos_797_, v_stopPos_798_);
v___y_813_ = v___x_815_;
goto v___jp_812_;
}
v___jp_802_:
{
if (v___y_803_ == 0)
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v_startInclusive_806_; lean_object* v_endExclusive_807_; 
lean_del_object(v___x_800_);
lean_dec(v_stopPos_798_);
lean_dec(v_startPos_797_);
lean_dec_ref(v_str_796_);
v___x_804_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_805_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_804_);
v_startInclusive_806_ = lean_ctor_get(v___x_805_, 1);
lean_inc(v_startInclusive_806_);
v_endExclusive_807_ = lean_ctor_get(v___x_805_, 2);
lean_inc(v_endExclusive_807_);
v___y_789_ = v___x_805_;
v_startInclusive_790_ = v_startInclusive_806_;
v_endExclusive_791_ = v_endExclusive_807_;
goto v___jp_788_;
}
else
{
lean_object* v___x_809_; 
lean_inc(v_stopPos_798_);
lean_inc(v_startPos_797_);
if (v_isShared_801_ == 0)
{
v___x_809_ = v___x_800_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_str_796_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_startPos_797_);
lean_ctor_set(v_reuseFailAlloc_810_, 2, v_stopPos_798_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
v___y_789_ = v___x_809_;
v_startInclusive_790_ = v_startPos_797_;
v_endExclusive_791_ = v_stopPos_798_;
goto v___jp_788_;
}
}
}
v___jp_812_:
{
if (v___x_811_ == 0)
{
v___y_803_ = v___x_811_;
goto v___jp_802_;
}
else
{
v___y_803_ = v___y_813_;
goto v___jp_802_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_allImpl___boxed(lean_object* v_s_817_, lean_object* v_p_818_){
_start:
{
uint8_t v_res_819_; lean_object* v_r_820_; 
v_res_819_ = lean_substring_all(v_s_817_, v_p_818_);
v_r_820_ = lean_box(v_res_819_);
return v_r_820_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_contains___lam__0(uint32_t v_c_821_, uint32_t v_a_822_){
_start:
{
uint8_t v___x_823_; 
v___x_823_ = lean_uint32_dec_eq(v_a_822_, v_c_821_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_contains___lam__0___boxed(lean_object* v_c_824_, lean_object* v_a_825_){
_start:
{
uint32_t v_c_boxed_826_; uint32_t v_a_boxed_827_; uint8_t v_res_828_; lean_object* v_r_829_; 
v_c_boxed_826_ = lean_unbox_uint32(v_c_824_);
lean_dec(v_c_824_);
v_a_boxed_827_ = lean_unbox_uint32(v_a_825_);
lean_dec(v_a_825_);
v_res_828_ = l_Substring_Raw_contains___lam__0(v_c_boxed_826_, v_a_boxed_827_);
v_r_829_ = lean_box(v_res_828_);
return v_r_829_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_contains(lean_object* v_s_830_, uint32_t v_c_831_){
_start:
{
lean_object* v___x_832_; lean_object* v___f_833_; lean_object* v___x_834_; lean_object* v_str_835_; lean_object* v_startPos_836_; lean_object* v_stopPos_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_858_; 
v___x_832_ = lean_box_uint32(v_c_831_);
v___f_833_ = lean_alloc_closure((void*)(l_Substring_Raw_contains___lam__0___boxed), 2, 1);
lean_closure_set(v___f_833_, 0, v___x_832_);
lean_inc_ref(v___f_833_);
v___x_834_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___f_833_);
v_str_835_ = lean_ctor_get(v_s_830_, 0);
v_startPos_836_ = lean_ctor_get(v_s_830_, 1);
v_stopPos_837_ = lean_ctor_get(v_s_830_, 2);
v_isSharedCheck_858_ = !lean_is_exclusive(v_s_830_);
if (v_isSharedCheck_858_ == 0)
{
v___x_839_ = v_s_830_;
v_isShared_840_ = v_isSharedCheck_858_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_stopPos_837_);
lean_inc(v_startPos_836_);
lean_inc(v_str_835_);
lean_dec(v_s_830_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_858_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_841_; lean_object* v___f_842_; lean_object* v___x_843_; uint8_t v___y_845_; uint8_t v___x_853_; uint8_t v___y_855_; uint8_t v___x_856_; 
v___x_841_ = l_String_instInhabitedSlice;
v___f_842_ = lean_alloc_closure((void*)(l_Substring_Raw_any___lam__0), 8, 1);
lean_closure_set(v___f_842_, 0, v___x_834_);
v___x_843_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_843_, 0, lean_box(0));
lean_closure_set(v___x_843_, 1, v___f_833_);
v___x_853_ = lean_string_is_valid_pos(v_str_835_, v_startPos_836_);
v___x_856_ = lean_string_is_valid_pos(v_str_835_, v_stopPos_837_);
if (v___x_856_ == 0)
{
v___y_855_ = v___x_856_;
goto v___jp_854_;
}
else
{
uint8_t v___x_857_; 
v___x_857_ = lean_nat_dec_le(v_startPos_836_, v_stopPos_837_);
v___y_855_ = v___x_857_;
goto v___jp_854_;
}
v___jp_844_:
{
if (v___y_845_ == 0)
{
lean_object* v___x_846_; lean_object* v___x_847_; uint8_t v___x_848_; 
lean_del_object(v___x_839_);
lean_dec(v_stopPos_837_);
lean_dec(v_startPos_836_);
lean_dec_ref(v_str_835_);
v___x_846_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_847_ = l_panic___redArg(v___x_841_, v___x_846_);
v___x_848_ = l_String_Slice_contains___redArg(v___f_842_, v___x_847_, v___x_843_);
return v___x_848_;
}
else
{
lean_object* v___x_850_; 
if (v_isShared_840_ == 0)
{
v___x_850_ = v___x_839_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_str_835_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v_startPos_836_);
lean_ctor_set(v_reuseFailAlloc_852_, 2, v_stopPos_837_);
v___x_850_ = v_reuseFailAlloc_852_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
uint8_t v___x_851_; 
v___x_851_ = l_String_Slice_contains___redArg(v___f_842_, v___x_850_, v___x_843_);
return v___x_851_;
}
}
}
v___jp_854_:
{
if (v___x_853_ == 0)
{
v___y_845_ = v___x_853_;
goto v___jp_844_;
}
else
{
v___y_845_ = v___y_855_;
goto v___jp_844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_contains___boxed(lean_object* v_s_859_, lean_object* v_c_860_){
_start:
{
uint32_t v_c_boxed_861_; uint8_t v_res_862_; lean_object* v_r_863_; 
v_c_boxed_861_ = lean_unbox_uint32(v_c_860_);
lean_dec(v_c_860_);
v_res_862_ = l_Substring_Raw_contains(v_s_859_, v_c_boxed_861_);
v_r_863_ = lean_box(v_res_862_);
return v_r_863_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux(lean_object* v_s_864_, lean_object* v_stopPos_865_, lean_object* v_p_866_, lean_object* v_i_867_){
_start:
{
uint8_t v___y_869_; lean_object* v___x_872_; lean_object* v___x_873_; uint8_t v___x_874_; 
v___x_872_ = lean_unsigned_to_nat(1u);
v___x_873_ = lean_nat_add(v_i_867_, v___x_872_);
v___x_874_ = lean_nat_dec_le(v___x_873_, v_stopPos_865_);
lean_dec(v___x_873_);
if (v___x_874_ == 0)
{
lean_dec_ref(v_p_866_);
return v_i_867_;
}
else
{
if (v___x_874_ == 0)
{
v___y_869_ = v___x_874_;
goto v___jp_868_;
}
else
{
uint32_t v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; uint8_t v___x_878_; 
v___x_875_ = lean_string_utf8_get(v_s_864_, v_i_867_);
v___x_876_ = lean_box_uint32(v___x_875_);
lean_inc_ref(v_p_866_);
v___x_877_ = lean_apply_1(v_p_866_, v___x_876_);
v___x_878_ = lean_unbox(v___x_877_);
v___y_869_ = v___x_878_;
goto v___jp_868_;
}
}
v___jp_868_:
{
if (v___y_869_ == 0)
{
lean_dec_ref(v_p_866_);
return v_i_867_;
}
else
{
lean_object* v___x_870_; 
v___x_870_ = lean_string_utf8_next(v_s_864_, v_i_867_);
lean_dec(v_i_867_);
v_i_867_ = v___x_870_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___boxed(lean_object* v_s_879_, lean_object* v_stopPos_880_, lean_object* v_p_881_, lean_object* v_i_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Substring_Raw_takeWhileAux(v_s_879_, v_stopPos_880_, v_p_881_, v_i_882_);
lean_dec(v_stopPos_880_);
lean_dec_ref(v_s_879_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhile(lean_object* v_x_884_, lean_object* v_x_885_){
_start:
{
lean_object* v_str_886_; lean_object* v_startPos_887_; lean_object* v_stopPos_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_896_; 
v_str_886_ = lean_ctor_get(v_x_884_, 0);
v_startPos_887_ = lean_ctor_get(v_x_884_, 1);
v_stopPos_888_ = lean_ctor_get(v_x_884_, 2);
v_isSharedCheck_896_ = !lean_is_exclusive(v_x_884_);
if (v_isSharedCheck_896_ == 0)
{
v___x_890_ = v_x_884_;
v_isShared_891_ = v_isSharedCheck_896_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_stopPos_888_);
lean_inc(v_startPos_887_);
lean_inc(v_str_886_);
lean_dec(v_x_884_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_896_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v_e_892_; lean_object* v___x_894_; 
lean_inc(v_startPos_887_);
v_e_892_ = l_Substring_Raw_takeWhileAux(v_str_886_, v_stopPos_888_, v_x_885_, v_startPos_887_);
lean_dec(v_stopPos_888_);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 2, v_e_892_);
v___x_894_ = v___x_890_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_str_886_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_startPos_887_);
lean_ctor_set(v_reuseFailAlloc_895_, 2, v_e_892_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(lean_object* v_a_897_, lean_object* v_s_898_, lean_object* v_stopPos_899_, lean_object* v_i_900_){
_start:
{
uint8_t v___y_902_; lean_object* v___x_905_; lean_object* v___x_906_; uint8_t v___x_907_; 
v___x_905_ = lean_unsigned_to_nat(1u);
v___x_906_ = lean_nat_add(v_i_900_, v___x_905_);
v___x_907_ = lean_nat_dec_le(v___x_906_, v_stopPos_899_);
lean_dec(v___x_906_);
if (v___x_907_ == 0)
{
lean_dec_ref(v_a_897_);
return v_i_900_;
}
else
{
if (v___x_907_ == 0)
{
v___y_902_ = v___x_907_;
goto v___jp_901_;
}
else
{
uint32_t v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; uint8_t v___x_911_; 
v___x_908_ = lean_string_utf8_get(v_s_898_, v_i_900_);
v___x_909_ = lean_box_uint32(v___x_908_);
lean_inc_ref(v_a_897_);
v___x_910_ = lean_apply_1(v_a_897_, v___x_909_);
v___x_911_ = lean_unbox(v___x_910_);
v___y_902_ = v___x_911_;
goto v___jp_901_;
}
}
v___jp_901_:
{
if (v___y_902_ == 0)
{
lean_dec_ref(v_a_897_);
return v_i_900_;
}
else
{
lean_object* v___x_903_; 
v___x_903_ = lean_string_utf8_next(v_s_898_, v_i_900_);
lean_dec(v_i_900_);
v_i_900_ = v___x_903_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0___boxed(lean_object* v_a_912_, lean_object* v_s_913_, lean_object* v_stopPos_914_, lean_object* v_i_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(v_a_912_, v_s_913_, v_stopPos_914_, v_i_915_);
lean_dec(v_stopPos_914_);
lean_dec_ref(v_s_913_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* lean_substring_takewhile(lean_object* v_a_917_, lean_object* v_a_918_){
_start:
{
lean_object* v_str_919_; lean_object* v_startPos_920_; lean_object* v_stopPos_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_929_; 
v_str_919_ = lean_ctor_get(v_a_917_, 0);
v_startPos_920_ = lean_ctor_get(v_a_917_, 1);
v_stopPos_921_ = lean_ctor_get(v_a_917_, 2);
v_isSharedCheck_929_ = !lean_is_exclusive(v_a_917_);
if (v_isSharedCheck_929_ == 0)
{
v___x_923_ = v_a_917_;
v_isShared_924_ = v_isSharedCheck_929_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_stopPos_921_);
lean_inc(v_startPos_920_);
lean_inc(v_str_919_);
lean_dec(v_a_917_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_929_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v_e_925_; lean_object* v___x_927_; 
lean_inc(v_startPos_920_);
v_e_925_ = l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(v_a_918_, v_str_919_, v_stopPos_921_, v_startPos_920_);
lean_dec(v_stopPos_921_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 2, v_e_925_);
v___x_927_ = v___x_923_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_str_919_);
lean_ctor_set(v_reuseFailAlloc_928_, 1, v_startPos_920_);
lean_ctor_set(v_reuseFailAlloc_928_, 2, v_e_925_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropWhile(lean_object* v_x_930_, lean_object* v_x_931_){
_start:
{
lean_object* v_str_932_; lean_object* v_startPos_933_; lean_object* v_stopPos_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_942_; 
v_str_932_ = lean_ctor_get(v_x_930_, 0);
v_startPos_933_ = lean_ctor_get(v_x_930_, 1);
v_stopPos_934_ = lean_ctor_get(v_x_930_, 2);
v_isSharedCheck_942_ = !lean_is_exclusive(v_x_930_);
if (v_isSharedCheck_942_ == 0)
{
v___x_936_ = v_x_930_;
v_isShared_937_ = v_isSharedCheck_942_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_stopPos_934_);
lean_inc(v_startPos_933_);
lean_inc(v_str_932_);
lean_dec(v_x_930_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_942_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v_b_938_; lean_object* v___x_940_; 
v_b_938_ = l_Substring_Raw_takeWhileAux(v_str_932_, v_stopPos_934_, v_x_931_, v_startPos_933_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 1, v_b_938_);
v___x_940_ = v___x_936_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_str_932_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_b_938_);
lean_ctor_set(v_reuseFailAlloc_941_, 2, v_stopPos_934_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux(lean_object* v_s_943_, lean_object* v_begPos_944_, lean_object* v_p_945_, lean_object* v_i_946_){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; uint8_t v___x_949_; 
v___x_947_ = lean_unsigned_to_nat(1u);
v___x_948_ = lean_nat_add(v_begPos_944_, v___x_947_);
v___x_949_ = lean_nat_dec_le(v___x_948_, v_i_946_);
lean_dec(v___x_948_);
if (v___x_949_ == 0)
{
lean_dec_ref(v_p_945_);
return v_i_946_;
}
else
{
lean_object* v_i_x27_950_; uint8_t v___y_952_; uint8_t v___y_955_; uint32_t v_c_956_; lean_object* v___x_957_; lean_object* v___x_958_; uint8_t v___x_959_; 
v_i_x27_950_ = lean_string_utf8_prev(v_s_943_, v_i_946_);
v_c_956_ = lean_string_utf8_get(v_s_943_, v_i_x27_950_);
v___x_957_ = lean_box_uint32(v_c_956_);
lean_inc_ref(v_p_945_);
v___x_958_ = lean_apply_1(v_p_945_, v___x_957_);
v___x_959_ = lean_unbox(v___x_958_);
if (v___x_959_ == 0)
{
v___y_955_ = v___x_949_;
goto v___jp_954_;
}
else
{
uint8_t v___x_960_; 
v___x_960_ = 0;
v___y_955_ = v___x_960_;
goto v___jp_954_;
}
v___jp_951_:
{
if (v___y_952_ == 0)
{
lean_dec(v_i_946_);
v_i_946_ = v_i_x27_950_;
goto _start;
}
else
{
lean_dec(v_i_x27_950_);
lean_dec_ref(v_p_945_);
return v_i_946_;
}
}
v___jp_954_:
{
if (v___x_949_ == 0)
{
v___y_952_ = v___x_949_;
goto v___jp_951_;
}
else
{
v___y_952_ = v___y_955_;
goto v___jp_951_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux___boxed(lean_object* v_s_961_, lean_object* v_begPos_962_, lean_object* v_p_963_, lean_object* v_i_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Substring_Raw_takeRightWhileAux(v_s_961_, v_begPos_962_, v_p_963_, v_i_964_);
lean_dec(v_begPos_962_);
lean_dec_ref(v_s_961_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhile(lean_object* v_x_966_, lean_object* v_x_967_){
_start:
{
lean_object* v_str_968_; lean_object* v_startPos_969_; lean_object* v_stopPos_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_978_; 
v_str_968_ = lean_ctor_get(v_x_966_, 0);
v_startPos_969_ = lean_ctor_get(v_x_966_, 1);
v_stopPos_970_ = lean_ctor_get(v_x_966_, 2);
v_isSharedCheck_978_ = !lean_is_exclusive(v_x_966_);
if (v_isSharedCheck_978_ == 0)
{
v___x_972_ = v_x_966_;
v_isShared_973_ = v_isSharedCheck_978_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_stopPos_970_);
lean_inc(v_startPos_969_);
lean_inc(v_str_968_);
lean_dec(v_x_966_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_978_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v_b_974_; lean_object* v___x_976_; 
lean_inc(v_stopPos_970_);
v_b_974_ = l_Substring_Raw_takeRightWhileAux(v_str_968_, v_startPos_969_, v_x_967_, v_stopPos_970_);
lean_dec(v_startPos_969_);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 1, v_b_974_);
v___x_976_ = v___x_972_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_str_968_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_b_974_);
lean_ctor_set(v_reuseFailAlloc_977_, 2, v_stopPos_970_);
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
LEAN_EXPORT lean_object* l_Substring_Raw_dropRightWhile(lean_object* v_x_979_, lean_object* v_x_980_){
_start:
{
lean_object* v_str_981_; lean_object* v_startPos_982_; lean_object* v_stopPos_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_991_; 
v_str_981_ = lean_ctor_get(v_x_979_, 0);
v_startPos_982_ = lean_ctor_get(v_x_979_, 1);
v_stopPos_983_ = lean_ctor_get(v_x_979_, 2);
v_isSharedCheck_991_ = !lean_is_exclusive(v_x_979_);
if (v_isSharedCheck_991_ == 0)
{
v___x_985_ = v_x_979_;
v_isShared_986_ = v_isSharedCheck_991_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_stopPos_983_);
lean_inc(v_startPos_982_);
lean_inc(v_str_981_);
lean_dec(v_x_979_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_991_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v_e_987_; lean_object* v___x_989_; 
v_e_987_ = l_Substring_Raw_takeRightWhileAux(v_str_981_, v_startPos_982_, v_x_980_, v_stopPos_983_);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 2, v_e_987_);
v___x_989_ = v___x_985_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_str_981_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_startPos_982_);
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
LEAN_EXPORT lean_object* l_Substring_Raw_trimLeft(lean_object* v_s_993_){
_start:
{
lean_object* v_str_994_; lean_object* v_startPos_995_; lean_object* v_stopPos_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1005_; 
v_str_994_ = lean_ctor_get(v_s_993_, 0);
v_startPos_995_ = lean_ctor_get(v_s_993_, 1);
v_stopPos_996_ = lean_ctor_get(v_s_993_, 2);
v_isSharedCheck_1005_ = !lean_is_exclusive(v_s_993_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_998_ = v_s_993_;
v_isShared_999_ = v_isSharedCheck_1005_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_stopPos_996_);
lean_inc(v_startPos_995_);
lean_inc(v_str_994_);
lean_dec(v_s_993_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1005_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1000_; lean_object* v_b_1001_; lean_object* v___x_1003_; 
v___x_1000_ = ((lean_object*)(l_Substring_Raw_trimLeft___closed__0));
v_b_1001_ = l_Substring_Raw_takeWhileAux(v_str_994_, v_stopPos_996_, v___x_1000_, v_startPos_995_);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 1, v_b_1001_);
v___x_1003_ = v___x_998_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_str_994_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v_b_1001_);
lean_ctor_set(v_reuseFailAlloc_1004_, 2, v_stopPos_996_);
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
LEAN_EXPORT lean_object* l_Substring_Raw_trimRight(lean_object* v_s_1006_){
_start:
{
lean_object* v_str_1007_; lean_object* v_startPos_1008_; lean_object* v_stopPos_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1018_; 
v_str_1007_ = lean_ctor_get(v_s_1006_, 0);
v_startPos_1008_ = lean_ctor_get(v_s_1006_, 1);
v_stopPos_1009_ = lean_ctor_get(v_s_1006_, 2);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_s_1006_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1011_ = v_s_1006_;
v_isShared_1012_ = v_isSharedCheck_1018_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_stopPos_1009_);
lean_inc(v_startPos_1008_);
lean_inc(v_str_1007_);
lean_dec(v_s_1006_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1018_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1013_; lean_object* v_e_1014_; lean_object* v___x_1016_; 
v___x_1013_ = ((lean_object*)(l_Substring_Raw_trimLeft___closed__0));
v_e_1014_ = l_Substring_Raw_takeRightWhileAux(v_str_1007_, v_startPos_1008_, v___x_1013_, v_stopPos_1009_);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 2, v_e_1014_);
v___x_1016_ = v___x_1011_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_str_1007_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v_startPos_1008_);
lean_ctor_set(v_reuseFailAlloc_1017_, 2, v_e_1014_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_trim(lean_object* v_x_1019_){
_start:
{
lean_object* v_str_1020_; lean_object* v_startPos_1021_; lean_object* v_stopPos_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1032_; 
v_str_1020_ = lean_ctor_get(v_x_1019_, 0);
v_startPos_1021_ = lean_ctor_get(v_x_1019_, 1);
v_stopPos_1022_ = lean_ctor_get(v_x_1019_, 2);
v_isSharedCheck_1032_ = !lean_is_exclusive(v_x_1019_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1024_ = v_x_1019_;
v_isShared_1025_ = v_isSharedCheck_1032_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_stopPos_1022_);
lean_inc(v_startPos_1021_);
lean_inc(v_str_1020_);
lean_dec(v_x_1019_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1032_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v_b_1027_; lean_object* v_e_1028_; lean_object* v___x_1030_; 
v___x_1026_ = ((lean_object*)(l_Substring_Raw_trimLeft___closed__0));
v_b_1027_ = l_Substring_Raw_takeWhileAux(v_str_1020_, v_stopPos_1022_, v___x_1026_, v_startPos_1021_);
v_e_1028_ = l_Substring_Raw_takeRightWhileAux(v_str_1020_, v_b_1027_, v___x_1026_, v_stopPos_1022_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 2, v_e_1028_);
lean_ctor_set(v___x_1024_, 1, v_b_1027_);
v___x_1030_ = v___x_1024_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_str_1020_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_b_1027_);
lean_ctor_set(v_reuseFailAlloc_1031_, 2, v_e_1028_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___lam__0(lean_object* v___y_1033_, uint8_t v___x_1034_, uint8_t v___x_1035_, lean_object* v_it_1036_, lean_object* v_acc_1037_, lean_object* v_hP_1038_, lean_object* v_recur_1039_){
_start:
{
lean_object* v_str_1040_; lean_object* v_startInclusive_1041_; lean_object* v_endExclusive_1042_; lean_object* v___x_1043_; uint8_t v_decide_1044_; 
v_str_1040_ = lean_ctor_get(v___y_1033_, 0);
v_startInclusive_1041_ = lean_ctor_get(v___y_1033_, 1);
v_endExclusive_1042_ = lean_ctor_get(v___y_1033_, 2);
v___x_1043_ = lean_nat_sub(v_endExclusive_1042_, v_startInclusive_1041_);
v_decide_1044_ = lean_nat_dec_eq(v_it_1036_, v___x_1043_);
lean_dec(v___x_1043_);
if (v_decide_1044_ == 0)
{
lean_object* v_snd_1045_; lean_object* v_snd_1046_; lean_object* v_fst_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1107_; 
v_snd_1045_ = lean_ctor_get(v_acc_1037_, 1);
lean_inc(v_snd_1045_);
v_snd_1046_ = lean_ctor_get(v_snd_1045_, 1);
lean_inc(v_snd_1046_);
v_fst_1047_ = lean_ctor_get(v_acc_1037_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v_acc_1037_);
if (v_isSharedCheck_1107_ == 0)
{
lean_object* v_unused_1108_; 
v_unused_1108_ = lean_ctor_get(v_acc_1037_, 1);
lean_dec(v_unused_1108_);
v___x_1049_ = v_acc_1037_;
v_isShared_1050_ = v_isSharedCheck_1107_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_fst_1047_);
lean_dec(v_acc_1037_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1107_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v_fst_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1105_; 
v_fst_1051_ = lean_ctor_get(v_snd_1045_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v_snd_1045_);
if (v_isSharedCheck_1105_ == 0)
{
lean_object* v_unused_1106_; 
v_unused_1106_ = lean_ctor_get(v_snd_1045_, 1);
lean_dec(v_unused_1106_);
v___x_1053_ = v_snd_1045_;
v_isShared_1054_ = v_isSharedCheck_1105_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_fst_1051_);
lean_dec(v_snd_1045_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1105_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v_snd_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1103_; 
v_snd_1055_ = lean_ctor_get(v_snd_1046_, 1);
v_isSharedCheck_1103_ = !lean_is_exclusive(v_snd_1046_);
if (v_isSharedCheck_1103_ == 0)
{
lean_object* v_unused_1104_; 
v_unused_1104_ = lean_ctor_get(v_snd_1046_, 0);
lean_dec(v_unused_1104_);
v___x_1057_ = v_snd_1046_;
v_isShared_1058_ = v_isSharedCheck_1103_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_snd_1055_);
lean_dec(v_snd_1046_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1103_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1059_; uint32_t v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; uint8_t v___y_1064_; uint8_t v___y_1065_; uint8_t v___y_1083_; uint8_t v___y_1084_; uint8_t v___y_1089_; uint8_t v___y_1090_; uint8_t v___y_1095_; uint32_t v___x_1099_; uint8_t v___x_1100_; 
v___x_1059_ = lean_nat_add(v_startInclusive_1041_, v_it_1036_);
v___x_1060_ = lean_string_utf8_get_fast(v_str_1040_, v___x_1059_);
v___x_1061_ = lean_string_utf8_next_fast(v_str_1040_, v___x_1059_);
lean_dec(v___x_1059_);
v___x_1062_ = lean_nat_sub(v___x_1061_, v_startInclusive_1041_);
v___x_1099_ = 48;
v___x_1100_ = lean_uint32_dec_le(v___x_1099_, v___x_1060_);
if (v___x_1100_ == 0)
{
v___y_1095_ = v___x_1100_;
goto v___jp_1094_;
}
else
{
uint32_t v___x_1101_; uint8_t v___x_1102_; 
v___x_1101_ = 57;
v___x_1102_ = lean_uint32_dec_le(v___x_1060_, v___x_1101_);
v___y_1095_ = v___x_1102_;
goto v___jp_1094_;
}
v___jp_1063_:
{
uint32_t v___x_1066_; uint8_t v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1071_; 
v___x_1066_ = 95;
v___x_1067_ = lean_uint32_dec_eq(v___x_1060_, v___x_1066_);
v___x_1068_ = lean_box(v___y_1064_);
v___x_1069_ = lean_box(v___y_1065_);
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 1, v___x_1069_);
lean_ctor_set(v___x_1057_, 0, v___x_1068_);
v___x_1071_ = v___x_1057_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v___x_1069_);
v___x_1071_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1072_; lean_object* v___x_1074_; 
v___x_1072_ = lean_box(v___x_1067_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 1, v___x_1071_);
lean_ctor_set(v___x_1053_, 0, v___x_1072_);
v___x_1074_ = v___x_1053_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v___x_1071_);
v___x_1074_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1075_ = lean_box(v___x_1034_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 1, v___x_1074_);
lean_ctor_set(v___x_1049_, 0, v___x_1075_);
v___x_1077_ = v___x_1049_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1075_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v___x_1074_);
v___x_1077_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v___x_1078_; 
v___x_1078_ = lean_apply_4(v_recur_1039_, v___x_1062_, v___x_1077_, lean_box(0), lean_box(0));
return v___x_1078_;
}
}
}
}
v___jp_1082_:
{
uint8_t v___x_1085_; 
v___x_1085_ = lean_unbox(v_fst_1051_);
lean_dec(v_fst_1051_);
if (v___x_1085_ == 0)
{
v___y_1064_ = v___y_1083_;
v___y_1065_ = v___y_1084_;
goto v___jp_1063_;
}
else
{
uint32_t v___x_1086_; uint8_t v___x_1087_; 
v___x_1086_ = 95;
v___x_1087_ = lean_uint32_dec_eq(v___x_1060_, v___x_1086_);
if (v___x_1087_ == 0)
{
v___y_1064_ = v___y_1083_;
v___y_1065_ = v___y_1084_;
goto v___jp_1063_;
}
else
{
v___y_1064_ = v___y_1083_;
v___y_1065_ = v___x_1034_;
goto v___jp_1063_;
}
}
}
v___jp_1088_:
{
uint8_t v___x_1091_; 
v___x_1091_ = lean_unbox(v_fst_1047_);
lean_dec(v_fst_1047_);
if (v___x_1091_ == 0)
{
v___y_1083_ = v___y_1089_;
v___y_1084_ = v___y_1090_;
goto v___jp_1082_;
}
else
{
uint32_t v___x_1092_; uint8_t v___x_1093_; 
v___x_1092_ = 95;
v___x_1093_ = lean_uint32_dec_eq(v___x_1060_, v___x_1092_);
if (v___x_1093_ == 0)
{
v___y_1083_ = v___y_1089_;
v___y_1084_ = v___y_1090_;
goto v___jp_1082_;
}
else
{
lean_dec(v_fst_1051_);
v___y_1064_ = v___y_1089_;
v___y_1065_ = v___x_1034_;
goto v___jp_1063_;
}
}
}
v___jp_1094_:
{
uint8_t v___x_1096_; 
v___x_1096_ = lean_unbox(v_snd_1055_);
lean_dec(v_snd_1055_);
if (v___x_1096_ == 0)
{
lean_dec(v_fst_1051_);
lean_dec(v_fst_1047_);
v___y_1064_ = v___y_1095_;
v___y_1065_ = v___x_1034_;
goto v___jp_1063_;
}
else
{
if (v___y_1095_ == 0)
{
uint32_t v___x_1097_; uint8_t v___x_1098_; 
v___x_1097_ = 95;
v___x_1098_ = lean_uint32_dec_eq(v___x_1060_, v___x_1097_);
if (v___x_1098_ == 0)
{
lean_dec(v_fst_1051_);
lean_dec(v_fst_1047_);
v___y_1064_ = v___y_1095_;
v___y_1065_ = v___x_1034_;
goto v___jp_1063_;
}
else
{
v___y_1089_ = v___y_1095_;
v___y_1090_ = v___x_1098_;
goto v___jp_1088_;
}
}
else
{
v___y_1089_ = v___y_1095_;
v___y_1090_ = v___x_1035_;
goto v___jp_1088_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_recur_1039_);
return v_acc_1037_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___lam__0___boxed(lean_object* v___y_1109_, lean_object* v___x_1110_, lean_object* v___x_1111_, lean_object* v_it_1112_, lean_object* v_acc_1113_, lean_object* v_hP_1114_, lean_object* v_recur_1115_){
_start:
{
uint8_t v___x_807__boxed_1116_; uint8_t v___x_808__boxed_1117_; lean_object* v_res_1118_; 
v___x_807__boxed_1116_ = lean_unbox(v___x_1110_);
v___x_808__boxed_1117_ = lean_unbox(v___x_1111_);
v_res_1118_ = l_Substring_Raw_isNat___lam__0(v___y_1109_, v___x_807__boxed_1116_, v___x_808__boxed_1117_, v_it_1112_, v_acc_1113_, v_hP_1114_, v_recur_1115_);
lean_dec(v_it_1112_);
lean_dec_ref(v___y_1109_);
return v_res_1118_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_isNat(lean_object* v_s_1119_){
_start:
{
lean_object* v_str_1120_; lean_object* v_startPos_1121_; lean_object* v_stopPos_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1163_; 
v_str_1120_ = lean_ctor_get(v_s_1119_, 0);
v_startPos_1121_ = lean_ctor_get(v_s_1119_, 1);
v_stopPos_1122_ = lean_ctor_get(v_s_1119_, 2);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_s_1119_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1124_ = v_s_1119_;
v_isShared_1125_ = v_isSharedCheck_1163_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_stopPos_1122_);
lean_inc(v_startPos_1121_);
lean_inc(v_str_1120_);
lean_dec(v_s_1119_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1163_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1126_ = lean_nat_sub(v_stopPos_1122_, v_startPos_1121_);
v___x_1127_ = lean_unsigned_to_nat(0u);
v___x_1128_ = lean_nat_dec_eq(v___x_1126_, v___x_1127_);
lean_dec(v___x_1126_);
if (v___x_1128_ == 0)
{
uint8_t v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___y_1138_; lean_object* v___x_1149_; uint8_t v___y_1151_; uint8_t v___x_1157_; uint8_t v___y_1159_; uint8_t v___x_1160_; 
v___x_1129_ = 1;
v___x_1130_ = lean_box(v___x_1128_);
v___x_1131_ = lean_box(v___x_1129_);
v___x_1132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1130_);
lean_ctor_set(v___x_1132_, 1, v___x_1131_);
v___x_1133_ = lean_box(v___x_1128_);
v___x_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
lean_ctor_set(v___x_1134_, 1, v___x_1132_);
v___x_1135_ = lean_box(v___x_1129_);
v___x_1136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
lean_ctor_set(v___x_1136_, 1, v___x_1134_);
v___x_1149_ = l_String_instInhabitedSlice;
v___x_1157_ = lean_string_is_valid_pos(v_str_1120_, v_startPos_1121_);
v___x_1160_ = lean_string_is_valid_pos(v_str_1120_, v_stopPos_1122_);
if (v___x_1160_ == 0)
{
v___y_1159_ = v___x_1160_;
goto v___jp_1158_;
}
else
{
uint8_t v___x_1161_; 
v___x_1161_ = lean_nat_dec_le(v_startPos_1121_, v_stopPos_1122_);
v___y_1159_ = v___x_1161_;
goto v___jp_1158_;
}
v___jp_1137_:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___f_1141_; lean_object* v___x_1142_; lean_object* v_snd_1143_; lean_object* v_snd_1144_; lean_object* v_snd_1145_; uint8_t v___x_1146_; 
v___x_1139_ = lean_box(v___x_1128_);
v___x_1140_ = lean_box(v___x_1129_);
v___f_1141_ = lean_alloc_closure((void*)(l_Substring_Raw_isNat___lam__0___boxed), 7, 3);
lean_closure_set(v___f_1141_, 0, v___y_1138_);
lean_closure_set(v___f_1141_, 1, v___x_1139_);
lean_closure_set(v___f_1141_, 2, v___x_1140_);
v___x_1142_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1141_, v___x_1127_, v___x_1136_, lean_box(0));
v_snd_1143_ = lean_ctor_get(v___x_1142_, 1);
lean_inc(v_snd_1143_);
lean_dec(v___x_1142_);
v_snd_1144_ = lean_ctor_get(v_snd_1143_, 1);
lean_inc(v_snd_1144_);
lean_dec(v_snd_1143_);
v_snd_1145_ = lean_ctor_get(v_snd_1144_, 1);
v___x_1146_ = lean_unbox(v_snd_1145_);
if (v___x_1146_ == 0)
{
lean_dec(v_snd_1144_);
return v___x_1128_;
}
else
{
lean_object* v_fst_1147_; uint8_t v___x_1148_; 
v_fst_1147_ = lean_ctor_get(v_snd_1144_, 0);
lean_inc(v_fst_1147_);
lean_dec(v_snd_1144_);
v___x_1148_ = lean_unbox(v_fst_1147_);
lean_dec(v_fst_1147_);
return v___x_1148_;
}
}
v___jp_1150_:
{
if (v___y_1151_ == 0)
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
lean_del_object(v___x_1124_);
lean_dec(v_stopPos_1122_);
lean_dec(v_startPos_1121_);
lean_dec_ref(v_str_1120_);
v___x_1152_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_1153_ = l_panic___redArg(v___x_1149_, v___x_1152_);
v___y_1138_ = v___x_1153_;
goto v___jp_1137_;
}
else
{
lean_object* v___x_1155_; 
if (v_isShared_1125_ == 0)
{
v___x_1155_ = v___x_1124_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_str_1120_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v_startPos_1121_);
lean_ctor_set(v_reuseFailAlloc_1156_, 2, v_stopPos_1122_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
v___y_1138_ = v___x_1155_;
goto v___jp_1137_;
}
}
}
v___jp_1158_:
{
if (v___x_1157_ == 0)
{
v___y_1151_ = v___x_1157_;
goto v___jp_1150_;
}
else
{
v___y_1151_ = v___y_1159_;
goto v___jp_1150_;
}
}
}
else
{
uint8_t v___x_1162_; 
lean_del_object(v___x_1124_);
lean_dec(v_stopPos_1122_);
lean_dec(v_startPos_1121_);
lean_dec_ref(v_str_1120_);
v___x_1162_ = 0;
return v___x_1162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___boxed(lean_object* v_s_1164_){
_start:
{
uint8_t v_res_1165_; lean_object* v_r_1166_; 
v_res_1165_ = l_Substring_Raw_isNat(v_s_1164_);
v_r_1166_ = lean_box(v_res_1165_);
return v_r_1166_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(lean_object* v___y_1167_, lean_object* v_a_1168_, lean_object* v_b_1169_){
_start:
{
lean_object* v_str_1170_; lean_object* v_startInclusive_1171_; lean_object* v_endExclusive_1172_; lean_object* v___x_1173_; uint8_t v_decide_1174_; 
v_str_1170_ = lean_ctor_get(v___y_1167_, 0);
v_startInclusive_1171_ = lean_ctor_get(v___y_1167_, 1);
v_endExclusive_1172_ = lean_ctor_get(v___y_1167_, 2);
v___x_1173_ = lean_nat_sub(v_endExclusive_1172_, v_startInclusive_1171_);
v_decide_1174_ = lean_nat_dec_eq(v_a_1168_, v___x_1173_);
lean_dec(v___x_1173_);
if (v_decide_1174_ == 0)
{
lean_object* v___x_1175_; uint32_t v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; uint32_t v___x_1179_; uint8_t v___x_1180_; 
v___x_1175_ = lean_nat_add(v_startInclusive_1171_, v_a_1168_);
lean_dec(v_a_1168_);
v___x_1176_ = lean_string_utf8_get_fast(v_str_1170_, v___x_1175_);
v___x_1177_ = lean_string_utf8_next_fast(v_str_1170_, v___x_1175_);
lean_dec(v___x_1175_);
v___x_1178_ = lean_nat_sub(v___x_1177_, v_startInclusive_1171_);
v___x_1179_ = 95;
v___x_1180_ = lean_uint32_dec_eq(v___x_1176_, v___x_1179_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1181_ = lean_unsigned_to_nat(10u);
v___x_1182_ = lean_nat_mul(v_b_1169_, v___x_1181_);
lean_dec(v_b_1169_);
v___x_1183_ = lean_uint32_to_nat(v___x_1176_);
v___x_1184_ = lean_unsigned_to_nat(48u);
v___x_1185_ = lean_nat_sub(v___x_1183_, v___x_1184_);
lean_dec(v___x_1183_);
v___x_1186_ = lean_nat_add(v___x_1182_, v___x_1185_);
lean_dec(v___x_1185_);
lean_dec(v___x_1182_);
v_a_1168_ = v___x_1178_;
v_b_1169_ = v___x_1186_;
goto _start;
}
else
{
v_a_1168_ = v___x_1178_;
goto _start;
}
}
else
{
lean_dec(v_a_1168_);
return v_b_1169_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg___boxed(lean_object* v___y_1189_, lean_object* v_a_1190_, lean_object* v_b_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(v___y_1189_, v_a_1190_, v_b_1191_);
lean_dec_ref(v___y_1189_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(lean_object* v___x_1193_, lean_object* v___y_1194_, lean_object* v_a_1195_, lean_object* v_b_1196_){
_start:
{
lean_object* v_str_1197_; lean_object* v_startInclusive_1198_; lean_object* v_endExclusive_1199_; lean_object* v___x_1200_; uint8_t v_decide_1201_; 
v_str_1197_ = lean_ctor_get(v___y_1194_, 0);
v_startInclusive_1198_ = lean_ctor_get(v___y_1194_, 1);
v_endExclusive_1199_ = lean_ctor_get(v___y_1194_, 2);
v___x_1200_ = lean_nat_sub(v_endExclusive_1199_, v_startInclusive_1198_);
v_decide_1201_ = lean_nat_dec_eq(v_a_1195_, v___x_1200_);
lean_dec(v___x_1200_);
if (v_decide_1201_ == 0)
{
lean_object* v_snd_1202_; lean_object* v_snd_1203_; lean_object* v_fst_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1267_; 
v_snd_1202_ = lean_ctor_get(v_b_1196_, 1);
lean_inc(v_snd_1202_);
v_snd_1203_ = lean_ctor_get(v_snd_1202_, 1);
lean_inc(v_snd_1203_);
v_fst_1204_ = lean_ctor_get(v_b_1196_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v_b_1196_);
if (v_isSharedCheck_1267_ == 0)
{
lean_object* v_unused_1268_; 
v_unused_1268_ = lean_ctor_get(v_b_1196_, 1);
lean_dec(v_unused_1268_);
v___x_1206_ = v_b_1196_;
v_isShared_1207_ = v_isSharedCheck_1267_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_fst_1204_);
lean_dec(v_b_1196_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1267_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v_fst_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1265_; 
v_fst_1208_ = lean_ctor_get(v_snd_1202_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v_snd_1202_);
if (v_isSharedCheck_1265_ == 0)
{
lean_object* v_unused_1266_; 
v_unused_1266_ = lean_ctor_get(v_snd_1202_, 1);
lean_dec(v_unused_1266_);
v___x_1210_ = v_snd_1202_;
v_isShared_1211_ = v_isSharedCheck_1265_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_fst_1208_);
lean_dec(v_snd_1202_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1265_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v_snd_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1263_; 
v_snd_1212_ = lean_ctor_get(v_snd_1203_, 1);
v_isSharedCheck_1263_ = !lean_is_exclusive(v_snd_1203_);
if (v_isSharedCheck_1263_ == 0)
{
lean_object* v_unused_1264_; 
v_unused_1264_ = lean_ctor_get(v_snd_1203_, 0);
lean_dec(v_unused_1264_);
v___x_1214_ = v_snd_1203_;
v_isShared_1215_ = v_isSharedCheck_1263_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_snd_1212_);
lean_dec(v_snd_1203_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1263_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1216_; uint8_t v___x_1217_; uint8_t v___x_1218_; lean_object* v___x_1219_; uint32_t v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; uint8_t v___y_1224_; uint8_t v___y_1225_; uint8_t v___y_1243_; uint8_t v___y_1244_; uint8_t v___y_1249_; uint8_t v___y_1250_; uint8_t v___y_1255_; uint32_t v___x_1259_; uint8_t v___x_1260_; 
v___x_1216_ = lean_unsigned_to_nat(0u);
v___x_1217_ = lean_nat_dec_eq(v___x_1193_, v___x_1216_);
v___x_1218_ = 1;
v___x_1219_ = lean_nat_add(v_startInclusive_1198_, v_a_1195_);
lean_dec(v_a_1195_);
v___x_1220_ = lean_string_utf8_get_fast(v_str_1197_, v___x_1219_);
v___x_1221_ = lean_string_utf8_next_fast(v_str_1197_, v___x_1219_);
lean_dec(v___x_1219_);
v___x_1222_ = lean_nat_sub(v___x_1221_, v_startInclusive_1198_);
v___x_1259_ = 48;
v___x_1260_ = lean_uint32_dec_le(v___x_1259_, v___x_1220_);
if (v___x_1260_ == 0)
{
v___y_1255_ = v___x_1260_;
goto v___jp_1254_;
}
else
{
uint32_t v___x_1261_; uint8_t v___x_1262_; 
v___x_1261_ = 57;
v___x_1262_ = lean_uint32_dec_le(v___x_1220_, v___x_1261_);
v___y_1255_ = v___x_1262_;
goto v___jp_1254_;
}
v___jp_1223_:
{
uint32_t v___x_1226_; uint8_t v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1231_; 
v___x_1226_ = 95;
v___x_1227_ = lean_uint32_dec_eq(v___x_1220_, v___x_1226_);
v___x_1228_ = lean_box(v___y_1224_);
v___x_1229_ = lean_box(v___y_1225_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 1, v___x_1229_);
lean_ctor_set(v___x_1214_, 0, v___x_1228_);
v___x_1231_ = v___x_1214_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1228_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v___x_1229_);
v___x_1231_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_object* v___x_1232_; lean_object* v___x_1234_; 
v___x_1232_ = lean_box(v___x_1227_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 1, v___x_1231_);
lean_ctor_set(v___x_1210_, 0, v___x_1232_);
v___x_1234_ = v___x_1210_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1232_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v___x_1231_);
v___x_1234_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
lean_object* v___x_1235_; lean_object* v___x_1237_; 
v___x_1235_ = lean_box(v___x_1217_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 1, v___x_1234_);
lean_ctor_set(v___x_1206_, 0, v___x_1235_);
v___x_1237_ = v___x_1206_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1235_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v___x_1234_);
v___x_1237_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
v_a_1195_ = v___x_1222_;
v_b_1196_ = v___x_1237_;
goto _start;
}
}
}
}
v___jp_1242_:
{
uint8_t v___x_1245_; 
v___x_1245_ = lean_unbox(v_fst_1208_);
lean_dec(v_fst_1208_);
if (v___x_1245_ == 0)
{
v___y_1224_ = v___y_1243_;
v___y_1225_ = v___y_1244_;
goto v___jp_1223_;
}
else
{
uint32_t v___x_1246_; uint8_t v___x_1247_; 
v___x_1246_ = 95;
v___x_1247_ = lean_uint32_dec_eq(v___x_1220_, v___x_1246_);
if (v___x_1247_ == 0)
{
v___y_1224_ = v___y_1243_;
v___y_1225_ = v___y_1244_;
goto v___jp_1223_;
}
else
{
v___y_1224_ = v___y_1243_;
v___y_1225_ = v___x_1217_;
goto v___jp_1223_;
}
}
}
v___jp_1248_:
{
uint8_t v___x_1251_; 
v___x_1251_ = lean_unbox(v_fst_1204_);
lean_dec(v_fst_1204_);
if (v___x_1251_ == 0)
{
v___y_1243_ = v___y_1249_;
v___y_1244_ = v___y_1250_;
goto v___jp_1242_;
}
else
{
uint32_t v___x_1252_; uint8_t v___x_1253_; 
v___x_1252_ = 95;
v___x_1253_ = lean_uint32_dec_eq(v___x_1220_, v___x_1252_);
if (v___x_1253_ == 0)
{
v___y_1243_ = v___y_1249_;
v___y_1244_ = v___y_1250_;
goto v___jp_1242_;
}
else
{
lean_dec(v_fst_1208_);
v___y_1224_ = v___y_1249_;
v___y_1225_ = v___x_1217_;
goto v___jp_1223_;
}
}
}
v___jp_1254_:
{
uint8_t v___x_1256_; 
v___x_1256_ = lean_unbox(v_snd_1212_);
lean_dec(v_snd_1212_);
if (v___x_1256_ == 0)
{
lean_dec(v_fst_1208_);
lean_dec(v_fst_1204_);
v___y_1224_ = v___y_1255_;
v___y_1225_ = v___x_1217_;
goto v___jp_1223_;
}
else
{
if (v___y_1255_ == 0)
{
uint32_t v___x_1257_; uint8_t v___x_1258_; 
v___x_1257_ = 95;
v___x_1258_ = lean_uint32_dec_eq(v___x_1220_, v___x_1257_);
if (v___x_1258_ == 0)
{
lean_dec(v_fst_1208_);
lean_dec(v_fst_1204_);
v___y_1224_ = v___y_1255_;
v___y_1225_ = v___x_1217_;
goto v___jp_1223_;
}
else
{
v___y_1249_ = v___y_1255_;
v___y_1250_ = v___x_1258_;
goto v___jp_1248_;
}
}
else
{
v___y_1249_ = v___y_1255_;
v___y_1250_ = v___x_1218_;
goto v___jp_1248_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1195_);
return v_b_1196_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg___boxed(lean_object* v___x_1269_, lean_object* v___y_1270_, lean_object* v_a_1271_, lean_object* v_b_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(v___x_1269_, v___y_1270_, v_a_1271_, v_b_1272_);
lean_dec_ref(v___y_1270_);
lean_dec(v___x_1269_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toNat_x3f(lean_object* v_s_1274_){
_start:
{
lean_object* v_str_1275_; lean_object* v_startPos_1276_; lean_object* v_stopPos_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1330_; 
v_str_1275_ = lean_ctor_get(v_s_1274_, 0);
v_startPos_1276_ = lean_ctor_get(v_s_1274_, 1);
v_stopPos_1277_ = lean_ctor_get(v_s_1274_, 2);
v_isSharedCheck_1330_ = !lean_is_exclusive(v_s_1274_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1279_ = v_s_1274_;
v_isShared_1280_ = v_isSharedCheck_1330_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_stopPos_1277_);
lean_inc(v_startPos_1276_);
lean_inc(v_str_1275_);
lean_dec(v_s_1274_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1330_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___y_1284_; uint8_t v___y_1291_; uint8_t v___y_1292_; uint8_t v___x_1296_; 
v___x_1281_ = lean_nat_sub(v_stopPos_1277_, v_startPos_1276_);
v___x_1282_ = lean_unsigned_to_nat(0u);
v___x_1296_ = lean_nat_dec_eq(v___x_1281_, v___x_1282_);
if (v___x_1296_ == 0)
{
uint8_t v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___y_1306_; uint8_t v___y_1320_; uint8_t v___x_1324_; uint8_t v___y_1326_; uint8_t v___x_1327_; 
v___x_1297_ = 1;
v___x_1298_ = lean_box(v___x_1296_);
v___x_1299_ = lean_box(v___x_1297_);
v___x_1300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1298_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
v___x_1301_ = lean_box(v___x_1296_);
v___x_1302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
lean_ctor_set(v___x_1302_, 1, v___x_1300_);
v___x_1303_ = lean_box(v___x_1297_);
v___x_1304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
lean_ctor_set(v___x_1304_, 1, v___x_1302_);
v___x_1324_ = lean_string_is_valid_pos(v_str_1275_, v_startPos_1276_);
v___x_1327_ = lean_string_is_valid_pos(v_str_1275_, v_stopPos_1277_);
if (v___x_1327_ == 0)
{
v___y_1326_ = v___x_1327_;
goto v___jp_1325_;
}
else
{
uint8_t v___x_1328_; 
v___x_1328_ = lean_nat_dec_le(v_startPos_1276_, v_stopPos_1277_);
v___y_1326_ = v___x_1328_;
goto v___jp_1325_;
}
v___jp_1305_:
{
lean_object* v___x_1307_; lean_object* v_snd_1308_; lean_object* v_snd_1309_; lean_object* v_snd_1310_; uint8_t v___x_1311_; 
v___x_1307_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(v___x_1281_, v___y_1306_, v___x_1282_, v___x_1304_);
lean_dec_ref(v___y_1306_);
lean_dec(v___x_1281_);
v_snd_1308_ = lean_ctor_get(v___x_1307_, 1);
lean_inc(v_snd_1308_);
lean_dec_ref(v___x_1307_);
v_snd_1309_ = lean_ctor_get(v_snd_1308_, 1);
lean_inc(v_snd_1309_);
lean_dec(v_snd_1308_);
v_snd_1310_ = lean_ctor_get(v_snd_1309_, 1);
v___x_1311_ = lean_unbox(v_snd_1310_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; 
lean_dec(v_snd_1309_);
lean_del_object(v___x_1279_);
lean_dec(v_stopPos_1277_);
lean_dec(v_startPos_1276_);
lean_dec_ref(v_str_1275_);
v___x_1312_ = lean_box(0);
return v___x_1312_;
}
else
{
lean_object* v_fst_1313_; uint8_t v___x_1314_; 
v_fst_1313_ = lean_ctor_get(v_snd_1309_, 0);
lean_inc(v_fst_1313_);
lean_dec(v_snd_1309_);
v___x_1314_ = lean_unbox(v_fst_1313_);
lean_dec(v_fst_1313_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1315_; 
lean_del_object(v___x_1279_);
lean_dec(v_stopPos_1277_);
lean_dec(v_startPos_1276_);
lean_dec_ref(v_str_1275_);
v___x_1315_ = lean_box(0);
return v___x_1315_;
}
else
{
uint8_t v___x_1316_; uint8_t v___x_1317_; 
v___x_1316_ = lean_string_is_valid_pos(v_str_1275_, v_startPos_1276_);
v___x_1317_ = lean_string_is_valid_pos(v_str_1275_, v_stopPos_1277_);
if (v___x_1317_ == 0)
{
v___y_1291_ = v___x_1316_;
v___y_1292_ = v___x_1317_;
goto v___jp_1290_;
}
else
{
uint8_t v___x_1318_; 
v___x_1318_ = lean_nat_dec_le(v_startPos_1276_, v_stopPos_1277_);
v___y_1291_ = v___x_1316_;
v___y_1292_ = v___x_1318_;
goto v___jp_1290_;
}
}
}
}
v___jp_1319_:
{
if (v___y_1320_ == 0)
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_1322_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_1321_);
v___y_1306_ = v___x_1322_;
goto v___jp_1305_;
}
else
{
lean_object* v___x_1323_; 
lean_inc(v_stopPos_1277_);
lean_inc(v_startPos_1276_);
lean_inc_ref(v_str_1275_);
v___x_1323_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1323_, 0, v_str_1275_);
lean_ctor_set(v___x_1323_, 1, v_startPos_1276_);
lean_ctor_set(v___x_1323_, 2, v_stopPos_1277_);
v___y_1306_ = v___x_1323_;
goto v___jp_1305_;
}
}
v___jp_1325_:
{
if (v___x_1324_ == 0)
{
v___y_1320_ = v___x_1324_;
goto v___jp_1319_;
}
else
{
v___y_1320_ = v___y_1326_;
goto v___jp_1319_;
}
}
}
else
{
lean_object* v___x_1329_; 
lean_dec(v___x_1281_);
lean_del_object(v___x_1279_);
lean_dec(v_stopPos_1277_);
lean_dec(v_startPos_1276_);
lean_dec_ref(v_str_1275_);
v___x_1329_ = lean_box(0);
return v___x_1329_;
}
v___jp_1283_:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(v___y_1284_, v___x_1282_, v___x_1282_);
lean_dec_ref(v___y_1284_);
v___x_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
return v___x_1286_;
}
v___jp_1287_:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_1289_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_1288_);
v___y_1284_ = v___x_1289_;
goto v___jp_1283_;
}
v___jp_1290_:
{
if (v___y_1291_ == 0)
{
lean_del_object(v___x_1279_);
lean_dec(v_stopPos_1277_);
lean_dec(v_startPos_1276_);
lean_dec_ref(v_str_1275_);
goto v___jp_1287_;
}
else
{
if (v___y_1292_ == 0)
{
lean_del_object(v___x_1279_);
lean_dec(v_stopPos_1277_);
lean_dec(v_startPos_1276_);
lean_dec_ref(v_str_1275_);
goto v___jp_1287_;
}
else
{
lean_object* v___x_1294_; 
if (v_isShared_1280_ == 0)
{
v___x_1294_ = v___x_1279_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_str_1275_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v_startPos_1276_);
lean_ctor_set(v_reuseFailAlloc_1295_, 2, v_stopPos_1277_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
v___y_1284_ = v___x_1294_;
goto v___jp_1283_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0(lean_object* v___x_1331_, lean_object* v___y_1332_, lean_object* v_inst_1333_, lean_object* v_R_1334_, lean_object* v_a_1335_, lean_object* v_b_1336_, lean_object* v_c_1337_){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(v___x_1331_, v___y_1332_, v_a_1335_, v_b_1336_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___boxed(lean_object* v___x_1339_, lean_object* v___y_1340_, lean_object* v_inst_1341_, lean_object* v_R_1342_, lean_object* v_a_1343_, lean_object* v_b_1344_, lean_object* v_c_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0(v___x_1339_, v___y_1340_, v_inst_1341_, v_R_1342_, v_a_1343_, v_b_1344_, v_c_1345_);
lean_dec_ref(v___y_1340_);
lean_dec(v___x_1339_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1(lean_object* v___y_1347_, lean_object* v_inst_1348_, lean_object* v_R_1349_, lean_object* v_a_1350_, lean_object* v_b_1351_, lean_object* v_c_1352_){
_start:
{
lean_object* v___x_1353_; 
v___x_1353_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(v___y_1347_, v_a_1350_, v_b_1351_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___boxed(lean_object* v___y_1354_, lean_object* v_inst_1355_, lean_object* v_R_1356_, lean_object* v_a_1357_, lean_object* v_b_1358_, lean_object* v_c_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1(v___y_1354_, v_inst_1355_, v_R_1356_, v_a_1357_, v_b_1358_, v_c_1359_);
lean_dec_ref(v___y_1354_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_repair(lean_object* v_x_1361_){
_start:
{
lean_object* v_str_1362_; lean_object* v_startPos_1363_; lean_object* v_stopPos_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1380_; 
v_str_1362_ = lean_ctor_get(v_x_1361_, 0);
v_startPos_1363_ = lean_ctor_get(v_x_1361_, 1);
v_stopPos_1364_ = lean_ctor_get(v_x_1361_, 2);
v_isSharedCheck_1380_ = !lean_is_exclusive(v_x_1361_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1366_ = v_x_1361_;
v_isShared_1367_ = v_isSharedCheck_1380_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_stopPos_1364_);
lean_inc(v_startPos_1363_);
lean_inc(v_str_1362_);
lean_dec(v_x_1361_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1380_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___y_1369_; uint8_t v___x_1378_; 
v___x_1378_ = lean_string_is_valid_pos(v_str_1362_, v_startPos_1363_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; 
lean_dec(v_startPos_1363_);
v___x_1379_ = lean_string_utf8_byte_size(v_str_1362_);
v___y_1369_ = v___x_1379_;
goto v___jp_1368_;
}
else
{
v___y_1369_ = v_startPos_1363_;
goto v___jp_1368_;
}
v___jp_1368_:
{
uint8_t v___x_1370_; 
v___x_1370_ = lean_string_is_valid_pos(v_str_1362_, v_stopPos_1364_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; lean_object* v___x_1373_; 
lean_dec(v_stopPos_1364_);
v___x_1371_ = lean_string_utf8_byte_size(v_str_1362_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 2, v___x_1371_);
lean_ctor_set(v___x_1366_, 1, v___y_1369_);
v___x_1373_ = v___x_1366_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_str_1362_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v___y_1369_);
lean_ctor_set(v_reuseFailAlloc_1374_, 2, v___x_1371_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
else
{
lean_object* v___x_1376_; 
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 1, v___y_1369_);
v___x_1376_ = v___x_1366_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_str_1362_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v___y_1369_);
lean_ctor_set(v_reuseFailAlloc_1377_, 2, v_stopPos_1364_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_beq(lean_object* v_ss1_1381_, lean_object* v_ss2_1382_){
_start:
{
lean_object* v_ss1_1383_; lean_object* v_str_1384_; lean_object* v_startPos_1385_; lean_object* v_stopPos_1386_; lean_object* v_ss2_1387_; lean_object* v_str_1388_; lean_object* v_startPos_1389_; lean_object* v_stopPos_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; uint8_t v___x_1393_; 
v_ss1_1383_ = l_Substring_Raw_repair(v_ss1_1381_);
v_str_1384_ = lean_ctor_get(v_ss1_1383_, 0);
lean_inc_ref(v_str_1384_);
v_startPos_1385_ = lean_ctor_get(v_ss1_1383_, 1);
lean_inc(v_startPos_1385_);
v_stopPos_1386_ = lean_ctor_get(v_ss1_1383_, 2);
lean_inc(v_stopPos_1386_);
lean_dec_ref(v_ss1_1383_);
v_ss2_1387_ = l_Substring_Raw_repair(v_ss2_1382_);
v_str_1388_ = lean_ctor_get(v_ss2_1387_, 0);
lean_inc_ref(v_str_1388_);
v_startPos_1389_ = lean_ctor_get(v_ss2_1387_, 1);
lean_inc(v_startPos_1389_);
v_stopPos_1390_ = lean_ctor_get(v_ss2_1387_, 2);
lean_inc(v_stopPos_1390_);
lean_dec_ref(v_ss2_1387_);
v___x_1391_ = lean_nat_sub(v_stopPos_1386_, v_startPos_1385_);
lean_dec(v_stopPos_1386_);
v___x_1392_ = lean_nat_sub(v_stopPos_1390_, v_startPos_1389_);
lean_dec(v_stopPos_1390_);
v___x_1393_ = lean_nat_dec_eq(v___x_1391_, v___x_1392_);
lean_dec(v___x_1392_);
if (v___x_1393_ == 0)
{
lean_dec(v___x_1391_);
lean_dec(v_startPos_1389_);
lean_dec_ref(v_str_1388_);
lean_dec(v_startPos_1385_);
lean_dec_ref(v_str_1384_);
return v___x_1393_;
}
else
{
uint8_t v___x_1394_; 
v___x_1394_ = l_String_Pos_Raw_substrEq(v_str_1384_, v_startPos_1385_, v_str_1388_, v_startPos_1389_, v___x_1391_);
lean_dec(v___x_1391_);
lean_dec_ref(v_str_1388_);
lean_dec_ref(v_str_1384_);
return v___x_1394_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_beq___boxed(lean_object* v_ss1_1395_, lean_object* v_ss2_1396_){
_start:
{
uint8_t v_res_1397_; lean_object* v_r_1398_; 
v_res_1397_ = l_Substring_Raw_beq(v_ss1_1395_, v_ss2_1396_);
v_r_1398_ = lean_box(v_res_1397_);
return v_r_1398_;
}
}
LEAN_EXPORT uint8_t lean_substring_beq(lean_object* v_ss1_1399_, lean_object* v_ss2_1400_){
_start:
{
uint8_t v___x_1401_; 
v___x_1401_ = l_Substring_Raw_beq(v_ss1_1399_, v_ss2_1400_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_beqImpl___boxed(lean_object* v_ss1_1402_, lean_object* v_ss2_1403_){
_start:
{
uint8_t v_res_1404_; lean_object* v_r_1405_; 
v_res_1404_ = lean_substring_beq(v_ss1_1402_, v_ss2_1403_);
v_r_1405_ = lean_box(v_res_1404_);
return v_r_1405_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_sameAs(lean_object* v_ss1_1408_, lean_object* v_ss2_1409_){
_start:
{
lean_object* v_startPos_1410_; lean_object* v_startPos_1411_; uint8_t v_decide_1412_; 
v_startPos_1410_ = lean_ctor_get(v_ss1_1408_, 1);
v_startPos_1411_ = lean_ctor_get(v_ss2_1409_, 1);
v_decide_1412_ = lean_nat_dec_eq(v_startPos_1410_, v_startPos_1411_);
if (v_decide_1412_ == 0)
{
lean_dec_ref(v_ss2_1409_);
lean_dec_ref(v_ss1_1408_);
return v_decide_1412_;
}
else
{
uint8_t v___x_1413_; 
v___x_1413_ = l_Substring_Raw_beq(v_ss1_1408_, v_ss2_1409_);
return v___x_1413_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_sameAs___boxed(lean_object* v_ss1_1414_, lean_object* v_ss2_1415_){
_start:
{
uint8_t v_res_1416_; lean_object* v_r_1417_; 
v_res_1416_ = l_Substring_Raw_sameAs(v_ss1_1414_, v_ss2_1415_);
v_r_1417_ = lean_box(v_res_1416_);
return v_r_1417_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(lean_object* v_s_1418_, lean_object* v_t_1419_, lean_object* v_spos_1420_, lean_object* v_tpos_1421_){
_start:
{
lean_object* v_str_1422_; lean_object* v_stopPos_1423_; lean_object* v_str_1424_; lean_object* v_stopPos_1425_; uint8_t v___y_1427_; uint8_t v___x_1434_; 
v_str_1422_ = lean_ctor_get(v_s_1418_, 0);
v_stopPos_1423_ = lean_ctor_get(v_s_1418_, 2);
v_str_1424_ = lean_ctor_get(v_t_1419_, 0);
v_stopPos_1425_ = lean_ctor_get(v_t_1419_, 2);
v___x_1434_ = l_String_instDecidableLtRaw(v_spos_1420_, v_stopPos_1423_);
if (v___x_1434_ == 0)
{
v___y_1427_ = v___x_1434_;
goto v___jp_1426_;
}
else
{
uint8_t v___x_1435_; 
v___x_1435_ = l_String_instDecidableLtRaw(v_tpos_1421_, v_stopPos_1425_);
v___y_1427_ = v___x_1435_;
goto v___jp_1426_;
}
v___jp_1426_:
{
if (v___y_1427_ == 0)
{
lean_dec(v_tpos_1421_);
return v_spos_1420_;
}
else
{
uint32_t v___x_1428_; uint32_t v___x_1429_; uint8_t v___x_1430_; 
v___x_1428_ = lean_string_utf8_get(v_str_1422_, v_spos_1420_);
v___x_1429_ = lean_string_utf8_get(v_str_1424_, v_tpos_1421_);
v___x_1430_ = lean_uint32_dec_eq(v___x_1428_, v___x_1429_);
if (v___x_1430_ == 0)
{
lean_dec(v_tpos_1421_);
return v_spos_1420_;
}
else
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1431_ = lean_string_utf8_next(v_str_1422_, v_spos_1420_);
lean_dec(v_spos_1420_);
v___x_1432_ = lean_string_utf8_next(v_str_1424_, v_tpos_1421_);
lean_dec(v_tpos_1421_);
v_spos_1420_ = v___x_1431_;
v_tpos_1421_ = v___x_1432_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop___boxed(lean_object* v_s_1436_, lean_object* v_t_1437_, lean_object* v_spos_1438_, lean_object* v_tpos_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(v_s_1436_, v_t_1437_, v_spos_1438_, v_tpos_1439_);
lean_dec_ref(v_t_1437_);
lean_dec_ref(v_s_1436_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_commonPrefix(lean_object* v_s_1441_, lean_object* v_t_1442_){
_start:
{
lean_object* v_str_1443_; lean_object* v_startPos_1444_; lean_object* v_startPos_1445_; lean_object* v___x_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
v_str_1443_ = lean_ctor_get(v_s_1441_, 0);
lean_inc_ref(v_str_1443_);
v_startPos_1444_ = lean_ctor_get(v_s_1441_, 1);
lean_inc_n(v_startPos_1444_, 2);
v_startPos_1445_ = lean_ctor_get(v_t_1442_, 1);
lean_inc(v_startPos_1445_);
v___x_1446_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(v_s_1441_, v_t_1442_, v_startPos_1444_, v_startPos_1445_);
lean_dec_ref(v_s_1441_);
v_isSharedCheck_1453_ = !lean_is_exclusive(v_t_1442_);
if (v_isSharedCheck_1453_ == 0)
{
lean_object* v_unused_1454_; lean_object* v_unused_1455_; lean_object* v_unused_1456_; 
v_unused_1454_ = lean_ctor_get(v_t_1442_, 2);
lean_dec(v_unused_1454_);
v_unused_1455_ = lean_ctor_get(v_t_1442_, 1);
lean_dec(v_unused_1455_);
v_unused_1456_ = lean_ctor_get(v_t_1442_, 0);
lean_dec(v_unused_1456_);
v___x_1448_ = v_t_1442_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_dec(v_t_1442_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
lean_ctor_set(v___x_1448_, 2, v___x_1446_);
lean_ctor_set(v___x_1448_, 1, v_startPos_1444_);
lean_ctor_set(v___x_1448_, 0, v_str_1443_);
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_str_1443_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_startPos_1444_);
lean_ctor_set(v_reuseFailAlloc_1452_, 2, v___x_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(lean_object* v_s_1457_, lean_object* v_t_1458_, lean_object* v_spos_1459_, lean_object* v_tpos_1460_){
_start:
{
lean_object* v_str_1461_; lean_object* v_startPos_1462_; lean_object* v_str_1463_; lean_object* v_startPos_1464_; uint8_t v___y_1466_; uint8_t v___x_1473_; 
v_str_1461_ = lean_ctor_get(v_s_1457_, 0);
v_startPos_1462_ = lean_ctor_get(v_s_1457_, 1);
v_str_1463_ = lean_ctor_get(v_t_1458_, 0);
v_startPos_1464_ = lean_ctor_get(v_t_1458_, 1);
v___x_1473_ = l_String_instDecidableLtRaw(v_startPos_1462_, v_spos_1459_);
if (v___x_1473_ == 0)
{
v___y_1466_ = v___x_1473_;
goto v___jp_1465_;
}
else
{
uint8_t v___x_1474_; 
v___x_1474_ = l_String_instDecidableLtRaw(v_startPos_1464_, v_tpos_1460_);
v___y_1466_ = v___x_1474_;
goto v___jp_1465_;
}
v___jp_1465_:
{
if (v___y_1466_ == 0)
{
lean_dec(v_tpos_1460_);
return v_spos_1459_;
}
else
{
lean_object* v_spos_x27_1467_; lean_object* v_tpos_x27_1468_; uint32_t v___x_1469_; uint32_t v___x_1470_; uint8_t v___x_1471_; 
v_spos_x27_1467_ = lean_string_utf8_prev(v_str_1461_, v_spos_1459_);
v_tpos_x27_1468_ = lean_string_utf8_prev(v_str_1463_, v_tpos_1460_);
lean_dec(v_tpos_1460_);
v___x_1469_ = lean_string_utf8_get(v_str_1461_, v_spos_x27_1467_);
v___x_1470_ = lean_string_utf8_get(v_str_1463_, v_tpos_x27_1468_);
v___x_1471_ = lean_uint32_dec_eq(v___x_1469_, v___x_1470_);
if (v___x_1471_ == 0)
{
lean_dec(v_tpos_x27_1468_);
lean_dec(v_spos_x27_1467_);
return v_spos_1459_;
}
else
{
lean_dec(v_spos_1459_);
v_spos_1459_ = v_spos_x27_1467_;
v_tpos_1460_ = v_tpos_x27_1468_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop___boxed(lean_object* v_s_1475_, lean_object* v_t_1476_, lean_object* v_spos_1477_, lean_object* v_tpos_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(v_s_1475_, v_t_1476_, v_spos_1477_, v_tpos_1478_);
lean_dec_ref(v_t_1476_);
lean_dec_ref(v_s_1475_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_commonSuffix(lean_object* v_s_1480_, lean_object* v_t_1481_){
_start:
{
lean_object* v_str_1482_; lean_object* v_stopPos_1483_; lean_object* v_stopPos_1484_; lean_object* v___x_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
v_str_1482_ = lean_ctor_get(v_s_1480_, 0);
lean_inc_ref(v_str_1482_);
v_stopPos_1483_ = lean_ctor_get(v_s_1480_, 2);
lean_inc_n(v_stopPos_1483_, 2);
v_stopPos_1484_ = lean_ctor_get(v_t_1481_, 2);
lean_inc(v_stopPos_1484_);
v___x_1485_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(v_s_1480_, v_t_1481_, v_stopPos_1483_, v_stopPos_1484_);
lean_dec_ref(v_s_1480_);
v_isSharedCheck_1492_ = !lean_is_exclusive(v_t_1481_);
if (v_isSharedCheck_1492_ == 0)
{
lean_object* v_unused_1493_; lean_object* v_unused_1494_; lean_object* v_unused_1495_; 
v_unused_1493_ = lean_ctor_get(v_t_1481_, 2);
lean_dec(v_unused_1493_);
v_unused_1494_ = lean_ctor_get(v_t_1481_, 1);
lean_dec(v_unused_1494_);
v_unused_1495_ = lean_ctor_get(v_t_1481_, 0);
lean_dec(v_unused_1495_);
v___x_1487_ = v_t_1481_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_dec(v_t_1481_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 2, v_stopPos_1483_);
lean_ctor_set(v___x_1487_, 1, v___x_1485_);
lean_ctor_set(v___x_1487_, 0, v_str_1482_);
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_str_1482_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v___x_1485_);
lean_ctor_set(v_reuseFailAlloc_1491_, 2, v_stopPos_1483_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropPrefix_x3f(lean_object* v_s_1496_, lean_object* v_pre_1497_){
_start:
{
lean_object* v_t_1498_; lean_object* v_startPos_1499_; lean_object* v_stopPos_1500_; lean_object* v_startPos_1501_; lean_object* v_stopPos_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; uint8_t v___x_1505_; 
lean_inc_ref(v_pre_1497_);
lean_inc_ref(v_s_1496_);
v_t_1498_ = l_Substring_Raw_commonPrefix(v_s_1496_, v_pre_1497_);
v_startPos_1499_ = lean_ctor_get(v_t_1498_, 1);
lean_inc(v_startPos_1499_);
v_stopPos_1500_ = lean_ctor_get(v_t_1498_, 2);
lean_inc(v_stopPos_1500_);
lean_dec_ref(v_t_1498_);
v_startPos_1501_ = lean_ctor_get(v_pre_1497_, 1);
lean_inc(v_startPos_1501_);
v_stopPos_1502_ = lean_ctor_get(v_pre_1497_, 2);
lean_inc(v_stopPos_1502_);
lean_dec_ref(v_pre_1497_);
v___x_1503_ = lean_nat_sub(v_stopPos_1500_, v_startPos_1499_);
lean_dec(v_startPos_1499_);
v___x_1504_ = lean_nat_sub(v_stopPos_1502_, v_startPos_1501_);
lean_dec(v_startPos_1501_);
lean_dec(v_stopPos_1502_);
v___x_1505_ = lean_nat_dec_eq(v___x_1503_, v___x_1504_);
lean_dec(v___x_1504_);
lean_dec(v___x_1503_);
if (v___x_1505_ == 0)
{
lean_object* v___x_1506_; 
lean_dec(v_stopPos_1500_);
lean_dec_ref(v_s_1496_);
v___x_1506_ = lean_box(0);
return v___x_1506_;
}
else
{
lean_object* v_str_1507_; lean_object* v_stopPos_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1516_; 
v_str_1507_ = lean_ctor_get(v_s_1496_, 0);
v_stopPos_1508_ = lean_ctor_get(v_s_1496_, 2);
v_isSharedCheck_1516_ = !lean_is_exclusive(v_s_1496_);
if (v_isSharedCheck_1516_ == 0)
{
lean_object* v_unused_1517_; 
v_unused_1517_ = lean_ctor_get(v_s_1496_, 1);
lean_dec(v_unused_1517_);
v___x_1510_ = v_s_1496_;
v_isShared_1511_ = v_isSharedCheck_1516_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_stopPos_1508_);
lean_inc(v_str_1507_);
lean_dec(v_s_1496_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1516_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 1, v_stopPos_1500_);
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_str_1507_);
lean_ctor_set(v_reuseFailAlloc_1515_, 1, v_stopPos_1500_);
lean_ctor_set(v_reuseFailAlloc_1515_, 2, v_stopPos_1508_);
v___x_1513_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
lean_object* v___x_1514_; 
v___x_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
return v___x_1514_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropSuffix_x3f(lean_object* v_s_1518_, lean_object* v_suff_1519_){
_start:
{
lean_object* v_t_1520_; lean_object* v_startPos_1521_; lean_object* v_stopPos_1522_; lean_object* v_startPos_1523_; lean_object* v_stopPos_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; uint8_t v___x_1527_; 
lean_inc_ref(v_suff_1519_);
lean_inc_ref(v_s_1518_);
v_t_1520_ = l_Substring_Raw_commonSuffix(v_s_1518_, v_suff_1519_);
v_startPos_1521_ = lean_ctor_get(v_t_1520_, 1);
lean_inc(v_startPos_1521_);
v_stopPos_1522_ = lean_ctor_get(v_t_1520_, 2);
lean_inc(v_stopPos_1522_);
lean_dec_ref(v_t_1520_);
v_startPos_1523_ = lean_ctor_get(v_suff_1519_, 1);
lean_inc(v_startPos_1523_);
v_stopPos_1524_ = lean_ctor_get(v_suff_1519_, 2);
lean_inc(v_stopPos_1524_);
lean_dec_ref(v_suff_1519_);
v___x_1525_ = lean_nat_sub(v_stopPos_1522_, v_startPos_1521_);
lean_dec(v_stopPos_1522_);
v___x_1526_ = lean_nat_sub(v_stopPos_1524_, v_startPos_1523_);
lean_dec(v_startPos_1523_);
lean_dec(v_stopPos_1524_);
v___x_1527_ = lean_nat_dec_eq(v___x_1525_, v___x_1526_);
lean_dec(v___x_1526_);
lean_dec(v___x_1525_);
if (v___x_1527_ == 0)
{
lean_object* v___x_1528_; 
lean_dec(v_startPos_1521_);
lean_dec_ref(v_s_1518_);
v___x_1528_ = lean_box(0);
return v___x_1528_;
}
else
{
lean_object* v_str_1529_; lean_object* v_startPos_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1538_; 
v_str_1529_ = lean_ctor_get(v_s_1518_, 0);
v_startPos_1530_ = lean_ctor_get(v_s_1518_, 1);
v_isSharedCheck_1538_ = !lean_is_exclusive(v_s_1518_);
if (v_isSharedCheck_1538_ == 0)
{
lean_object* v_unused_1539_; 
v_unused_1539_ = lean_ctor_get(v_s_1518_, 2);
lean_dec(v_unused_1539_);
v___x_1532_ = v_s_1518_;
v_isShared_1533_ = v_isSharedCheck_1538_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_startPos_1530_);
lean_inc(v_str_1529_);
lean_dec(v_s_1518_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1538_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 2, v_startPos_1521_);
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_str_1529_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_startPos_1530_);
lean_ctor_set(v_reuseFailAlloc_1537_, 2, v_startPos_1521_);
v___x_1535_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_object* v___x_1536_; 
v___x_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1535_);
return v___x_1536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg(lean_object* v_x_1540_, lean_object* v_x_1541_, lean_object* v_x_1542_, lean_object* v_h__1_1543_, lean_object* v_h__2_1544_){
_start:
{
lean_object* v_zero_1545_; uint8_t v_isZero_1546_; 
v_zero_1545_ = lean_unsigned_to_nat(0u);
v_isZero_1546_ = lean_nat_dec_eq(v_x_1541_, v_zero_1545_);
if (v_isZero_1546_ == 1)
{
lean_object* v___x_1547_; 
lean_dec(v_h__2_1544_);
v___x_1547_ = lean_apply_2(v_h__1_1543_, v_x_1540_, v_x_1542_);
return v___x_1547_;
}
else
{
lean_object* v_one_1548_; lean_object* v_n_1549_; lean_object* v___x_1550_; 
lean_dec(v_h__1_1543_);
v_one_1548_ = lean_unsigned_to_nat(1u);
v_n_1549_ = lean_nat_sub(v_x_1541_, v_one_1548_);
v___x_1550_ = lean_apply_3(v_h__2_1544_, v_x_1540_, v_n_1549_, v_x_1542_);
return v___x_1550_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg___boxed(lean_object* v_x_1551_, lean_object* v_x_1552_, lean_object* v_x_1553_, lean_object* v_h__1_1554_, lean_object* v_h__2_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg(v_x_1551_, v_x_1552_, v_x_1553_, v_h__1_1554_, v_h__2_1555_);
lean_dec(v_x_1552_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter(lean_object* v_motive_1557_, lean_object* v_x_1558_, lean_object* v_x_1559_, lean_object* v_x_1560_, lean_object* v_h__1_1561_, lean_object* v_h__2_1562_){
_start:
{
lean_object* v_zero_1563_; uint8_t v_isZero_1564_; 
v_zero_1563_ = lean_unsigned_to_nat(0u);
v_isZero_1564_ = lean_nat_dec_eq(v_x_1559_, v_zero_1563_);
if (v_isZero_1564_ == 1)
{
lean_object* v___x_1565_; 
lean_dec(v_h__2_1562_);
v___x_1565_ = lean_apply_2(v_h__1_1561_, v_x_1558_, v_x_1560_);
return v___x_1565_;
}
else
{
lean_object* v_one_1566_; lean_object* v_n_1567_; lean_object* v___x_1568_; 
lean_dec(v_h__1_1561_);
v_one_1566_ = lean_unsigned_to_nat(1u);
v_n_1567_ = lean_nat_sub(v_x_1559_, v_one_1566_);
v___x_1568_ = lean_apply_3(v_h__2_1562_, v_x_1558_, v_n_1567_, v_x_1560_);
return v___x_1568_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___boxed(lean_object* v_motive_1569_, lean_object* v_x_1570_, lean_object* v_x_1571_, lean_object* v_x_1572_, lean_object* v_h__1_1573_, lean_object* v_h__2_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter(v_motive_1569_, v_x_1570_, v_x_1571_, v_x_1572_, v_h__1_1573_, v_h__2_1574_);
lean_dec(v_x_1571_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l_Substring_bsize(lean_object* v_a_1576_){
_start:
{
lean_object* v_startPos_1577_; lean_object* v_stopPos_1578_; lean_object* v___x_1579_; 
v_startPos_1577_ = lean_ctor_get(v_a_1576_, 1);
v_stopPos_1578_ = lean_ctor_get(v_a_1576_, 2);
v___x_1579_ = lean_nat_sub(v_stopPos_1578_, v_startPos_1577_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Substring_bsize___boxed(lean_object* v_a_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_Substring_bsize(v_a_1580_);
lean_dec_ref(v_a_1580_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l_Substring_toString(lean_object* v_a_1582_){
_start:
{
lean_object* v_str_1583_; lean_object* v_startPos_1584_; lean_object* v_stopPos_1585_; lean_object* v___x_1586_; 
v_str_1583_ = lean_ctor_get(v_a_1582_, 0);
v_startPos_1584_ = lean_ctor_get(v_a_1582_, 1);
v_stopPos_1585_ = lean_ctor_get(v_a_1582_, 2);
v___x_1586_ = lean_string_utf8_extract(v_str_1583_, v_startPos_1584_, v_stopPos_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Substring_toString___boxed(lean_object* v_a_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_Substring_toString(v_a_1587_);
lean_dec_ref(v_a_1587_);
return v_res_1588_;
}
}
LEAN_EXPORT uint8_t l_Substring_isEmpty(lean_object* v_ss_1589_){
_start:
{
lean_object* v_startPos_1590_; lean_object* v_stopPos_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; uint8_t v___x_1594_; 
v_startPos_1590_ = lean_ctor_get(v_ss_1589_, 1);
v_stopPos_1591_ = lean_ctor_get(v_ss_1589_, 2);
v___x_1592_ = lean_nat_sub(v_stopPos_1591_, v_startPos_1590_);
v___x_1593_ = lean_unsigned_to_nat(0u);
v___x_1594_ = lean_nat_dec_eq(v___x_1592_, v___x_1593_);
lean_dec(v___x_1592_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Substring_isEmpty___boxed(lean_object* v_ss_1595_){
_start:
{
uint8_t v_res_1596_; lean_object* v_r_1597_; 
v_res_1596_ = l_Substring_isEmpty(v_ss_1595_);
lean_dec_ref(v_ss_1595_);
v_r_1597_ = lean_box(v_res_1596_);
return v_r_1597_;
}
}
LEAN_EXPORT lean_object* l_Substring_next(lean_object* v_a_1598_, lean_object* v_a_1599_){
_start:
{
lean_object* v_str_1600_; lean_object* v_startPos_1601_; lean_object* v_stopPos_1602_; lean_object* v_absP_1603_; uint8_t v_decide_1604_; 
v_str_1600_ = lean_ctor_get(v_a_1598_, 0);
v_startPos_1601_ = lean_ctor_get(v_a_1598_, 1);
v_stopPos_1602_ = lean_ctor_get(v_a_1598_, 2);
v_absP_1603_ = lean_nat_add(v_startPos_1601_, v_a_1599_);
v_decide_1604_ = lean_nat_dec_eq(v_absP_1603_, v_stopPos_1602_);
if (v_decide_1604_ == 0)
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1605_ = lean_string_utf8_next(v_str_1600_, v_absP_1603_);
lean_dec(v_absP_1603_);
v___x_1606_ = lean_nat_sub(v___x_1605_, v_startPos_1601_);
lean_dec(v___x_1605_);
return v___x_1606_;
}
else
{
lean_dec(v_absP_1603_);
lean_inc(v_a_1599_);
return v_a_1599_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_next___boxed(lean_object* v_a_1607_, lean_object* v_a_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Substring_next(v_a_1607_, v_a_1608_);
lean_dec(v_a_1608_);
lean_dec_ref(v_a_1607_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Substring_prev(lean_object* v_a_1610_, lean_object* v_a_1611_){
_start:
{
lean_object* v_str_1612_; lean_object* v_startPos_1613_; lean_object* v_absP_1614_; uint8_t v_decide_1615_; 
v_str_1612_ = lean_ctor_get(v_a_1610_, 0);
v_startPos_1613_ = lean_ctor_get(v_a_1610_, 1);
v_absP_1614_ = lean_nat_add(v_startPos_1613_, v_a_1611_);
v_decide_1615_ = lean_nat_dec_eq(v_absP_1614_, v_startPos_1613_);
if (v_decide_1615_ == 0)
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = lean_string_utf8_prev(v_str_1612_, v_absP_1614_);
lean_dec(v_absP_1614_);
v___x_1617_ = lean_nat_sub(v___x_1616_, v_startPos_1613_);
lean_dec(v___x_1616_);
return v___x_1617_;
}
else
{
lean_dec(v_absP_1614_);
lean_inc(v_a_1611_);
return v_a_1611_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_prev___boxed(lean_object* v_a_1618_, lean_object* v_a_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Substring_prev(v_a_1618_, v_a_1619_);
lean_dec(v_a_1619_);
lean_dec_ref(v_a_1618_);
return v_res_1620_;
}
}
LEAN_EXPORT uint8_t l_Substring_atEnd(lean_object* v_a_1621_, lean_object* v_a_1622_){
_start:
{
lean_object* v_startPos_1623_; lean_object* v_stopPos_1624_; lean_object* v___x_1625_; uint8_t v_decide_1626_; 
v_startPos_1623_ = lean_ctor_get(v_a_1621_, 1);
v_stopPos_1624_ = lean_ctor_get(v_a_1621_, 2);
v___x_1625_ = lean_nat_add(v_startPos_1623_, v_a_1622_);
v_decide_1626_ = lean_nat_dec_eq(v___x_1625_, v_stopPos_1624_);
lean_dec(v___x_1625_);
return v_decide_1626_;
}
}
LEAN_EXPORT lean_object* l_Substring_atEnd___boxed(lean_object* v_a_1627_, lean_object* v_a_1628_){
_start:
{
uint8_t v_res_1629_; lean_object* v_r_1630_; 
v_res_1629_ = l_Substring_atEnd(v_a_1627_, v_a_1628_);
lean_dec(v_a_1628_);
lean_dec_ref(v_a_1627_);
v_r_1630_ = lean_box(v_res_1629_);
return v_r_1630_;
}
}
LEAN_EXPORT uint8_t l_Substring_beq(lean_object* v_ss1_1631_, lean_object* v_ss2_1632_){
_start:
{
uint8_t v___x_1633_; 
v___x_1633_ = l_Substring_Raw_beq(v_ss1_1631_, v_ss2_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Substring_beq___boxed(lean_object* v_ss1_1634_, lean_object* v_ss2_1635_){
_start:
{
uint8_t v_res_1636_; lean_object* v_r_1637_; 
v_res_1636_ = l_Substring_beq(v_ss1_1634_, v_ss2_1635_);
v_r_1637_ = lean_box(v_res_1636_);
return v_r_1637_;
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

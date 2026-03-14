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
lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Substring_Raw_Internal_allImpl_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Substring_Raw_Internal_allImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* v___y_702_; lean_object* v_str_710_; lean_object* v_startPos_711_; lean_object* v_stopPos_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_726_; 
v_str_710_ = lean_ctor_get(v_s_699_, 0);
v_startPos_711_ = lean_ctor_get(v_s_699_, 1);
v_stopPos_712_ = lean_ctor_get(v_s_699_, 2);
v_isSharedCheck_726_ = !lean_is_exclusive(v_s_699_);
if (v_isSharedCheck_726_ == 0)
{
v___x_714_ = v_s_699_;
v_isShared_715_ = v_isSharedCheck_726_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_stopPos_712_);
lean_inc(v_startPos_711_);
lean_inc(v_str_710_);
lean_dec(v_s_699_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_726_;
goto v_resetjp_713_;
}
v___jp_701_:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v_startInclusive_706_; lean_object* v_endExclusive_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
lean_inc_ref(v_p_700_);
v___x_703_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v_p_700_);
v___x_704_ = lean_unsigned_to_nat(0u);
v___x_705_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go(lean_box(0), v___y_702_, v_p_700_, v___x_703_, v___x_704_);
lean_dec_ref(v_p_700_);
lean_dec_ref(v___y_702_);
v_startInclusive_706_ = lean_ctor_get(v___x_705_, 1);
lean_inc(v_startInclusive_706_);
v_endExclusive_707_ = lean_ctor_get(v___x_705_, 2);
lean_inc(v_endExclusive_707_);
lean_dec_ref(v___x_705_);
v___x_708_ = lean_nat_sub(v_endExclusive_707_, v_startInclusive_706_);
lean_dec(v_startInclusive_706_);
lean_dec(v_endExclusive_707_);
v___x_709_ = lean_nat_dec_eq(v___x_708_, v___x_704_);
lean_dec(v___x_708_);
return v___x_709_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; uint8_t v___x_720_; 
v___x_716_ = l_String_instInhabitedSlice;
v___x_720_ = lean_string_is_valid_pos(v_str_710_, v_startPos_711_);
if (v___x_720_ == 0)
{
lean_del_object(v___x_714_);
lean_dec(v_stopPos_712_);
lean_dec(v_startPos_711_);
lean_dec_ref(v_str_710_);
goto v___jp_717_;
}
else
{
uint8_t v___x_721_; 
v___x_721_ = lean_string_is_valid_pos(v_str_710_, v_stopPos_712_);
if (v___x_721_ == 0)
{
lean_del_object(v___x_714_);
lean_dec(v_stopPos_712_);
lean_dec(v_startPos_711_);
lean_dec_ref(v_str_710_);
goto v___jp_717_;
}
else
{
uint8_t v___x_722_; 
v___x_722_ = lean_nat_dec_le(v_startPos_711_, v_stopPos_712_);
if (v___x_722_ == 0)
{
lean_del_object(v___x_714_);
lean_dec(v_stopPos_712_);
lean_dec(v_startPos_711_);
lean_dec_ref(v_str_710_);
goto v___jp_717_;
}
else
{
lean_object* v___x_724_; 
if (v_isShared_715_ == 0)
{
v___x_724_ = v___x_714_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_str_710_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_startPos_711_);
lean_ctor_set(v_reuseFailAlloc_725_, 2, v_stopPos_712_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
v___y_702_ = v___x_724_;
goto v___jp_701_;
}
}
}
}
v___jp_717_:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_719_ = l_panic___redArg(v___x_716_, v___x_718_);
v___y_702_ = v___x_719_;
goto v___jp_701_;
}
}
}
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
v___x_733_ = lean_panic_fn(v___x_732_, v_msg_731_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Substring_Raw_Internal_allImpl_spec__0(lean_object* v_p_734_, lean_object* v_s_735_, lean_object* v_curr_736_){
_start:
{
lean_object* v_str_737_; lean_object* v_startInclusive_738_; lean_object* v_endExclusive_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
v_str_737_ = lean_ctor_get(v_s_735_, 0);
v_startInclusive_738_ = lean_ctor_get(v_s_735_, 1);
v_endExclusive_739_ = lean_ctor_get(v_s_735_, 2);
v___x_740_ = lean_nat_add(v_startInclusive_738_, v_curr_736_);
lean_inc(v_endExclusive_739_);
lean_inc(v___x_740_);
lean_inc_ref(v_str_737_);
v___x_741_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_741_, 0, v_str_737_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
lean_ctor_set(v___x_741_, 2, v_endExclusive_739_);
v___x_742_ = lean_unsigned_to_nat(0u);
v___x_743_ = lean_nat_sub(v_endExclusive_739_, v___x_740_);
v___x_744_ = lean_nat_dec_eq(v___x_742_, v___x_743_);
lean_dec(v___x_743_);
if (v___x_744_ == 0)
{
uint32_t v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; uint8_t v___x_748_; 
v___x_745_ = lean_string_utf8_get_fast(v_str_737_, v___x_740_);
v___x_746_ = lean_box_uint32(v___x_745_);
lean_inc_ref(v_p_734_);
v___x_747_ = lean_apply_1(v_p_734_, v___x_746_);
v___x_748_ = lean_unbox(v___x_747_);
if (v___x_748_ == 0)
{
lean_dec(v___x_740_);
lean_dec(v_curr_736_);
lean_dec_ref(v_p_734_);
return v___x_741_;
}
else
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_749_ = lean_string_utf8_next_fast(v_str_737_, v___x_740_);
v___x_750_ = lean_nat_sub(v___x_749_, v___x_740_);
lean_dec(v___x_740_);
v___x_751_ = lean_nat_add(v_curr_736_, v___x_750_);
lean_dec(v___x_750_);
v___x_752_ = lean_nat_dec_lt(v_curr_736_, v___x_751_);
lean_dec(v_curr_736_);
if (v___x_752_ == 0)
{
lean_dec(v___x_751_);
lean_dec_ref(v_p_734_);
return v___x_741_;
}
else
{
lean_dec_ref(v___x_741_);
v_curr_736_ = v___x_751_;
goto _start;
}
}
}
else
{
lean_dec(v___x_740_);
lean_dec(v_curr_736_);
lean_dec_ref(v_p_734_);
return v___x_741_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Substring_Raw_Internal_allImpl_spec__0___boxed(lean_object* v_p_754_, lean_object* v_s_755_, lean_object* v_curr_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Substring_Raw_Internal_allImpl_spec__0(v_p_754_, v_s_755_, v_curr_756_);
lean_dec_ref(v_s_755_);
return v_res_757_;
}
}
LEAN_EXPORT uint8_t lean_substring_all(lean_object* v_s_758_, lean_object* v_p_759_){
_start:
{
lean_object* v___y_761_; lean_object* v_str_771_; lean_object* v_startPos_772_; lean_object* v_stopPos_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_783_; 
v_str_771_ = lean_ctor_get(v_s_758_, 0);
v_startPos_772_ = lean_ctor_get(v_s_758_, 1);
v_stopPos_773_ = lean_ctor_get(v_s_758_, 2);
v_isSharedCheck_783_ = !lean_is_exclusive(v_s_758_);
if (v_isSharedCheck_783_ == 0)
{
v___x_775_ = v_s_758_;
v_isShared_776_ = v_isSharedCheck_783_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_stopPos_773_);
lean_inc(v_startPos_772_);
lean_inc(v_str_771_);
lean_dec(v_s_758_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_783_;
goto v_resetjp_774_;
}
v___jp_760_:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v_startInclusive_764_; lean_object* v_endExclusive_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_762_ = lean_unsigned_to_nat(0u);
v___x_763_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Substring_Raw_Internal_allImpl_spec__0(v_p_759_, v___y_761_, v___x_762_);
lean_dec_ref(v___y_761_);
v_startInclusive_764_ = lean_ctor_get(v___x_763_, 1);
lean_inc(v_startInclusive_764_);
v_endExclusive_765_ = lean_ctor_get(v___x_763_, 2);
lean_inc(v_endExclusive_765_);
lean_dec_ref(v___x_763_);
v___x_766_ = lean_nat_sub(v_endExclusive_765_, v_startInclusive_764_);
lean_dec(v_startInclusive_764_);
lean_dec(v_endExclusive_765_);
v___x_767_ = lean_nat_dec_eq(v___x_766_, v___x_762_);
lean_dec(v___x_766_);
return v___x_767_;
}
v___jp_768_:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_770_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_769_);
v___y_761_ = v___x_770_;
goto v___jp_760_;
}
v_resetjp_774_:
{
uint8_t v___x_777_; 
v___x_777_ = lean_string_is_valid_pos(v_str_771_, v_startPos_772_);
if (v___x_777_ == 0)
{
lean_del_object(v___x_775_);
lean_dec(v_stopPos_773_);
lean_dec(v_startPos_772_);
lean_dec_ref(v_str_771_);
goto v___jp_768_;
}
else
{
uint8_t v___x_778_; 
v___x_778_ = lean_string_is_valid_pos(v_str_771_, v_stopPos_773_);
if (v___x_778_ == 0)
{
lean_del_object(v___x_775_);
lean_dec(v_stopPos_773_);
lean_dec(v_startPos_772_);
lean_dec_ref(v_str_771_);
goto v___jp_768_;
}
else
{
uint8_t v___x_779_; 
v___x_779_ = lean_nat_dec_le(v_startPos_772_, v_stopPos_773_);
if (v___x_779_ == 0)
{
lean_del_object(v___x_775_);
lean_dec(v_stopPos_773_);
lean_dec(v_startPos_772_);
lean_dec_ref(v_str_771_);
goto v___jp_768_;
}
else
{
lean_object* v___x_781_; 
if (v_isShared_776_ == 0)
{
v___x_781_ = v___x_775_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_str_771_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_startPos_772_);
lean_ctor_set(v_reuseFailAlloc_782_, 2, v_stopPos_773_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
v___y_761_ = v___x_781_;
goto v___jp_760_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_allImpl___boxed(lean_object* v_s_784_, lean_object* v_p_785_){
_start:
{
uint8_t v_res_786_; lean_object* v_r_787_; 
v_res_786_ = lean_substring_all(v_s_784_, v_p_785_);
v_r_787_ = lean_box(v_res_786_);
return v_r_787_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_contains___lam__0(uint32_t v_c_788_, uint32_t v_a_789_){
_start:
{
uint8_t v___x_790_; 
v___x_790_ = lean_uint32_dec_eq(v_a_789_, v_c_788_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_contains___lam__0___boxed(lean_object* v_c_791_, lean_object* v_a_792_){
_start:
{
uint32_t v_c_boxed_793_; uint32_t v_a_boxed_794_; uint8_t v_res_795_; lean_object* v_r_796_; 
v_c_boxed_793_ = lean_unbox_uint32(v_c_791_);
lean_dec(v_c_791_);
v_a_boxed_794_ = lean_unbox_uint32(v_a_792_);
lean_dec(v_a_792_);
v_res_795_ = l_Substring_Raw_contains___lam__0(v_c_boxed_793_, v_a_boxed_794_);
v_r_796_ = lean_box(v_res_795_);
return v_r_796_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_contains(lean_object* v_s_797_, uint32_t v_c_798_){
_start:
{
lean_object* v___x_799_; lean_object* v___f_800_; lean_object* v___x_801_; lean_object* v_str_802_; lean_object* v_startPos_803_; lean_object* v_stopPos_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_822_; 
v___x_799_ = lean_box_uint32(v_c_798_);
v___f_800_ = lean_alloc_closure((void*)(l_Substring_Raw_contains___lam__0___boxed), 2, 1);
lean_closure_set(v___f_800_, 0, v___x_799_);
lean_inc_ref(v___f_800_);
v___x_801_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___f_800_);
v_str_802_ = lean_ctor_get(v_s_797_, 0);
v_startPos_803_ = lean_ctor_get(v_s_797_, 1);
v_stopPos_804_ = lean_ctor_get(v_s_797_, 2);
v_isSharedCheck_822_ = !lean_is_exclusive(v_s_797_);
if (v_isSharedCheck_822_ == 0)
{
v___x_806_ = v_s_797_;
v_isShared_807_ = v_isSharedCheck_822_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_stopPos_804_);
lean_inc(v_startPos_803_);
lean_inc(v_str_802_);
lean_dec(v_s_797_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_822_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_808_; lean_object* v___f_809_; lean_object* v___x_810_; uint8_t v___x_815_; 
v___x_808_ = l_String_instInhabitedSlice;
v___f_809_ = lean_alloc_closure((void*)(l_Substring_Raw_any___lam__0), 8, 1);
lean_closure_set(v___f_809_, 0, v___x_801_);
v___x_810_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_810_, 0, lean_box(0));
lean_closure_set(v___x_810_, 1, v___f_800_);
v___x_815_ = lean_string_is_valid_pos(v_str_802_, v_startPos_803_);
if (v___x_815_ == 0)
{
lean_del_object(v___x_806_);
lean_dec(v_stopPos_804_);
lean_dec(v_startPos_803_);
lean_dec_ref(v_str_802_);
goto v___jp_811_;
}
else
{
uint8_t v___x_816_; 
v___x_816_ = lean_string_is_valid_pos(v_str_802_, v_stopPos_804_);
if (v___x_816_ == 0)
{
lean_del_object(v___x_806_);
lean_dec(v_stopPos_804_);
lean_dec(v_startPos_803_);
lean_dec_ref(v_str_802_);
goto v___jp_811_;
}
else
{
uint8_t v___x_817_; 
v___x_817_ = lean_nat_dec_le(v_startPos_803_, v_stopPos_804_);
if (v___x_817_ == 0)
{
lean_del_object(v___x_806_);
lean_dec(v_stopPos_804_);
lean_dec(v_startPos_803_);
lean_dec_ref(v_str_802_);
goto v___jp_811_;
}
else
{
lean_object* v___x_819_; 
if (v_isShared_807_ == 0)
{
v___x_819_ = v___x_806_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_str_802_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_startPos_803_);
lean_ctor_set(v_reuseFailAlloc_821_, 2, v_stopPos_804_);
v___x_819_ = v_reuseFailAlloc_821_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
uint8_t v___x_820_; 
v___x_820_ = l_String_Slice_contains___redArg(v___f_809_, v___x_819_, v___x_810_);
return v___x_820_;
}
}
}
}
v___jp_811_:
{
lean_object* v___x_812_; lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_812_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_813_ = l_panic___redArg(v___x_808_, v___x_812_);
v___x_814_ = l_String_Slice_contains___redArg(v___f_809_, v___x_813_, v___x_810_);
return v___x_814_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_contains___boxed(lean_object* v_s_823_, lean_object* v_c_824_){
_start:
{
uint32_t v_c_boxed_825_; uint8_t v_res_826_; lean_object* v_r_827_; 
v_c_boxed_825_ = lean_unbox_uint32(v_c_824_);
lean_dec(v_c_824_);
v_res_826_ = l_Substring_Raw_contains(v_s_823_, v_c_boxed_825_);
v_r_827_ = lean_box(v_res_826_);
return v_r_827_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux(lean_object* v_s_828_, lean_object* v_stopPos_829_, lean_object* v_p_830_, lean_object* v_i_831_){
_start:
{
uint8_t v___x_832_; 
v___x_832_ = lean_nat_dec_lt(v_i_831_, v_stopPos_829_);
if (v___x_832_ == 0)
{
lean_dec_ref(v_p_830_);
return v_i_831_;
}
else
{
uint32_t v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_833_ = lean_string_utf8_get(v_s_828_, v_i_831_);
v___x_834_ = lean_box_uint32(v___x_833_);
lean_inc_ref(v_p_830_);
v___x_835_ = lean_apply_1(v_p_830_, v___x_834_);
v___x_836_ = lean_unbox(v___x_835_);
if (v___x_836_ == 0)
{
lean_dec_ref(v_p_830_);
return v_i_831_;
}
else
{
lean_object* v___x_837_; 
v___x_837_ = lean_string_utf8_next(v_s_828_, v_i_831_);
lean_dec(v_i_831_);
v_i_831_ = v___x_837_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___boxed(lean_object* v_s_839_, lean_object* v_stopPos_840_, lean_object* v_p_841_, lean_object* v_i_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Substring_Raw_takeWhileAux(v_s_839_, v_stopPos_840_, v_p_841_, v_i_842_);
lean_dec(v_stopPos_840_);
lean_dec_ref(v_s_839_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhile(lean_object* v_x_844_, lean_object* v_x_845_){
_start:
{
lean_object* v_str_846_; lean_object* v_startPos_847_; lean_object* v_stopPos_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_856_; 
v_str_846_ = lean_ctor_get(v_x_844_, 0);
v_startPos_847_ = lean_ctor_get(v_x_844_, 1);
v_stopPos_848_ = lean_ctor_get(v_x_844_, 2);
v_isSharedCheck_856_ = !lean_is_exclusive(v_x_844_);
if (v_isSharedCheck_856_ == 0)
{
v___x_850_ = v_x_844_;
v_isShared_851_ = v_isSharedCheck_856_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_stopPos_848_);
lean_inc(v_startPos_847_);
lean_inc(v_str_846_);
lean_dec(v_x_844_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_856_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v_e_852_; lean_object* v___x_854_; 
lean_inc(v_startPos_847_);
v_e_852_ = l_Substring_Raw_takeWhileAux(v_str_846_, v_stopPos_848_, v_x_845_, v_startPos_847_);
lean_dec(v_stopPos_848_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 2, v_e_852_);
v___x_854_ = v___x_850_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_str_846_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_startPos_847_);
lean_ctor_set(v_reuseFailAlloc_855_, 2, v_e_852_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(lean_object* v_a_857_, lean_object* v_s_858_, lean_object* v_stopPos_859_, lean_object* v_i_860_){
_start:
{
uint8_t v___x_861_; 
v___x_861_ = lean_nat_dec_lt(v_i_860_, v_stopPos_859_);
if (v___x_861_ == 0)
{
lean_dec_ref(v_a_857_);
return v_i_860_;
}
else
{
uint32_t v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; uint8_t v___x_865_; 
v___x_862_ = lean_string_utf8_get(v_s_858_, v_i_860_);
v___x_863_ = lean_box_uint32(v___x_862_);
lean_inc_ref(v_a_857_);
v___x_864_ = lean_apply_1(v_a_857_, v___x_863_);
v___x_865_ = lean_unbox(v___x_864_);
if (v___x_865_ == 0)
{
lean_dec_ref(v_a_857_);
return v_i_860_;
}
else
{
lean_object* v___x_866_; 
v___x_866_ = lean_string_utf8_next(v_s_858_, v_i_860_);
lean_dec(v_i_860_);
v_i_860_ = v___x_866_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0___boxed(lean_object* v_a_868_, lean_object* v_s_869_, lean_object* v_stopPos_870_, lean_object* v_i_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(v_a_868_, v_s_869_, v_stopPos_870_, v_i_871_);
lean_dec(v_stopPos_870_);
lean_dec_ref(v_s_869_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* lean_substring_takewhile(lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v_str_875_; lean_object* v_startPos_876_; lean_object* v_stopPos_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_885_; 
v_str_875_ = lean_ctor_get(v_a_873_, 0);
v_startPos_876_ = lean_ctor_get(v_a_873_, 1);
v_stopPos_877_ = lean_ctor_get(v_a_873_, 2);
v_isSharedCheck_885_ = !lean_is_exclusive(v_a_873_);
if (v_isSharedCheck_885_ == 0)
{
v___x_879_ = v_a_873_;
v_isShared_880_ = v_isSharedCheck_885_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_stopPos_877_);
lean_inc(v_startPos_876_);
lean_inc(v_str_875_);
lean_dec(v_a_873_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_885_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v_e_881_; lean_object* v___x_883_; 
lean_inc(v_startPos_876_);
v_e_881_ = l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(v_a_874_, v_str_875_, v_stopPos_877_, v_startPos_876_);
lean_dec(v_stopPos_877_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 2, v_e_881_);
v___x_883_ = v___x_879_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_str_875_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v_startPos_876_);
lean_ctor_set(v_reuseFailAlloc_884_, 2, v_e_881_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropWhile(lean_object* v_x_886_, lean_object* v_x_887_){
_start:
{
lean_object* v_str_888_; lean_object* v_startPos_889_; lean_object* v_stopPos_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_898_; 
v_str_888_ = lean_ctor_get(v_x_886_, 0);
v_startPos_889_ = lean_ctor_get(v_x_886_, 1);
v_stopPos_890_ = lean_ctor_get(v_x_886_, 2);
v_isSharedCheck_898_ = !lean_is_exclusive(v_x_886_);
if (v_isSharedCheck_898_ == 0)
{
v___x_892_ = v_x_886_;
v_isShared_893_ = v_isSharedCheck_898_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_stopPos_890_);
lean_inc(v_startPos_889_);
lean_inc(v_str_888_);
lean_dec(v_x_886_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_898_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v_b_894_; lean_object* v___x_896_; 
v_b_894_ = l_Substring_Raw_takeWhileAux(v_str_888_, v_stopPos_890_, v_x_887_, v_startPos_889_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 1, v_b_894_);
v___x_896_ = v___x_892_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_str_888_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_b_894_);
lean_ctor_set(v_reuseFailAlloc_897_, 2, v_stopPos_890_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux(lean_object* v_s_899_, lean_object* v_begPos_900_, lean_object* v_p_901_, lean_object* v_i_902_){
_start:
{
uint8_t v___x_903_; 
v___x_903_ = lean_nat_dec_lt(v_begPos_900_, v_i_902_);
if (v___x_903_ == 0)
{
lean_dec_ref(v_p_901_);
return v_i_902_;
}
else
{
lean_object* v_i_x27_904_; uint32_t v_c_905_; lean_object* v___x_906_; lean_object* v___x_907_; uint8_t v___x_908_; 
v_i_x27_904_ = lean_string_utf8_prev(v_s_899_, v_i_902_);
v_c_905_ = lean_string_utf8_get(v_s_899_, v_i_x27_904_);
v___x_906_ = lean_box_uint32(v_c_905_);
lean_inc_ref(v_p_901_);
v___x_907_ = lean_apply_1(v_p_901_, v___x_906_);
v___x_908_ = lean_unbox(v___x_907_);
if (v___x_908_ == 0)
{
lean_dec(v_i_x27_904_);
lean_dec_ref(v_p_901_);
return v_i_902_;
}
else
{
lean_dec(v_i_902_);
v_i_902_ = v_i_x27_904_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux___boxed(lean_object* v_s_910_, lean_object* v_begPos_911_, lean_object* v_p_912_, lean_object* v_i_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Substring_Raw_takeRightWhileAux(v_s_910_, v_begPos_911_, v_p_912_, v_i_913_);
lean_dec(v_begPos_911_);
lean_dec_ref(v_s_910_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhile(lean_object* v_x_915_, lean_object* v_x_916_){
_start:
{
lean_object* v_str_917_; lean_object* v_startPos_918_; lean_object* v_stopPos_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_927_; 
v_str_917_ = lean_ctor_get(v_x_915_, 0);
v_startPos_918_ = lean_ctor_get(v_x_915_, 1);
v_stopPos_919_ = lean_ctor_get(v_x_915_, 2);
v_isSharedCheck_927_ = !lean_is_exclusive(v_x_915_);
if (v_isSharedCheck_927_ == 0)
{
v___x_921_ = v_x_915_;
v_isShared_922_ = v_isSharedCheck_927_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_stopPos_919_);
lean_inc(v_startPos_918_);
lean_inc(v_str_917_);
lean_dec(v_x_915_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_927_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v_b_923_; lean_object* v___x_925_; 
lean_inc(v_stopPos_919_);
v_b_923_ = l_Substring_Raw_takeRightWhileAux(v_str_917_, v_startPos_918_, v_x_916_, v_stopPos_919_);
lean_dec(v_startPos_918_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 1, v_b_923_);
v___x_925_ = v___x_921_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_str_917_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v_b_923_);
lean_ctor_set(v_reuseFailAlloc_926_, 2, v_stopPos_919_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropRightWhile(lean_object* v_x_928_, lean_object* v_x_929_){
_start:
{
lean_object* v_str_930_; lean_object* v_startPos_931_; lean_object* v_stopPos_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_940_; 
v_str_930_ = lean_ctor_get(v_x_928_, 0);
v_startPos_931_ = lean_ctor_get(v_x_928_, 1);
v_stopPos_932_ = lean_ctor_get(v_x_928_, 2);
v_isSharedCheck_940_ = !lean_is_exclusive(v_x_928_);
if (v_isSharedCheck_940_ == 0)
{
v___x_934_ = v_x_928_;
v_isShared_935_ = v_isSharedCheck_940_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_stopPos_932_);
lean_inc(v_startPos_931_);
lean_inc(v_str_930_);
lean_dec(v_x_928_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_940_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v_e_936_; lean_object* v___x_938_; 
v_e_936_ = l_Substring_Raw_takeRightWhileAux(v_str_930_, v_startPos_931_, v_x_929_, v_stopPos_932_);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 2, v_e_936_);
v___x_938_ = v___x_934_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_str_930_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v_startPos_931_);
lean_ctor_set(v_reuseFailAlloc_939_, 2, v_e_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_trimLeft(lean_object* v_s_942_){
_start:
{
lean_object* v_str_943_; lean_object* v_startPos_944_; lean_object* v_stopPos_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_954_; 
v_str_943_ = lean_ctor_get(v_s_942_, 0);
v_startPos_944_ = lean_ctor_get(v_s_942_, 1);
v_stopPos_945_ = lean_ctor_get(v_s_942_, 2);
v_isSharedCheck_954_ = !lean_is_exclusive(v_s_942_);
if (v_isSharedCheck_954_ == 0)
{
v___x_947_ = v_s_942_;
v_isShared_948_ = v_isSharedCheck_954_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_stopPos_945_);
lean_inc(v_startPos_944_);
lean_inc(v_str_943_);
lean_dec(v_s_942_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_954_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_949_; lean_object* v_b_950_; lean_object* v___x_952_; 
v___x_949_ = ((lean_object*)(l_Substring_Raw_trimLeft___closed__0));
v_b_950_ = l_Substring_Raw_takeWhileAux(v_str_943_, v_stopPos_945_, v___x_949_, v_startPos_944_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 1, v_b_950_);
v___x_952_ = v___x_947_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_str_943_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v_b_950_);
lean_ctor_set(v_reuseFailAlloc_953_, 2, v_stopPos_945_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_trimRight(lean_object* v_s_955_){
_start:
{
lean_object* v_str_956_; lean_object* v_startPos_957_; lean_object* v_stopPos_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_967_; 
v_str_956_ = lean_ctor_get(v_s_955_, 0);
v_startPos_957_ = lean_ctor_get(v_s_955_, 1);
v_stopPos_958_ = lean_ctor_get(v_s_955_, 2);
v_isSharedCheck_967_ = !lean_is_exclusive(v_s_955_);
if (v_isSharedCheck_967_ == 0)
{
v___x_960_ = v_s_955_;
v_isShared_961_ = v_isSharedCheck_967_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_stopPos_958_);
lean_inc(v_startPos_957_);
lean_inc(v_str_956_);
lean_dec(v_s_955_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_967_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_962_; lean_object* v_e_963_; lean_object* v___x_965_; 
v___x_962_ = ((lean_object*)(l_Substring_Raw_trimLeft___closed__0));
v_e_963_ = l_Substring_Raw_takeRightWhileAux(v_str_956_, v_startPos_957_, v___x_962_, v_stopPos_958_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 2, v_e_963_);
v___x_965_ = v___x_960_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_str_956_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_startPos_957_);
lean_ctor_set(v_reuseFailAlloc_966_, 2, v_e_963_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_trim(lean_object* v_x_968_){
_start:
{
lean_object* v_str_969_; lean_object* v_startPos_970_; lean_object* v_stopPos_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_981_; 
v_str_969_ = lean_ctor_get(v_x_968_, 0);
v_startPos_970_ = lean_ctor_get(v_x_968_, 1);
v_stopPos_971_ = lean_ctor_get(v_x_968_, 2);
v_isSharedCheck_981_ = !lean_is_exclusive(v_x_968_);
if (v_isSharedCheck_981_ == 0)
{
v___x_973_ = v_x_968_;
v_isShared_974_ = v_isSharedCheck_981_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_stopPos_971_);
lean_inc(v_startPos_970_);
lean_inc(v_str_969_);
lean_dec(v_x_968_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_981_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_975_; lean_object* v_b_976_; lean_object* v_e_977_; lean_object* v___x_979_; 
v___x_975_ = ((lean_object*)(l_Substring_Raw_trimLeft___closed__0));
v_b_976_ = l_Substring_Raw_takeWhileAux(v_str_969_, v_stopPos_971_, v___x_975_, v_startPos_970_);
v_e_977_ = l_Substring_Raw_takeRightWhileAux(v_str_969_, v_b_976_, v___x_975_, v_stopPos_971_);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 2, v_e_977_);
lean_ctor_set(v___x_973_, 1, v_b_976_);
v___x_979_ = v___x_973_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_str_969_);
lean_ctor_set(v_reuseFailAlloc_980_, 1, v_b_976_);
lean_ctor_set(v_reuseFailAlloc_980_, 2, v_e_977_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___lam__0(lean_object* v___y_982_, uint8_t v___x_983_, uint8_t v___x_984_, lean_object* v_it_985_, lean_object* v_acc_986_, lean_object* v_hP_987_, lean_object* v_recur_988_){
_start:
{
lean_object* v_str_989_; lean_object* v_startInclusive_990_; lean_object* v_endExclusive_991_; lean_object* v___x_992_; uint8_t v___x_993_; 
v_str_989_ = lean_ctor_get(v___y_982_, 0);
v_startInclusive_990_ = lean_ctor_get(v___y_982_, 1);
v_endExclusive_991_ = lean_ctor_get(v___y_982_, 2);
v___x_992_ = lean_nat_sub(v_endExclusive_991_, v_startInclusive_990_);
v___x_993_ = lean_nat_dec_eq(v_it_985_, v___x_992_);
lean_dec(v___x_992_);
if (v___x_993_ == 0)
{
lean_object* v_snd_994_; lean_object* v_snd_995_; lean_object* v_fst_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1057_; 
v_snd_994_ = lean_ctor_get(v_acc_986_, 1);
lean_inc(v_snd_994_);
v_snd_995_ = lean_ctor_get(v_snd_994_, 1);
lean_inc(v_snd_995_);
v_fst_996_ = lean_ctor_get(v_acc_986_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_acc_986_);
if (v_isSharedCheck_1057_ == 0)
{
lean_object* v_unused_1058_; 
v_unused_1058_ = lean_ctor_get(v_acc_986_, 1);
lean_dec(v_unused_1058_);
v___x_998_ = v_acc_986_;
v_isShared_999_ = v_isSharedCheck_1057_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_fst_996_);
lean_dec(v_acc_986_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1057_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v_fst_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1055_; 
v_fst_1000_ = lean_ctor_get(v_snd_994_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v_snd_994_);
if (v_isSharedCheck_1055_ == 0)
{
lean_object* v_unused_1056_; 
v_unused_1056_ = lean_ctor_get(v_snd_994_, 1);
lean_dec(v_unused_1056_);
v___x_1002_ = v_snd_994_;
v_isShared_1003_ = v_isSharedCheck_1055_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_fst_1000_);
lean_dec(v_snd_994_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1055_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v_snd_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1053_; 
v_snd_1004_ = lean_ctor_get(v_snd_995_, 1);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_snd_995_);
if (v_isSharedCheck_1053_ == 0)
{
lean_object* v_unused_1054_; 
v_unused_1054_ = lean_ctor_get(v_snd_995_, 0);
lean_dec(v_unused_1054_);
v___x_1006_ = v_snd_995_;
v_isShared_1007_ = v_isSharedCheck_1053_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_snd_1004_);
lean_dec(v_snd_995_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1053_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; uint32_t v___x_1011_; uint8_t v___y_1013_; uint8_t v___y_1014_; uint8_t v___y_1032_; uint8_t v___y_1033_; uint8_t v___y_1038_; uint8_t v___y_1039_; uint8_t v___y_1044_; uint32_t v___x_1049_; uint8_t v___x_1050_; 
v___x_1008_ = lean_nat_add(v_startInclusive_990_, v_it_985_);
v___x_1009_ = lean_string_utf8_next_fast(v_str_989_, v___x_1008_);
v___x_1010_ = lean_nat_sub(v___x_1009_, v_startInclusive_990_);
v___x_1011_ = lean_string_utf8_get_fast(v_str_989_, v___x_1008_);
lean_dec(v___x_1008_);
v___x_1049_ = 48;
v___x_1050_ = lean_uint32_dec_le(v___x_1049_, v___x_1011_);
if (v___x_1050_ == 0)
{
v___y_1044_ = v___x_1050_;
goto v___jp_1043_;
}
else
{
uint32_t v___x_1051_; uint8_t v___x_1052_; 
v___x_1051_ = 57;
v___x_1052_ = lean_uint32_dec_le(v___x_1011_, v___x_1051_);
v___y_1044_ = v___x_1052_;
goto v___jp_1043_;
}
v___jp_1012_:
{
uint32_t v___x_1015_; uint8_t v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1020_; 
v___x_1015_ = 95;
v___x_1016_ = lean_uint32_dec_eq(v___x_1011_, v___x_1015_);
v___x_1017_ = lean_box(v___y_1013_);
v___x_1018_ = lean_box(v___y_1014_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 1, v___x_1018_);
lean_ctor_set(v___x_1006_, 0, v___x_1017_);
v___x_1020_ = v___x_1006_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1017_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v___x_1018_);
v___x_1020_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
lean_object* v___x_1021_; lean_object* v___x_1023_; 
v___x_1021_ = lean_box(v___x_1016_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 1, v___x_1020_);
lean_ctor_set(v___x_1002_, 0, v___x_1021_);
v___x_1023_ = v___x_1002_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1021_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v___x_1020_);
v___x_1023_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v___x_1024_; lean_object* v___x_1026_; 
v___x_1024_ = lean_box(v___x_983_);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 1, v___x_1023_);
lean_ctor_set(v___x_998_, 0, v___x_1024_);
v___x_1026_ = v___x_998_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1024_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v___x_1023_);
v___x_1026_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1027_; 
v___x_1027_ = lean_apply_4(v_recur_988_, v___x_1010_, v___x_1026_, lean_box(0), lean_box(0));
return v___x_1027_;
}
}
}
}
v___jp_1031_:
{
uint8_t v___x_1034_; 
v___x_1034_ = lean_unbox(v_fst_1000_);
lean_dec(v_fst_1000_);
if (v___x_1034_ == 0)
{
v___y_1013_ = v___y_1032_;
v___y_1014_ = v___y_1033_;
goto v___jp_1012_;
}
else
{
uint32_t v___x_1035_; uint8_t v___x_1036_; 
v___x_1035_ = 95;
v___x_1036_ = lean_uint32_dec_eq(v___x_1011_, v___x_1035_);
if (v___x_1036_ == 0)
{
v___y_1013_ = v___y_1032_;
v___y_1014_ = v___y_1033_;
goto v___jp_1012_;
}
else
{
v___y_1013_ = v___y_1032_;
v___y_1014_ = v___x_983_;
goto v___jp_1012_;
}
}
}
v___jp_1037_:
{
uint8_t v___x_1040_; 
v___x_1040_ = lean_unbox(v_fst_996_);
lean_dec(v_fst_996_);
if (v___x_1040_ == 0)
{
v___y_1032_ = v___y_1038_;
v___y_1033_ = v___y_1039_;
goto v___jp_1031_;
}
else
{
uint32_t v___x_1041_; uint8_t v___x_1042_; 
v___x_1041_ = 95;
v___x_1042_ = lean_uint32_dec_eq(v___x_1011_, v___x_1041_);
if (v___x_1042_ == 0)
{
v___y_1032_ = v___y_1038_;
v___y_1033_ = v___y_1039_;
goto v___jp_1031_;
}
else
{
if (v___x_983_ == 0)
{
lean_dec(v_fst_1000_);
v___y_1013_ = v___y_1038_;
v___y_1014_ = v___x_983_;
goto v___jp_1012_;
}
else
{
v___y_1032_ = v___y_1038_;
v___y_1033_ = v___x_983_;
goto v___jp_1031_;
}
}
}
}
v___jp_1043_:
{
uint8_t v___x_1045_; 
v___x_1045_ = lean_unbox(v_snd_1004_);
if (v___x_1045_ == 0)
{
uint8_t v___x_1046_; 
lean_dec(v_fst_1000_);
lean_dec(v_fst_996_);
v___x_1046_ = lean_unbox(v_snd_1004_);
lean_dec(v_snd_1004_);
v___y_1013_ = v___y_1044_;
v___y_1014_ = v___x_1046_;
goto v___jp_1012_;
}
else
{
lean_dec(v_snd_1004_);
if (v___y_1044_ == 0)
{
uint32_t v___x_1047_; uint8_t v___x_1048_; 
v___x_1047_ = 95;
v___x_1048_ = lean_uint32_dec_eq(v___x_1011_, v___x_1047_);
if (v___x_1048_ == 0)
{
lean_dec(v_fst_1000_);
lean_dec(v_fst_996_);
v___y_1013_ = v___y_1044_;
v___y_1014_ = v___x_1048_;
goto v___jp_1012_;
}
else
{
v___y_1038_ = v___y_1044_;
v___y_1039_ = v___x_1048_;
goto v___jp_1037_;
}
}
else
{
v___y_1038_ = v___y_1044_;
v___y_1039_ = v___x_984_;
goto v___jp_1037_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_recur_988_);
return v_acc_986_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___lam__0___boxed(lean_object* v___y_1059_, lean_object* v___x_1060_, lean_object* v___x_1061_, lean_object* v_it_1062_, lean_object* v_acc_1063_, lean_object* v_hP_1064_, lean_object* v_recur_1065_){
_start:
{
uint8_t v___x_1061__boxed_1066_; uint8_t v___x_1062__boxed_1067_; lean_object* v_res_1068_; 
v___x_1061__boxed_1066_ = lean_unbox(v___x_1060_);
v___x_1062__boxed_1067_ = lean_unbox(v___x_1061_);
v_res_1068_ = l_Substring_Raw_isNat___lam__0(v___y_1059_, v___x_1061__boxed_1066_, v___x_1062__boxed_1067_, v_it_1062_, v_acc_1063_, v_hP_1064_, v_recur_1065_);
lean_dec(v_it_1062_);
lean_dec_ref(v___y_1059_);
return v_res_1068_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_isNat(lean_object* v_s_1069_){
_start:
{
lean_object* v_str_1070_; lean_object* v_startPos_1071_; lean_object* v_stopPos_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1111_; 
v_str_1070_ = lean_ctor_get(v_s_1069_, 0);
v_startPos_1071_ = lean_ctor_get(v_s_1069_, 1);
v_stopPos_1072_ = lean_ctor_get(v_s_1069_, 2);
v_isSharedCheck_1111_ = !lean_is_exclusive(v_s_1069_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1074_ = v_s_1069_;
v_isShared_1075_ = v_isSharedCheck_1111_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_stopPos_1072_);
lean_inc(v_startPos_1071_);
lean_inc(v_str_1070_);
lean_dec(v_s_1069_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1111_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; 
v___x_1076_ = lean_nat_sub(v_stopPos_1072_, v_startPos_1071_);
v___x_1077_ = lean_unsigned_to_nat(0u);
v___x_1078_ = lean_nat_dec_eq(v___x_1076_, v___x_1077_);
lean_dec(v___x_1076_);
if (v___x_1078_ == 0)
{
uint8_t v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___y_1088_; lean_object* v___x_1100_; uint8_t v___x_1104_; 
v___x_1079_ = 1;
v___x_1080_ = lean_box(v___x_1078_);
v___x_1081_ = lean_box(v___x_1079_);
v___x_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1080_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = lean_box(v___x_1078_);
v___x_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
lean_ctor_set(v___x_1084_, 1, v___x_1082_);
v___x_1085_ = lean_box(v___x_1079_);
v___x_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
lean_ctor_set(v___x_1086_, 1, v___x_1084_);
v___x_1100_ = l_String_instInhabitedSlice;
v___x_1104_ = lean_string_is_valid_pos(v_str_1070_, v_startPos_1071_);
if (v___x_1104_ == 0)
{
lean_del_object(v___x_1074_);
lean_dec(v_stopPos_1072_);
lean_dec(v_startPos_1071_);
lean_dec_ref(v_str_1070_);
goto v___jp_1101_;
}
else
{
uint8_t v___x_1105_; 
v___x_1105_ = lean_string_is_valid_pos(v_str_1070_, v_stopPos_1072_);
if (v___x_1105_ == 0)
{
lean_del_object(v___x_1074_);
lean_dec(v_stopPos_1072_);
lean_dec(v_startPos_1071_);
lean_dec_ref(v_str_1070_);
goto v___jp_1101_;
}
else
{
uint8_t v___x_1106_; 
v___x_1106_ = lean_nat_dec_le(v_startPos_1071_, v_stopPos_1072_);
if (v___x_1106_ == 0)
{
lean_del_object(v___x_1074_);
lean_dec(v_stopPos_1072_);
lean_dec(v_startPos_1071_);
lean_dec_ref(v_str_1070_);
goto v___jp_1101_;
}
else
{
lean_object* v___x_1108_; 
if (v_isShared_1075_ == 0)
{
v___x_1108_ = v___x_1074_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_str_1070_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v_startPos_1071_);
lean_ctor_set(v_reuseFailAlloc_1109_, 2, v_stopPos_1072_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
v___y_1088_ = v___x_1108_;
goto v___jp_1087_;
}
}
}
}
v___jp_1087_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___f_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v_snd_1094_; lean_object* v_snd_1095_; lean_object* v_snd_1096_; uint8_t v___x_1097_; 
v___x_1089_ = lean_box(v___x_1078_);
v___x_1090_ = lean_box(v___x_1079_);
lean_inc_ref(v___y_1088_);
v___f_1091_ = lean_alloc_closure((void*)(l_Substring_Raw_isNat___lam__0___boxed), 7, 3);
lean_closure_set(v___f_1091_, 0, v___y_1088_);
lean_closure_set(v___f_1091_, 1, v___x_1089_);
lean_closure_set(v___f_1091_, 2, v___x_1090_);
v___x_1092_ = l_String_Slice_positions(v___y_1088_);
lean_dec_ref(v___y_1088_);
v___x_1093_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1091_, v___x_1092_, v___x_1086_, lean_box(0));
v_snd_1094_ = lean_ctor_get(v___x_1093_, 1);
lean_inc(v_snd_1094_);
lean_dec(v___x_1093_);
v_snd_1095_ = lean_ctor_get(v_snd_1094_, 1);
lean_inc(v_snd_1095_);
lean_dec(v_snd_1094_);
v_snd_1096_ = lean_ctor_get(v_snd_1095_, 1);
v___x_1097_ = lean_unbox(v_snd_1096_);
if (v___x_1097_ == 0)
{
lean_dec(v_snd_1095_);
return v___x_1078_;
}
else
{
lean_object* v_fst_1098_; uint8_t v___x_1099_; 
v_fst_1098_ = lean_ctor_get(v_snd_1095_, 0);
lean_inc(v_fst_1098_);
lean_dec(v_snd_1095_);
v___x_1099_ = lean_unbox(v_fst_1098_);
lean_dec(v_fst_1098_);
return v___x_1099_;
}
}
v___jp_1101_:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_1103_ = l_panic___redArg(v___x_1100_, v___x_1102_);
v___y_1088_ = v___x_1103_;
goto v___jp_1087_;
}
}
else
{
uint8_t v___x_1110_; 
lean_del_object(v___x_1074_);
lean_dec(v_stopPos_1072_);
lean_dec(v_startPos_1071_);
lean_dec_ref(v_str_1070_);
v___x_1110_ = 0;
return v___x_1110_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___boxed(lean_object* v_s_1112_){
_start:
{
uint8_t v_res_1113_; lean_object* v_r_1114_; 
v_res_1113_ = l_Substring_Raw_isNat(v_s_1112_);
v_r_1114_ = lean_box(v_res_1113_);
return v_r_1114_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(lean_object* v___x_1115_, lean_object* v___y_1116_, lean_object* v_a_1117_, lean_object* v_b_1118_){
_start:
{
lean_object* v_str_1119_; lean_object* v_startInclusive_1120_; lean_object* v_endExclusive_1121_; lean_object* v___x_1122_; uint8_t v___x_1123_; 
v_str_1119_ = lean_ctor_get(v___y_1116_, 0);
v_startInclusive_1120_ = lean_ctor_get(v___y_1116_, 1);
v_endExclusive_1121_ = lean_ctor_get(v___y_1116_, 2);
v___x_1122_ = lean_nat_sub(v_endExclusive_1121_, v_startInclusive_1120_);
v___x_1123_ = lean_nat_dec_eq(v_a_1117_, v___x_1122_);
lean_dec(v___x_1122_);
if (v___x_1123_ == 0)
{
lean_object* v_snd_1124_; lean_object* v_snd_1125_; lean_object* v_fst_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1190_; 
v_snd_1124_ = lean_ctor_get(v_b_1118_, 1);
lean_inc(v_snd_1124_);
v_snd_1125_ = lean_ctor_get(v_snd_1124_, 1);
lean_inc(v_snd_1125_);
v_fst_1126_ = lean_ctor_get(v_b_1118_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v_b_1118_);
if (v_isSharedCheck_1190_ == 0)
{
lean_object* v_unused_1191_; 
v_unused_1191_ = lean_ctor_get(v_b_1118_, 1);
lean_dec(v_unused_1191_);
v___x_1128_ = v_b_1118_;
v_isShared_1129_ = v_isSharedCheck_1190_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_fst_1126_);
lean_dec(v_b_1118_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1190_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v_fst_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1188_; 
v_fst_1130_ = lean_ctor_get(v_snd_1124_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v_snd_1124_);
if (v_isSharedCheck_1188_ == 0)
{
lean_object* v_unused_1189_; 
v_unused_1189_ = lean_ctor_get(v_snd_1124_, 1);
lean_dec(v_unused_1189_);
v___x_1132_ = v_snd_1124_;
v_isShared_1133_ = v_isSharedCheck_1188_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_fst_1130_);
lean_dec(v_snd_1124_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1188_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v_snd_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1186_; 
v_snd_1134_ = lean_ctor_get(v_snd_1125_, 1);
v_isSharedCheck_1186_ = !lean_is_exclusive(v_snd_1125_);
if (v_isSharedCheck_1186_ == 0)
{
lean_object* v_unused_1187_; 
v_unused_1187_ = lean_ctor_get(v_snd_1125_, 0);
lean_dec(v_unused_1187_);
v___x_1136_ = v_snd_1125_;
v_isShared_1137_ = v_isSharedCheck_1186_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_snd_1134_);
lean_dec(v_snd_1125_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1186_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; uint8_t v___x_1139_; uint8_t v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; uint32_t v___x_1144_; uint8_t v___y_1146_; uint8_t v___y_1147_; uint8_t v___y_1165_; uint8_t v___y_1166_; uint8_t v___y_1171_; uint8_t v___y_1172_; uint8_t v___y_1177_; uint32_t v___x_1182_; uint8_t v___x_1183_; 
v___x_1138_ = lean_unsigned_to_nat(0u);
v___x_1139_ = lean_nat_dec_eq(v___x_1115_, v___x_1138_);
v___x_1140_ = 1;
v___x_1141_ = lean_nat_add(v_startInclusive_1120_, v_a_1117_);
lean_dec(v_a_1117_);
v___x_1142_ = lean_string_utf8_next_fast(v_str_1119_, v___x_1141_);
v___x_1143_ = lean_nat_sub(v___x_1142_, v_startInclusive_1120_);
v___x_1144_ = lean_string_utf8_get_fast(v_str_1119_, v___x_1141_);
lean_dec(v___x_1141_);
v___x_1182_ = 48;
v___x_1183_ = lean_uint32_dec_le(v___x_1182_, v___x_1144_);
if (v___x_1183_ == 0)
{
v___y_1177_ = v___x_1183_;
goto v___jp_1176_;
}
else
{
uint32_t v___x_1184_; uint8_t v___x_1185_; 
v___x_1184_ = 57;
v___x_1185_ = lean_uint32_dec_le(v___x_1144_, v___x_1184_);
v___y_1177_ = v___x_1185_;
goto v___jp_1176_;
}
v___jp_1145_:
{
uint32_t v___x_1148_; uint8_t v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1148_ = 95;
v___x_1149_ = lean_uint32_dec_eq(v___x_1144_, v___x_1148_);
v___x_1150_ = lean_box(v___y_1146_);
v___x_1151_ = lean_box(v___y_1147_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 1, v___x_1151_);
lean_ctor_set(v___x_1136_, 0, v___x_1150_);
v___x_1153_ = v___x_1136_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1150_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1154_; lean_object* v___x_1156_; 
v___x_1154_ = lean_box(v___x_1149_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 1, v___x_1153_);
lean_ctor_set(v___x_1132_, 0, v___x_1154_);
v___x_1156_ = v___x_1132_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1154_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v___x_1153_);
v___x_1156_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
lean_object* v___x_1157_; lean_object* v___x_1159_; 
v___x_1157_ = lean_box(v___x_1139_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 1, v___x_1156_);
lean_ctor_set(v___x_1128_, 0, v___x_1157_);
v___x_1159_ = v___x_1128_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1157_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v___x_1156_);
v___x_1159_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
v_a_1117_ = v___x_1143_;
v_b_1118_ = v___x_1159_;
goto _start;
}
}
}
}
v___jp_1164_:
{
uint8_t v___x_1167_; 
v___x_1167_ = lean_unbox(v_fst_1130_);
lean_dec(v_fst_1130_);
if (v___x_1167_ == 0)
{
v___y_1146_ = v___y_1165_;
v___y_1147_ = v___y_1166_;
goto v___jp_1145_;
}
else
{
uint32_t v___x_1168_; uint8_t v___x_1169_; 
v___x_1168_ = 95;
v___x_1169_ = lean_uint32_dec_eq(v___x_1144_, v___x_1168_);
if (v___x_1169_ == 0)
{
v___y_1146_ = v___y_1165_;
v___y_1147_ = v___y_1166_;
goto v___jp_1145_;
}
else
{
v___y_1146_ = v___y_1165_;
v___y_1147_ = v___x_1139_;
goto v___jp_1145_;
}
}
}
v___jp_1170_:
{
uint8_t v___x_1173_; 
v___x_1173_ = lean_unbox(v_fst_1126_);
lean_dec(v_fst_1126_);
if (v___x_1173_ == 0)
{
v___y_1165_ = v___y_1171_;
v___y_1166_ = v___y_1172_;
goto v___jp_1164_;
}
else
{
uint32_t v___x_1174_; uint8_t v___x_1175_; 
v___x_1174_ = 95;
v___x_1175_ = lean_uint32_dec_eq(v___x_1144_, v___x_1174_);
if (v___x_1175_ == 0)
{
v___y_1165_ = v___y_1171_;
v___y_1166_ = v___y_1172_;
goto v___jp_1164_;
}
else
{
if (v___x_1139_ == 0)
{
lean_dec(v_fst_1130_);
v___y_1146_ = v___y_1171_;
v___y_1147_ = v___x_1139_;
goto v___jp_1145_;
}
else
{
v___y_1165_ = v___y_1171_;
v___y_1166_ = v___x_1139_;
goto v___jp_1164_;
}
}
}
}
v___jp_1176_:
{
uint8_t v___x_1178_; 
v___x_1178_ = lean_unbox(v_snd_1134_);
if (v___x_1178_ == 0)
{
uint8_t v___x_1179_; 
lean_dec(v_fst_1130_);
lean_dec(v_fst_1126_);
v___x_1179_ = lean_unbox(v_snd_1134_);
lean_dec(v_snd_1134_);
v___y_1146_ = v___y_1177_;
v___y_1147_ = v___x_1179_;
goto v___jp_1145_;
}
else
{
lean_dec(v_snd_1134_);
if (v___y_1177_ == 0)
{
uint32_t v___x_1180_; uint8_t v___x_1181_; 
v___x_1180_ = 95;
v___x_1181_ = lean_uint32_dec_eq(v___x_1144_, v___x_1180_);
if (v___x_1181_ == 0)
{
lean_dec(v_fst_1130_);
lean_dec(v_fst_1126_);
v___y_1146_ = v___y_1177_;
v___y_1147_ = v___x_1181_;
goto v___jp_1145_;
}
else
{
v___y_1171_ = v___y_1177_;
v___y_1172_ = v___x_1181_;
goto v___jp_1170_;
}
}
else
{
v___y_1171_ = v___y_1177_;
v___y_1172_ = v___x_1140_;
goto v___jp_1170_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1117_);
return v_b_1118_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg___boxed(lean_object* v___x_1192_, lean_object* v___y_1193_, lean_object* v_a_1194_, lean_object* v_b_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(v___x_1192_, v___y_1193_, v_a_1194_, v_b_1195_);
lean_dec_ref(v___y_1193_);
lean_dec(v___x_1192_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(lean_object* v___y_1197_, lean_object* v_a_1198_, lean_object* v_b_1199_){
_start:
{
lean_object* v_str_1200_; lean_object* v_startInclusive_1201_; lean_object* v_endExclusive_1202_; lean_object* v___x_1203_; uint8_t v___x_1204_; 
v_str_1200_ = lean_ctor_get(v___y_1197_, 0);
v_startInclusive_1201_ = lean_ctor_get(v___y_1197_, 1);
v_endExclusive_1202_ = lean_ctor_get(v___y_1197_, 2);
v___x_1203_ = lean_nat_sub(v_endExclusive_1202_, v_startInclusive_1201_);
v___x_1204_ = lean_nat_dec_eq(v_a_1198_, v___x_1203_);
lean_dec(v___x_1203_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; uint32_t v___x_1208_; uint32_t v___x_1209_; uint8_t v___x_1210_; 
v___x_1205_ = lean_nat_add(v_startInclusive_1201_, v_a_1198_);
lean_dec(v_a_1198_);
v___x_1206_ = lean_string_utf8_next_fast(v_str_1200_, v___x_1205_);
v___x_1207_ = lean_nat_sub(v___x_1206_, v_startInclusive_1201_);
v___x_1208_ = lean_string_utf8_get_fast(v_str_1200_, v___x_1205_);
lean_dec(v___x_1205_);
v___x_1209_ = 95;
v___x_1210_ = lean_uint32_dec_eq(v___x_1208_, v___x_1209_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1211_ = lean_unsigned_to_nat(10u);
v___x_1212_ = lean_nat_mul(v_b_1199_, v___x_1211_);
lean_dec(v_b_1199_);
v___x_1213_ = lean_uint32_to_nat(v___x_1208_);
v___x_1214_ = lean_unsigned_to_nat(48u);
v___x_1215_ = lean_nat_sub(v___x_1213_, v___x_1214_);
lean_dec(v___x_1213_);
v___x_1216_ = lean_nat_add(v___x_1212_, v___x_1215_);
lean_dec(v___x_1215_);
lean_dec(v___x_1212_);
v_a_1198_ = v___x_1207_;
v_b_1199_ = v___x_1216_;
goto _start;
}
else
{
v_a_1198_ = v___x_1207_;
goto _start;
}
}
else
{
lean_dec(v_a_1198_);
return v_b_1199_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg___boxed(lean_object* v___y_1219_, lean_object* v_a_1220_, lean_object* v_b_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(v___y_1219_, v_a_1220_, v_b_1221_);
lean_dec_ref(v___y_1219_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toNat_x3f(lean_object* v_s_1223_){
_start:
{
lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1231_; lean_object* v_str_1234_; lean_object* v_startPos_1235_; lean_object* v_stopPos_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1279_; 
v_str_1234_ = lean_ctor_get(v_s_1223_, 0);
v_startPos_1235_ = lean_ctor_get(v_s_1223_, 1);
v_stopPos_1236_ = lean_ctor_get(v_s_1223_, 2);
v_isSharedCheck_1279_ = !lean_is_exclusive(v_s_1223_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1238_ = v_s_1223_;
v_isShared_1239_ = v_isSharedCheck_1279_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_stopPos_1236_);
lean_inc(v_startPos_1235_);
lean_inc(v_str_1234_);
lean_dec(v_s_1223_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1279_;
goto v_resetjp_1237_;
}
v___jp_1224_:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1227_ = l_String_Slice_positions(v___y_1226_);
v___x_1228_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(v___y_1226_, v___x_1227_, v___y_1225_);
lean_dec_ref(v___y_1226_);
v___x_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
return v___x_1229_;
}
v___jp_1230_:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_1233_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_1232_);
v___y_1225_ = v___y_1231_;
v___y_1226_ = v___x_1233_;
goto v___jp_1224_;
}
v_resetjp_1237_:
{
uint8_t v___y_1241_; lean_object* v___x_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1250_ = lean_nat_sub(v_stopPos_1236_, v_startPos_1235_);
v___x_1251_ = lean_unsigned_to_nat(0u);
v___x_1252_ = lean_nat_dec_eq(v___x_1250_, v___x_1251_);
if (v___x_1252_ == 0)
{
uint8_t v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___y_1262_; uint8_t v___x_1274_; 
v___x_1253_ = 1;
v___x_1254_ = lean_box(v___x_1252_);
v___x_1255_ = lean_box(v___x_1253_);
v___x_1256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1254_);
lean_ctor_set(v___x_1256_, 1, v___x_1255_);
v___x_1257_ = lean_box(v___x_1252_);
v___x_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
lean_ctor_set(v___x_1258_, 1, v___x_1256_);
v___x_1259_ = lean_box(v___x_1253_);
v___x_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
lean_ctor_set(v___x_1260_, 1, v___x_1258_);
v___x_1274_ = lean_string_is_valid_pos(v_str_1234_, v_startPos_1235_);
if (v___x_1274_ == 0)
{
goto v___jp_1271_;
}
else
{
uint8_t v___x_1275_; 
v___x_1275_ = lean_string_is_valid_pos(v_str_1234_, v_stopPos_1236_);
if (v___x_1275_ == 0)
{
goto v___jp_1271_;
}
else
{
uint8_t v___x_1276_; 
v___x_1276_ = lean_nat_dec_le(v_startPos_1235_, v_stopPos_1236_);
if (v___x_1276_ == 0)
{
goto v___jp_1271_;
}
else
{
lean_object* v___x_1277_; 
lean_inc(v_stopPos_1236_);
lean_inc(v_startPos_1235_);
lean_inc_ref(v_str_1234_);
v___x_1277_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1277_, 0, v_str_1234_);
lean_ctor_set(v___x_1277_, 1, v_startPos_1235_);
lean_ctor_set(v___x_1277_, 2, v_stopPos_1236_);
v___y_1262_ = v___x_1277_;
goto v___jp_1261_;
}
}
}
v___jp_1261_:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v_snd_1265_; lean_object* v_snd_1266_; lean_object* v_snd_1267_; uint8_t v___x_1268_; 
v___x_1263_ = l_String_Slice_positions(v___y_1262_);
v___x_1264_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(v___x_1250_, v___y_1262_, v___x_1263_, v___x_1260_);
lean_dec_ref(v___y_1262_);
lean_dec(v___x_1250_);
v_snd_1265_ = lean_ctor_get(v___x_1264_, 1);
lean_inc(v_snd_1265_);
lean_dec_ref(v___x_1264_);
v_snd_1266_ = lean_ctor_get(v_snd_1265_, 1);
lean_inc(v_snd_1266_);
lean_dec(v_snd_1265_);
v_snd_1267_ = lean_ctor_get(v_snd_1266_, 1);
v___x_1268_ = lean_unbox(v_snd_1267_);
if (v___x_1268_ == 0)
{
lean_dec(v_snd_1266_);
v___y_1241_ = v___x_1252_;
goto v___jp_1240_;
}
else
{
lean_object* v_fst_1269_; uint8_t v___x_1270_; 
v_fst_1269_ = lean_ctor_get(v_snd_1266_, 0);
lean_inc(v_fst_1269_);
lean_dec(v_snd_1266_);
v___x_1270_ = lean_unbox(v_fst_1269_);
lean_dec(v_fst_1269_);
v___y_1241_ = v___x_1270_;
goto v___jp_1240_;
}
}
v___jp_1271_:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_1273_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_1272_);
v___y_1262_ = v___x_1273_;
goto v___jp_1261_;
}
}
else
{
lean_object* v___x_1278_; 
lean_dec(v___x_1250_);
lean_del_object(v___x_1238_);
lean_dec(v_stopPos_1236_);
lean_dec(v_startPos_1235_);
lean_dec_ref(v_str_1234_);
v___x_1278_ = lean_box(0);
return v___x_1278_;
}
v___jp_1240_:
{
if (v___y_1241_ == 0)
{
lean_object* v___x_1242_; 
lean_del_object(v___x_1238_);
lean_dec(v_stopPos_1236_);
lean_dec(v_startPos_1235_);
lean_dec_ref(v_str_1234_);
v___x_1242_ = lean_box(0);
return v___x_1242_;
}
else
{
lean_object* v___x_1243_; uint8_t v___x_1244_; 
v___x_1243_ = lean_unsigned_to_nat(0u);
v___x_1244_ = lean_string_is_valid_pos(v_str_1234_, v_startPos_1235_);
if (v___x_1244_ == 0)
{
lean_del_object(v___x_1238_);
lean_dec(v_stopPos_1236_);
lean_dec(v_startPos_1235_);
lean_dec_ref(v_str_1234_);
v___y_1231_ = v___x_1243_;
goto v___jp_1230_;
}
else
{
uint8_t v___x_1245_; 
v___x_1245_ = lean_string_is_valid_pos(v_str_1234_, v_stopPos_1236_);
if (v___x_1245_ == 0)
{
lean_del_object(v___x_1238_);
lean_dec(v_stopPos_1236_);
lean_dec(v_startPos_1235_);
lean_dec_ref(v_str_1234_);
v___y_1231_ = v___x_1243_;
goto v___jp_1230_;
}
else
{
uint8_t v___x_1246_; 
v___x_1246_ = lean_nat_dec_le(v_startPos_1235_, v_stopPos_1236_);
if (v___x_1246_ == 0)
{
lean_del_object(v___x_1238_);
lean_dec(v_stopPos_1236_);
lean_dec(v_startPos_1235_);
lean_dec_ref(v_str_1234_);
v___y_1231_ = v___x_1243_;
goto v___jp_1230_;
}
else
{
lean_object* v___x_1248_; 
if (v_isShared_1239_ == 0)
{
v___x_1248_ = v___x_1238_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_str_1234_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v_startPos_1235_);
lean_ctor_set(v_reuseFailAlloc_1249_, 2, v_stopPos_1236_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
v___y_1225_ = v___x_1243_;
v___y_1226_ = v___x_1248_;
goto v___jp_1224_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0(lean_object* v___y_1280_, lean_object* v_inst_1281_, lean_object* v_R_1282_, lean_object* v_a_1283_, lean_object* v_b_1284_, lean_object* v_c_1285_){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(v___y_1280_, v_a_1283_, v_b_1284_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___boxed(lean_object* v___y_1287_, lean_object* v_inst_1288_, lean_object* v_R_1289_, lean_object* v_a_1290_, lean_object* v_b_1291_, lean_object* v_c_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0(v___y_1287_, v_inst_1288_, v_R_1289_, v_a_1290_, v_b_1291_, v_c_1292_);
lean_dec_ref(v___y_1287_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1(lean_object* v___x_1294_, lean_object* v___y_1295_, lean_object* v_inst_1296_, lean_object* v_R_1297_, lean_object* v_a_1298_, lean_object* v_b_1299_, lean_object* v_c_1300_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(v___x_1294_, v___y_1295_, v_a_1298_, v_b_1299_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___boxed(lean_object* v___x_1302_, lean_object* v___y_1303_, lean_object* v_inst_1304_, lean_object* v_R_1305_, lean_object* v_a_1306_, lean_object* v_b_1307_, lean_object* v_c_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1(v___x_1302_, v___y_1303_, v_inst_1304_, v_R_1305_, v_a_1306_, v_b_1307_, v_c_1308_);
lean_dec_ref(v___y_1303_);
lean_dec(v___x_1302_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_repair(lean_object* v_x_1310_){
_start:
{
lean_object* v_str_1311_; lean_object* v_startPos_1312_; lean_object* v_stopPos_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1329_; 
v_str_1311_ = lean_ctor_get(v_x_1310_, 0);
v_startPos_1312_ = lean_ctor_get(v_x_1310_, 1);
v_stopPos_1313_ = lean_ctor_get(v_x_1310_, 2);
v_isSharedCheck_1329_ = !lean_is_exclusive(v_x_1310_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1315_ = v_x_1310_;
v_isShared_1316_ = v_isSharedCheck_1329_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_stopPos_1313_);
lean_inc(v_startPos_1312_);
lean_inc(v_str_1311_);
lean_dec(v_x_1310_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1329_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___y_1318_; uint8_t v___x_1327_; 
v___x_1327_ = lean_string_is_valid_pos(v_str_1311_, v_startPos_1312_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; 
lean_dec(v_startPos_1312_);
v___x_1328_ = lean_string_utf8_byte_size(v_str_1311_);
v___y_1318_ = v___x_1328_;
goto v___jp_1317_;
}
else
{
v___y_1318_ = v_startPos_1312_;
goto v___jp_1317_;
}
v___jp_1317_:
{
uint8_t v___x_1319_; 
v___x_1319_ = lean_string_is_valid_pos(v_str_1311_, v_stopPos_1313_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; lean_object* v___x_1322_; 
lean_dec(v_stopPos_1313_);
v___x_1320_ = lean_string_utf8_byte_size(v_str_1311_);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 2, v___x_1320_);
lean_ctor_set(v___x_1315_, 1, v___y_1318_);
v___x_1322_ = v___x_1315_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_str_1311_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v___y_1318_);
lean_ctor_set(v_reuseFailAlloc_1323_, 2, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
else
{
lean_object* v___x_1325_; 
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 1, v___y_1318_);
v___x_1325_ = v___x_1315_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_str_1311_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v___y_1318_);
lean_ctor_set(v_reuseFailAlloc_1326_, 2, v_stopPos_1313_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_beq(lean_object* v_ss1_1330_, lean_object* v_ss2_1331_){
_start:
{
lean_object* v_ss1_1332_; lean_object* v_str_1333_; lean_object* v_startPos_1334_; lean_object* v_stopPos_1335_; lean_object* v_ss2_1336_; lean_object* v_str_1337_; lean_object* v_startPos_1338_; lean_object* v_stopPos_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; uint8_t v___x_1342_; 
v_ss1_1332_ = l_Substring_Raw_repair(v_ss1_1330_);
v_str_1333_ = lean_ctor_get(v_ss1_1332_, 0);
lean_inc_ref(v_str_1333_);
v_startPos_1334_ = lean_ctor_get(v_ss1_1332_, 1);
lean_inc(v_startPos_1334_);
v_stopPos_1335_ = lean_ctor_get(v_ss1_1332_, 2);
lean_inc(v_stopPos_1335_);
lean_dec_ref(v_ss1_1332_);
v_ss2_1336_ = l_Substring_Raw_repair(v_ss2_1331_);
v_str_1337_ = lean_ctor_get(v_ss2_1336_, 0);
lean_inc_ref(v_str_1337_);
v_startPos_1338_ = lean_ctor_get(v_ss2_1336_, 1);
lean_inc(v_startPos_1338_);
v_stopPos_1339_ = lean_ctor_get(v_ss2_1336_, 2);
lean_inc(v_stopPos_1339_);
lean_dec_ref(v_ss2_1336_);
v___x_1340_ = lean_nat_sub(v_stopPos_1335_, v_startPos_1334_);
lean_dec(v_stopPos_1335_);
v___x_1341_ = lean_nat_sub(v_stopPos_1339_, v_startPos_1338_);
lean_dec(v_stopPos_1339_);
v___x_1342_ = lean_nat_dec_eq(v___x_1340_, v___x_1341_);
lean_dec(v___x_1341_);
if (v___x_1342_ == 0)
{
lean_dec(v___x_1340_);
lean_dec(v_startPos_1338_);
lean_dec_ref(v_str_1337_);
lean_dec(v_startPos_1334_);
lean_dec_ref(v_str_1333_);
return v___x_1342_;
}
else
{
uint8_t v___x_1343_; 
v___x_1343_ = l_String_Pos_Raw_substrEq(v_str_1333_, v_startPos_1334_, v_str_1337_, v_startPos_1338_, v___x_1340_);
lean_dec(v___x_1340_);
lean_dec_ref(v_str_1337_);
lean_dec_ref(v_str_1333_);
return v___x_1343_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_beq___boxed(lean_object* v_ss1_1344_, lean_object* v_ss2_1345_){
_start:
{
uint8_t v_res_1346_; lean_object* v_r_1347_; 
v_res_1346_ = l_Substring_Raw_beq(v_ss1_1344_, v_ss2_1345_);
v_r_1347_ = lean_box(v_res_1346_);
return v_r_1347_;
}
}
LEAN_EXPORT uint8_t lean_substring_beq(lean_object* v_ss1_1348_, lean_object* v_ss2_1349_){
_start:
{
uint8_t v___x_1350_; 
v___x_1350_ = l_Substring_Raw_beq(v_ss1_1348_, v_ss2_1349_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_beqImpl___boxed(lean_object* v_ss1_1351_, lean_object* v_ss2_1352_){
_start:
{
uint8_t v_res_1353_; lean_object* v_r_1354_; 
v_res_1353_ = lean_substring_beq(v_ss1_1351_, v_ss2_1352_);
v_r_1354_ = lean_box(v_res_1353_);
return v_r_1354_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_sameAs(lean_object* v_ss1_1357_, lean_object* v_ss2_1358_){
_start:
{
lean_object* v_startPos_1359_; lean_object* v_startPos_1360_; uint8_t v___x_1361_; 
v_startPos_1359_ = lean_ctor_get(v_ss1_1357_, 1);
v_startPos_1360_ = lean_ctor_get(v_ss2_1358_, 1);
v___x_1361_ = lean_nat_dec_eq(v_startPos_1359_, v_startPos_1360_);
if (v___x_1361_ == 0)
{
lean_dec_ref(v_ss2_1358_);
lean_dec_ref(v_ss1_1357_);
return v___x_1361_;
}
else
{
uint8_t v___x_1362_; 
v___x_1362_ = l_Substring_Raw_beq(v_ss1_1357_, v_ss2_1358_);
return v___x_1362_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_sameAs___boxed(lean_object* v_ss1_1363_, lean_object* v_ss2_1364_){
_start:
{
uint8_t v_res_1365_; lean_object* v_r_1366_; 
v_res_1365_ = l_Substring_Raw_sameAs(v_ss1_1363_, v_ss2_1364_);
v_r_1366_ = lean_box(v_res_1365_);
return v_r_1366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(lean_object* v_s_1367_, lean_object* v_t_1368_, lean_object* v_spos_1369_, lean_object* v_tpos_1370_){
_start:
{
lean_object* v_str_1371_; lean_object* v_stopPos_1372_; uint8_t v___x_1373_; 
v_str_1371_ = lean_ctor_get(v_s_1367_, 0);
v_stopPos_1372_ = lean_ctor_get(v_s_1367_, 2);
v___x_1373_ = lean_nat_dec_lt(v_spos_1369_, v_stopPos_1372_);
if (v___x_1373_ == 0)
{
lean_dec(v_tpos_1370_);
return v_spos_1369_;
}
else
{
lean_object* v_str_1374_; lean_object* v_stopPos_1375_; uint8_t v___x_1376_; 
v_str_1374_ = lean_ctor_get(v_t_1368_, 0);
v_stopPos_1375_ = lean_ctor_get(v_t_1368_, 2);
v___x_1376_ = lean_nat_dec_lt(v_tpos_1370_, v_stopPos_1375_);
if (v___x_1376_ == 0)
{
lean_dec(v_tpos_1370_);
return v_spos_1369_;
}
else
{
uint32_t v___x_1377_; uint32_t v___x_1378_; uint8_t v___x_1379_; 
v___x_1377_ = lean_string_utf8_get(v_str_1371_, v_spos_1369_);
v___x_1378_ = lean_string_utf8_get(v_str_1374_, v_tpos_1370_);
v___x_1379_ = lean_uint32_dec_eq(v___x_1377_, v___x_1378_);
if (v___x_1379_ == 0)
{
lean_dec(v_tpos_1370_);
return v_spos_1369_;
}
else
{
lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1380_ = lean_string_utf8_next(v_str_1371_, v_spos_1369_);
lean_dec(v_spos_1369_);
v___x_1381_ = lean_string_utf8_next(v_str_1374_, v_tpos_1370_);
lean_dec(v_tpos_1370_);
v_spos_1369_ = v___x_1380_;
v_tpos_1370_ = v___x_1381_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop___boxed(lean_object* v_s_1383_, lean_object* v_t_1384_, lean_object* v_spos_1385_, lean_object* v_tpos_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(v_s_1383_, v_t_1384_, v_spos_1385_, v_tpos_1386_);
lean_dec_ref(v_t_1384_);
lean_dec_ref(v_s_1383_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_commonPrefix(lean_object* v_s_1388_, lean_object* v_t_1389_){
_start:
{
lean_object* v_str_1390_; lean_object* v_startPos_1391_; lean_object* v_startPos_1392_; lean_object* v___x_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
v_str_1390_ = lean_ctor_get(v_s_1388_, 0);
lean_inc_ref(v_str_1390_);
v_startPos_1391_ = lean_ctor_get(v_s_1388_, 1);
lean_inc(v_startPos_1391_);
v_startPos_1392_ = lean_ctor_get(v_t_1389_, 1);
lean_inc(v_startPos_1392_);
lean_inc(v_startPos_1391_);
v___x_1393_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(v_s_1388_, v_t_1389_, v_startPos_1391_, v_startPos_1392_);
lean_dec_ref(v_s_1388_);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_t_1389_);
if (v_isSharedCheck_1400_ == 0)
{
lean_object* v_unused_1401_; lean_object* v_unused_1402_; lean_object* v_unused_1403_; 
v_unused_1401_ = lean_ctor_get(v_t_1389_, 2);
lean_dec(v_unused_1401_);
v_unused_1402_ = lean_ctor_get(v_t_1389_, 1);
lean_dec(v_unused_1402_);
v_unused_1403_ = lean_ctor_get(v_t_1389_, 0);
lean_dec(v_unused_1403_);
v___x_1395_ = v_t_1389_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_dec(v_t_1389_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 2, v___x_1393_);
lean_ctor_set(v___x_1395_, 1, v_startPos_1391_);
lean_ctor_set(v___x_1395_, 0, v_str_1390_);
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_str_1390_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_startPos_1391_);
lean_ctor_set(v_reuseFailAlloc_1399_, 2, v___x_1393_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(lean_object* v_s_1404_, lean_object* v_t_1405_, lean_object* v_spos_1406_, lean_object* v_tpos_1407_){
_start:
{
lean_object* v_str_1408_; lean_object* v_startPos_1409_; uint8_t v___x_1410_; 
v_str_1408_ = lean_ctor_get(v_s_1404_, 0);
v_startPos_1409_ = lean_ctor_get(v_s_1404_, 1);
v___x_1410_ = lean_nat_dec_lt(v_startPos_1409_, v_spos_1406_);
if (v___x_1410_ == 0)
{
lean_dec(v_tpos_1407_);
return v_spos_1406_;
}
else
{
lean_object* v_str_1411_; lean_object* v_startPos_1412_; uint8_t v___x_1413_; 
v_str_1411_ = lean_ctor_get(v_t_1405_, 0);
v_startPos_1412_ = lean_ctor_get(v_t_1405_, 1);
v___x_1413_ = lean_nat_dec_lt(v_startPos_1412_, v_tpos_1407_);
if (v___x_1413_ == 0)
{
lean_dec(v_tpos_1407_);
return v_spos_1406_;
}
else
{
lean_object* v_spos_x27_1414_; lean_object* v_tpos_x27_1415_; uint32_t v___x_1416_; uint32_t v___x_1417_; uint8_t v___x_1418_; 
v_spos_x27_1414_ = lean_string_utf8_prev(v_str_1408_, v_spos_1406_);
v_tpos_x27_1415_ = lean_string_utf8_prev(v_str_1411_, v_tpos_1407_);
lean_dec(v_tpos_1407_);
v___x_1416_ = lean_string_utf8_get(v_str_1408_, v_spos_x27_1414_);
v___x_1417_ = lean_string_utf8_get(v_str_1411_, v_tpos_x27_1415_);
v___x_1418_ = lean_uint32_dec_eq(v___x_1416_, v___x_1417_);
if (v___x_1418_ == 0)
{
lean_dec(v_tpos_x27_1415_);
lean_dec(v_spos_x27_1414_);
return v_spos_1406_;
}
else
{
lean_dec(v_spos_1406_);
v_spos_1406_ = v_spos_x27_1414_;
v_tpos_1407_ = v_tpos_x27_1415_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop___boxed(lean_object* v_s_1420_, lean_object* v_t_1421_, lean_object* v_spos_1422_, lean_object* v_tpos_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(v_s_1420_, v_t_1421_, v_spos_1422_, v_tpos_1423_);
lean_dec_ref(v_t_1421_);
lean_dec_ref(v_s_1420_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_commonSuffix(lean_object* v_s_1425_, lean_object* v_t_1426_){
_start:
{
lean_object* v_str_1427_; lean_object* v_stopPos_1428_; lean_object* v_stopPos_1429_; lean_object* v___x_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
v_str_1427_ = lean_ctor_get(v_s_1425_, 0);
lean_inc_ref(v_str_1427_);
v_stopPos_1428_ = lean_ctor_get(v_s_1425_, 2);
lean_inc(v_stopPos_1428_);
v_stopPos_1429_ = lean_ctor_get(v_t_1426_, 2);
lean_inc(v_stopPos_1429_);
lean_inc(v_stopPos_1428_);
v___x_1430_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(v_s_1425_, v_t_1426_, v_stopPos_1428_, v_stopPos_1429_);
lean_dec_ref(v_s_1425_);
v_isSharedCheck_1437_ = !lean_is_exclusive(v_t_1426_);
if (v_isSharedCheck_1437_ == 0)
{
lean_object* v_unused_1438_; lean_object* v_unused_1439_; lean_object* v_unused_1440_; 
v_unused_1438_ = lean_ctor_get(v_t_1426_, 2);
lean_dec(v_unused_1438_);
v_unused_1439_ = lean_ctor_get(v_t_1426_, 1);
lean_dec(v_unused_1439_);
v_unused_1440_ = lean_ctor_get(v_t_1426_, 0);
lean_dec(v_unused_1440_);
v___x_1432_ = v_t_1426_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_dec(v_t_1426_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 2, v_stopPos_1428_);
lean_ctor_set(v___x_1432_, 1, v___x_1430_);
lean_ctor_set(v___x_1432_, 0, v_str_1427_);
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_str_1427_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v___x_1430_);
lean_ctor_set(v_reuseFailAlloc_1436_, 2, v_stopPos_1428_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropPrefix_x3f(lean_object* v_s_1441_, lean_object* v_pre_1442_){
_start:
{
lean_object* v_t_1443_; lean_object* v_startPos_1444_; lean_object* v_stopPos_1445_; lean_object* v_startPos_1446_; lean_object* v_stopPos_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; uint8_t v___x_1450_; 
lean_inc_ref(v_pre_1442_);
lean_inc_ref(v_s_1441_);
v_t_1443_ = l_Substring_Raw_commonPrefix(v_s_1441_, v_pre_1442_);
v_startPos_1444_ = lean_ctor_get(v_t_1443_, 1);
lean_inc(v_startPos_1444_);
v_stopPos_1445_ = lean_ctor_get(v_t_1443_, 2);
lean_inc(v_stopPos_1445_);
lean_dec_ref(v_t_1443_);
v_startPos_1446_ = lean_ctor_get(v_pre_1442_, 1);
lean_inc(v_startPos_1446_);
v_stopPos_1447_ = lean_ctor_get(v_pre_1442_, 2);
lean_inc(v_stopPos_1447_);
lean_dec_ref(v_pre_1442_);
v___x_1448_ = lean_nat_sub(v_stopPos_1445_, v_startPos_1444_);
lean_dec(v_startPos_1444_);
v___x_1449_ = lean_nat_sub(v_stopPos_1447_, v_startPos_1446_);
lean_dec(v_startPos_1446_);
lean_dec(v_stopPos_1447_);
v___x_1450_ = lean_nat_dec_eq(v___x_1448_, v___x_1449_);
lean_dec(v___x_1449_);
lean_dec(v___x_1448_);
if (v___x_1450_ == 0)
{
lean_object* v___x_1451_; 
lean_dec(v_stopPos_1445_);
lean_dec_ref(v_s_1441_);
v___x_1451_ = lean_box(0);
return v___x_1451_;
}
else
{
lean_object* v_str_1452_; lean_object* v_stopPos_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1461_; 
v_str_1452_ = lean_ctor_get(v_s_1441_, 0);
v_stopPos_1453_ = lean_ctor_get(v_s_1441_, 2);
v_isSharedCheck_1461_ = !lean_is_exclusive(v_s_1441_);
if (v_isSharedCheck_1461_ == 0)
{
lean_object* v_unused_1462_; 
v_unused_1462_ = lean_ctor_get(v_s_1441_, 1);
lean_dec(v_unused_1462_);
v___x_1455_ = v_s_1441_;
v_isShared_1456_ = v_isSharedCheck_1461_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_stopPos_1453_);
lean_inc(v_str_1452_);
lean_dec(v_s_1441_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1461_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1458_; 
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 1, v_stopPos_1445_);
v___x_1458_ = v___x_1455_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_str_1452_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v_stopPos_1445_);
lean_ctor_set(v_reuseFailAlloc_1460_, 2, v_stopPos_1453_);
v___x_1458_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
lean_object* v___x_1459_; 
v___x_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
return v___x_1459_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropSuffix_x3f(lean_object* v_s_1463_, lean_object* v_suff_1464_){
_start:
{
lean_object* v_t_1465_; lean_object* v_startPos_1466_; lean_object* v_stopPos_1467_; lean_object* v_startPos_1468_; lean_object* v_stopPos_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; uint8_t v___x_1472_; 
lean_inc_ref(v_suff_1464_);
lean_inc_ref(v_s_1463_);
v_t_1465_ = l_Substring_Raw_commonSuffix(v_s_1463_, v_suff_1464_);
v_startPos_1466_ = lean_ctor_get(v_t_1465_, 1);
lean_inc(v_startPos_1466_);
v_stopPos_1467_ = lean_ctor_get(v_t_1465_, 2);
lean_inc(v_stopPos_1467_);
lean_dec_ref(v_t_1465_);
v_startPos_1468_ = lean_ctor_get(v_suff_1464_, 1);
lean_inc(v_startPos_1468_);
v_stopPos_1469_ = lean_ctor_get(v_suff_1464_, 2);
lean_inc(v_stopPos_1469_);
lean_dec_ref(v_suff_1464_);
v___x_1470_ = lean_nat_sub(v_stopPos_1467_, v_startPos_1466_);
lean_dec(v_stopPos_1467_);
v___x_1471_ = lean_nat_sub(v_stopPos_1469_, v_startPos_1468_);
lean_dec(v_startPos_1468_);
lean_dec(v_stopPos_1469_);
v___x_1472_ = lean_nat_dec_eq(v___x_1470_, v___x_1471_);
lean_dec(v___x_1471_);
lean_dec(v___x_1470_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1473_; 
lean_dec(v_startPos_1466_);
lean_dec_ref(v_s_1463_);
v___x_1473_ = lean_box(0);
return v___x_1473_;
}
else
{
lean_object* v_str_1474_; lean_object* v_startPos_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1483_; 
v_str_1474_ = lean_ctor_get(v_s_1463_, 0);
v_startPos_1475_ = lean_ctor_get(v_s_1463_, 1);
v_isSharedCheck_1483_ = !lean_is_exclusive(v_s_1463_);
if (v_isSharedCheck_1483_ == 0)
{
lean_object* v_unused_1484_; 
v_unused_1484_ = lean_ctor_get(v_s_1463_, 2);
lean_dec(v_unused_1484_);
v___x_1477_ = v_s_1463_;
v_isShared_1478_ = v_isSharedCheck_1483_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_startPos_1475_);
lean_inc(v_str_1474_);
lean_dec(v_s_1463_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1483_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 2, v_startPos_1466_);
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_str_1474_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v_startPos_1475_);
lean_ctor_set(v_reuseFailAlloc_1482_, 2, v_startPos_1466_);
v___x_1480_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
lean_object* v___x_1481_; 
v___x_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
return v___x_1481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg(lean_object* v_x_1485_, lean_object* v_x_1486_, lean_object* v_x_1487_, lean_object* v_h__1_1488_, lean_object* v_h__2_1489_){
_start:
{
lean_object* v_zero_1490_; uint8_t v_isZero_1491_; 
v_zero_1490_ = lean_unsigned_to_nat(0u);
v_isZero_1491_ = lean_nat_dec_eq(v_x_1486_, v_zero_1490_);
if (v_isZero_1491_ == 1)
{
lean_object* v___x_1492_; 
lean_dec(v_h__2_1489_);
v___x_1492_ = lean_apply_2(v_h__1_1488_, v_x_1485_, v_x_1487_);
return v___x_1492_;
}
else
{
lean_object* v_one_1493_; lean_object* v_n_1494_; lean_object* v___x_1495_; 
lean_dec(v_h__1_1488_);
v_one_1493_ = lean_unsigned_to_nat(1u);
v_n_1494_ = lean_nat_sub(v_x_1486_, v_one_1493_);
v___x_1495_ = lean_apply_3(v_h__2_1489_, v_x_1485_, v_n_1494_, v_x_1487_);
return v___x_1495_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg___boxed(lean_object* v_x_1496_, lean_object* v_x_1497_, lean_object* v_x_1498_, lean_object* v_h__1_1499_, lean_object* v_h__2_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg(v_x_1496_, v_x_1497_, v_x_1498_, v_h__1_1499_, v_h__2_1500_);
lean_dec(v_x_1497_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter(lean_object* v_motive_1502_, lean_object* v_x_1503_, lean_object* v_x_1504_, lean_object* v_x_1505_, lean_object* v_h__1_1506_, lean_object* v_h__2_1507_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg(v_x_1503_, v_x_1504_, v_x_1505_, v_h__1_1506_, v_h__2_1507_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___boxed(lean_object* v_motive_1509_, lean_object* v_x_1510_, lean_object* v_x_1511_, lean_object* v_x_1512_, lean_object* v_h__1_1513_, lean_object* v_h__2_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter(v_motive_1509_, v_x_1510_, v_x_1511_, v_x_1512_, v_h__1_1513_, v_h__2_1514_);
lean_dec(v_x_1511_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Substring_bsize(lean_object* v_a_1516_){
_start:
{
lean_object* v_startPos_1517_; lean_object* v_stopPos_1518_; lean_object* v___x_1519_; 
v_startPos_1517_ = lean_ctor_get(v_a_1516_, 1);
v_stopPos_1518_ = lean_ctor_get(v_a_1516_, 2);
v___x_1519_ = lean_nat_sub(v_stopPos_1518_, v_startPos_1517_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Substring_bsize___boxed(lean_object* v_a_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Substring_bsize(v_a_1520_);
lean_dec_ref(v_a_1520_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Substring_toString(lean_object* v_a_1522_){
_start:
{
lean_object* v_str_1523_; lean_object* v_startPos_1524_; lean_object* v_stopPos_1525_; lean_object* v___x_1526_; 
v_str_1523_ = lean_ctor_get(v_a_1522_, 0);
v_startPos_1524_ = lean_ctor_get(v_a_1522_, 1);
v_stopPos_1525_ = lean_ctor_get(v_a_1522_, 2);
v___x_1526_ = lean_string_utf8_extract(v_str_1523_, v_startPos_1524_, v_stopPos_1525_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Substring_toString___boxed(lean_object* v_a_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Substring_toString(v_a_1527_);
lean_dec_ref(v_a_1527_);
return v_res_1528_;
}
}
LEAN_EXPORT uint8_t l_Substring_isEmpty(lean_object* v_ss_1529_){
_start:
{
lean_object* v_startPos_1530_; lean_object* v_stopPos_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; uint8_t v___x_1534_; 
v_startPos_1530_ = lean_ctor_get(v_ss_1529_, 1);
v_stopPos_1531_ = lean_ctor_get(v_ss_1529_, 2);
v___x_1532_ = lean_nat_sub(v_stopPos_1531_, v_startPos_1530_);
v___x_1533_ = lean_unsigned_to_nat(0u);
v___x_1534_ = lean_nat_dec_eq(v___x_1532_, v___x_1533_);
lean_dec(v___x_1532_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Substring_isEmpty___boxed(lean_object* v_ss_1535_){
_start:
{
uint8_t v_res_1536_; lean_object* v_r_1537_; 
v_res_1536_ = l_Substring_isEmpty(v_ss_1535_);
lean_dec_ref(v_ss_1535_);
v_r_1537_ = lean_box(v_res_1536_);
return v_r_1537_;
}
}
LEAN_EXPORT lean_object* l_Substring_next(lean_object* v_a_1538_, lean_object* v_a_1539_){
_start:
{
lean_object* v_str_1540_; lean_object* v_startPos_1541_; lean_object* v_stopPos_1542_; lean_object* v_absP_1543_; uint8_t v___x_1544_; 
v_str_1540_ = lean_ctor_get(v_a_1538_, 0);
v_startPos_1541_ = lean_ctor_get(v_a_1538_, 1);
v_stopPos_1542_ = lean_ctor_get(v_a_1538_, 2);
v_absP_1543_ = lean_nat_add(v_startPos_1541_, v_a_1539_);
v___x_1544_ = lean_nat_dec_eq(v_absP_1543_, v_stopPos_1542_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1545_ = lean_string_utf8_next(v_str_1540_, v_absP_1543_);
lean_dec(v_absP_1543_);
v___x_1546_ = lean_nat_sub(v___x_1545_, v_startPos_1541_);
lean_dec(v___x_1545_);
return v___x_1546_;
}
else
{
lean_dec(v_absP_1543_);
lean_inc(v_a_1539_);
return v_a_1539_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_next___boxed(lean_object* v_a_1547_, lean_object* v_a_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Substring_next(v_a_1547_, v_a_1548_);
lean_dec(v_a_1548_);
lean_dec_ref(v_a_1547_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_Substring_prev(lean_object* v_a_1550_, lean_object* v_a_1551_){
_start:
{
lean_object* v_str_1552_; lean_object* v_startPos_1553_; lean_object* v_absP_1554_; uint8_t v___x_1555_; 
v_str_1552_ = lean_ctor_get(v_a_1550_, 0);
v_startPos_1553_ = lean_ctor_get(v_a_1550_, 1);
v_absP_1554_ = lean_nat_add(v_startPos_1553_, v_a_1551_);
v___x_1555_ = lean_nat_dec_eq(v_absP_1554_, v_startPos_1553_);
if (v___x_1555_ == 0)
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = lean_string_utf8_prev(v_str_1552_, v_absP_1554_);
lean_dec(v_absP_1554_);
v___x_1557_ = lean_nat_sub(v___x_1556_, v_startPos_1553_);
lean_dec(v___x_1556_);
return v___x_1557_;
}
else
{
lean_dec(v_absP_1554_);
lean_inc(v_a_1551_);
return v_a_1551_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_prev___boxed(lean_object* v_a_1558_, lean_object* v_a_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l_Substring_prev(v_a_1558_, v_a_1559_);
lean_dec(v_a_1559_);
lean_dec_ref(v_a_1558_);
return v_res_1560_;
}
}
LEAN_EXPORT uint8_t l_Substring_atEnd(lean_object* v_a_1561_, lean_object* v_a_1562_){
_start:
{
lean_object* v_startPos_1563_; lean_object* v_stopPos_1564_; lean_object* v___x_1565_; uint8_t v___x_1566_; 
v_startPos_1563_ = lean_ctor_get(v_a_1561_, 1);
v_stopPos_1564_ = lean_ctor_get(v_a_1561_, 2);
v___x_1565_ = lean_nat_add(v_startPos_1563_, v_a_1562_);
v___x_1566_ = lean_nat_dec_eq(v___x_1565_, v_stopPos_1564_);
lean_dec(v___x_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Substring_atEnd___boxed(lean_object* v_a_1567_, lean_object* v_a_1568_){
_start:
{
uint8_t v_res_1569_; lean_object* v_r_1570_; 
v_res_1569_ = l_Substring_atEnd(v_a_1567_, v_a_1568_);
lean_dec(v_a_1568_);
lean_dec_ref(v_a_1567_);
v_r_1570_ = lean_box(v_res_1569_);
return v_r_1570_;
}
}
LEAN_EXPORT uint8_t l_Substring_beq(lean_object* v_ss1_1571_, lean_object* v_ss2_1572_){
_start:
{
uint8_t v___x_1573_; 
v___x_1573_ = l_Substring_Raw_beq(v_ss1_1571_, v_ss2_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Substring_beq___boxed(lean_object* v_ss1_1574_, lean_object* v_ss2_1575_){
_start:
{
uint8_t v_res_1576_; lean_object* v_r_1577_; 
v_res_1576_ = l_Substring_beq(v_ss1_1574_, v_ss2_1575_);
v_r_1577_ = lean_box(v_res_1576_);
return v_r_1577_;
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

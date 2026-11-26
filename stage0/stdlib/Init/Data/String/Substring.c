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
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(lean_object*);
lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
uint8_t l_String_Slice_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Substring_Raw_splitOn_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Substring_Raw_splitOn_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Substring_Raw_splitOn_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Substring_Raw_splitOn_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Slice_splitToSubslice___at___00Substring_Raw_splitOn_spec__0___redArg___closed__0_value)}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Substring_Raw_splitOn_spec__0___redArg___closed__1 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Substring_Raw_splitOn_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Substring_Raw_splitOn_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Substring_Raw_splitOn_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Substring_Raw_splitOn_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Substring_Raw_splitOn_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Substring_Raw_splitOn_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Substring_Raw_splitOn_spec__2(lean_object*, lean_object*);
static const lean_array_object l_Substring_Raw_splitOn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Substring_Raw_splitOn___closed__0 = (const lean_object*)&l_Substring_Raw_splitOn___closed__0_value;
LEAN_EXPORT lean_object* l_Substring_Raw_splitOn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Substring_Raw_splitOn_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Substring_Raw_splitOn_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Substring_Raw_splitOn_spec__0___redArg(lean_object* v_sep_390_){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_391_ = lean_unsigned_to_nat(0u);
v___x_392_ = lean_string_utf8_byte_size(v_sep_390_);
v___x_393_ = lean_nat_dec_eq(v___x_392_, v___x_391_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_394_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_394_, 0, v_sep_390_);
lean_ctor_set(v___x_394_, 1, v___x_391_);
lean_ctor_set(v___x_394_, 2, v___x_392_);
v___x_395_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_394_);
v___x_396_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_396_, 0, v___x_394_);
lean_ctor_set(v___x_396_, 1, v___x_395_);
lean_ctor_set(v___x_396_, 2, v___x_391_);
lean_ctor_set(v___x_396_, 3, v___x_391_);
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_391_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
return v___x_397_;
}
else
{
lean_object* v___x_398_; 
lean_dec_ref(v_sep_390_);
v___x_398_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Substring_Raw_splitOn_spec__0___redArg___closed__1));
return v___x_398_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Substring_Raw_splitOn_spec__0(lean_object* v_sep_399_, lean_object* v_s_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_String_Slice_splitToSubslice___at___00Substring_Raw_splitOn_spec__0___redArg(v_sep_399_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Substring_Raw_splitOn_spec__0___boxed(lean_object* v_sep_402_, lean_object* v_s_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_String_Slice_splitToSubslice___at___00Substring_Raw_splitOn_spec__0(v_sep_402_, v_s_403_);
lean_dec_ref(v_s_403_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Substring_Raw_splitOn_spec__1___redArg(lean_object* v___x_405_, lean_object* v___x_406_, lean_object* v___x_407_, lean_object* v___x_408_, lean_object* v_a_409_, lean_object* v_b_410_){
_start:
{
lean_object* v_it_412_; lean_object* v_startInclusive_413_; lean_object* v_endExclusive_414_; 
if (lean_obj_tag(v_a_409_) == 0)
{
lean_object* v_currPos_420_; lean_object* v_searcher_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_532_; 
v_currPos_420_ = lean_ctor_get(v_a_409_, 0);
v_searcher_421_ = lean_ctor_get(v_a_409_, 1);
v_isSharedCheck_532_ = !lean_is_exclusive(v_a_409_);
if (v_isSharedCheck_532_ == 0)
{
v___x_423_ = v_a_409_;
v_isShared_424_ = v_isSharedCheck_532_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_searcher_421_);
lean_inc(v_currPos_420_);
lean_dec(v_a_409_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_532_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v_it_426_; lean_object* v_it_432_; lean_object* v_startPos_433_; lean_object* v_endPos_434_; 
switch(lean_obj_tag(v_searcher_421_))
{
case 0:
{
lean_object* v_pos_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_460_; 
lean_del_object(v___x_423_);
v_pos_448_ = lean_ctor_get(v_searcher_421_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v_searcher_421_);
if (v_isSharedCheck_460_ == 0)
{
v___x_450_ = v_searcher_421_;
v_isShared_451_ = v_isSharedCheck_460_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_pos_448_);
lean_dec(v_searcher_421_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_460_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v_startInclusive_452_; lean_object* v_endExclusive_453_; lean_object* v___x_454_; uint8_t v_decide_455_; 
v_startInclusive_452_ = lean_ctor_get(v___x_407_, 1);
v_endExclusive_453_ = lean_ctor_get(v___x_407_, 2);
v___x_454_ = lean_nat_sub(v_endExclusive_453_, v_startInclusive_452_);
v_decide_455_ = lean_nat_dec_eq(v_pos_448_, v___x_454_);
lean_dec(v___x_454_);
if (v_decide_455_ == 0)
{
lean_object* v___x_457_; 
lean_inc(v_pos_448_);
if (v_isShared_451_ == 0)
{
lean_ctor_set_tag(v___x_450_, 1);
v___x_457_ = v___x_450_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_pos_448_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_inc(v_pos_448_);
v_it_432_ = v___x_457_;
v_startPos_433_ = v_pos_448_;
v_endPos_434_ = v_pos_448_;
goto v___jp_431_;
}
}
else
{
lean_object* v___x_459_; 
lean_del_object(v___x_450_);
v___x_459_ = lean_box(3);
lean_inc(v_pos_448_);
v_it_432_ = v___x_459_;
v_startPos_433_ = v_pos_448_;
v_endPos_434_ = v_pos_448_;
goto v___jp_431_;
}
}
}
case 1:
{
lean_object* v_pos_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_471_; 
v_pos_461_ = lean_ctor_get(v_searcher_421_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v_searcher_421_);
if (v_isSharedCheck_471_ == 0)
{
v___x_463_ = v_searcher_421_;
v_isShared_464_ = v_isSharedCheck_471_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_pos_461_);
lean_dec(v_searcher_421_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_471_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_465_ = lean_nat_add(v___x_405_, v_pos_461_);
lean_dec(v_pos_461_);
v___x_466_ = lean_string_utf8_next_fast(v___x_406_, v___x_465_);
lean_dec(v___x_465_);
v___x_467_ = lean_nat_sub(v___x_466_, v___x_405_);
if (v_isShared_464_ == 0)
{
lean_ctor_set_tag(v___x_463_, 0);
lean_ctor_set(v___x_463_, 0, v___x_467_);
v___x_469_ = v___x_463_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_467_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
v_it_426_ = v___x_469_;
goto v___jp_425_;
}
}
}
case 2:
{
lean_object* v_needle_472_; lean_object* v_table_473_; lean_object* v_stackPos_474_; lean_object* v_needlePos_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_531_; 
v_needle_472_ = lean_ctor_get(v_searcher_421_, 0);
v_table_473_ = lean_ctor_get(v_searcher_421_, 1);
v_stackPos_474_ = lean_ctor_get(v_searcher_421_, 2);
v_needlePos_475_ = lean_ctor_get(v_searcher_421_, 3);
v_isSharedCheck_531_ = !lean_is_exclusive(v_searcher_421_);
if (v_isSharedCheck_531_ == 0)
{
v___x_477_ = v_searcher_421_;
v_isShared_478_ = v_isSharedCheck_531_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_needlePos_475_);
lean_inc(v_stackPos_474_);
lean_inc(v_table_473_);
lean_inc(v_needle_472_);
lean_dec(v_searcher_421_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_531_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v_str_479_; lean_object* v_startInclusive_480_; lean_object* v_endExclusive_481_; lean_object* v_basePos_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v_str_479_ = lean_ctor_get(v_needle_472_, 0);
v_startInclusive_480_ = lean_ctor_get(v_needle_472_, 1);
v_endExclusive_481_ = lean_ctor_get(v_needle_472_, 2);
v_basePos_482_ = lean_nat_sub(v_stackPos_474_, v_needlePos_475_);
v___x_483_ = lean_nat_sub(v_endExclusive_481_, v_startInclusive_480_);
v___x_484_ = lean_nat_add(v_basePos_482_, v___x_483_);
v___x_485_ = lean_nat_sub(v___x_408_, v___x_405_);
v___x_486_ = lean_nat_dec_le(v___x_484_, v___x_485_);
lean_dec(v___x_484_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
lean_dec(v___x_483_);
lean_del_object(v___x_477_);
lean_dec(v_needlePos_475_);
lean_dec(v_stackPos_474_);
lean_dec_ref(v_table_473_);
lean_dec_ref(v_needle_472_);
v___x_487_ = lean_unsigned_to_nat(1u);
v___x_488_ = lean_nat_add(v_basePos_482_, v___x_487_);
lean_dec(v_basePos_482_);
v___x_489_ = lean_nat_dec_le(v___x_488_, v___x_485_);
lean_dec(v___x_485_);
lean_dec(v___x_488_);
if (v___x_489_ == 0)
{
lean_del_object(v___x_423_);
goto v___jp_445_;
}
else
{
lean_object* v___x_490_; 
v___x_490_ = lean_box(3);
v_it_426_ = v___x_490_;
goto v___jp_425_;
}
}
else
{
lean_object* v___x_491_; uint8_t v_stackByte_492_; lean_object* v___x_493_; uint8_t v_patByte_494_; uint8_t v___x_495_; 
lean_dec(v___x_485_);
lean_dec(v_basePos_482_);
v___x_491_ = lean_nat_add(v___x_405_, v_stackPos_474_);
v_stackByte_492_ = lean_string_get_byte_fast(v___x_406_, v___x_491_);
v___x_493_ = lean_nat_add(v_startInclusive_480_, v_needlePos_475_);
v_patByte_494_ = lean_string_get_byte_fast(v_str_479_, v___x_493_);
v___x_495_ = lean_uint8_dec_eq(v_stackByte_492_, v_patByte_494_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; uint8_t v_decide_497_; 
lean_dec(v___x_483_);
v___x_496_ = lean_unsigned_to_nat(0u);
v_decide_497_ = lean_nat_dec_eq(v_needlePos_475_, v___x_496_);
if (v_decide_497_ == 0)
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v_newNeedlePos_500_; uint8_t v___x_501_; 
v___x_498_ = lean_unsigned_to_nat(1u);
v___x_499_ = lean_nat_sub(v_needlePos_475_, v___x_498_);
lean_dec(v_needlePos_475_);
v_newNeedlePos_500_ = lean_array_fget_borrowed(v_table_473_, v___x_499_);
lean_dec(v___x_499_);
v___x_501_ = lean_nat_dec_eq(v_newNeedlePos_500_, v___x_496_);
if (v___x_501_ == 0)
{
lean_object* v___x_503_; 
lean_inc(v_newNeedlePos_500_);
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 3, v_newNeedlePos_500_);
v___x_503_ = v___x_477_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_needle_472_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v_table_473_);
lean_ctor_set(v_reuseFailAlloc_504_, 2, v_stackPos_474_);
lean_ctor_set(v_reuseFailAlloc_504_, 3, v_newNeedlePos_500_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
v_it_426_ = v___x_503_;
goto v___jp_425_;
}
}
else
{
lean_object* v_nextStackPos_505_; lean_object* v___x_507_; 
v_nextStackPos_505_ = l_String_Slice_posGE___redArg(v___x_407_, v_stackPos_474_);
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 3, v___x_496_);
lean_ctor_set(v___x_477_, 2, v_nextStackPos_505_);
v___x_507_ = v___x_477_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_needle_472_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v_table_473_);
lean_ctor_set(v_reuseFailAlloc_508_, 2, v_nextStackPos_505_);
lean_ctor_set(v_reuseFailAlloc_508_, 3, v___x_496_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
v_it_426_ = v___x_507_;
goto v___jp_425_;
}
}
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v_nextStackPos_511_; lean_object* v___x_513_; 
lean_dec(v_needlePos_475_);
v___x_509_ = lean_unsigned_to_nat(1u);
v___x_510_ = lean_nat_add(v_stackPos_474_, v___x_509_);
lean_dec(v_stackPos_474_);
v_nextStackPos_511_ = l_String_Slice_posGE___redArg(v___x_407_, v___x_510_);
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 3, v___x_496_);
lean_ctor_set(v___x_477_, 2, v_nextStackPos_511_);
v___x_513_ = v___x_477_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_needle_472_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_table_473_);
lean_ctor_set(v_reuseFailAlloc_514_, 2, v_nextStackPos_511_);
lean_ctor_set(v_reuseFailAlloc_514_, 3, v___x_496_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
v_it_426_ = v___x_513_;
goto v___jp_425_;
}
}
}
else
{
lean_object* v___x_515_; lean_object* v_nextStackPos_516_; lean_object* v_nextNeedlePos_517_; uint8_t v_decide_518_; 
lean_del_object(v___x_423_);
v___x_515_ = lean_unsigned_to_nat(1u);
v_nextStackPos_516_ = lean_nat_add(v_stackPos_474_, v___x_515_);
lean_dec(v_stackPos_474_);
v_nextNeedlePos_517_ = lean_nat_add(v_needlePos_475_, v___x_515_);
lean_dec(v_needlePos_475_);
v_decide_518_ = lean_nat_dec_eq(v_nextNeedlePos_517_, v___x_483_);
lean_dec(v___x_483_);
if (v_decide_518_ == 0)
{
lean_object* v___x_520_; 
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 3, v_nextNeedlePos_517_);
lean_ctor_set(v___x_477_, 2, v_nextStackPos_516_);
v___x_520_ = v___x_477_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_needle_472_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_table_473_);
lean_ctor_set(v_reuseFailAlloc_523_, 2, v_nextStackPos_516_);
lean_ctor_set(v_reuseFailAlloc_523_, 3, v_nextNeedlePos_517_);
v___x_520_ = v_reuseFailAlloc_523_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
lean_object* v___x_521_; 
v___x_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_521_, 0, v_currPos_420_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v_a_409_ = v___x_521_;
goto _start;
}
}
else
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_524_ = lean_nat_sub(v_nextStackPos_516_, v_nextNeedlePos_517_);
lean_dec(v_nextNeedlePos_517_);
v___x_525_ = l_String_Slice_pos_x21(v___x_407_, v___x_524_);
lean_dec(v___x_524_);
v___x_526_ = l_String_Slice_pos_x21(v___x_407_, v_nextStackPos_516_);
v___x_527_ = lean_unsigned_to_nat(0u);
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 3, v___x_527_);
lean_ctor_set(v___x_477_, 2, v_nextStackPos_516_);
v___x_529_ = v___x_477_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_needle_472_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_table_473_);
lean_ctor_set(v_reuseFailAlloc_530_, 2, v_nextStackPos_516_);
lean_ctor_set(v_reuseFailAlloc_530_, 3, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
v_it_432_ = v___x_529_;
v_startPos_433_ = v___x_525_;
v_endPos_434_ = v___x_526_;
goto v___jp_431_;
}
}
}
}
}
}
default: 
{
lean_del_object(v___x_423_);
goto v___jp_445_;
}
}
v___jp_425_:
{
lean_object* v___x_428_; 
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 1, v_it_426_);
v___x_428_ = v___x_423_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_currPos_420_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_it_426_);
v___x_428_ = v_reuseFailAlloc_430_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
v_a_409_ = v___x_428_;
goto _start;
}
}
v___jp_431_:
{
lean_object* v_slice_435_; lean_object* v_startInclusive_436_; lean_object* v_endExclusive_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
v_slice_435_ = l_String_Slice_subslice_x21(v___x_407_, v_currPos_420_, v_startPos_433_);
v_startInclusive_436_ = lean_ctor_get(v_slice_435_, 0);
v_endExclusive_437_ = lean_ctor_get(v_slice_435_, 1);
v_isSharedCheck_444_ = !lean_is_exclusive(v_slice_435_);
if (v_isSharedCheck_444_ == 0)
{
v___x_439_ = v_slice_435_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_endExclusive_437_);
lean_inc(v_startInclusive_436_);
lean_dec(v_slice_435_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v_nextIt_442_; 
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v_it_432_);
lean_ctor_set(v___x_439_, 0, v_endPos_434_);
v_nextIt_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_endPos_434_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_it_432_);
v_nextIt_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
v_it_412_ = v_nextIt_442_;
v_startInclusive_413_ = v_startInclusive_436_;
v_endExclusive_414_ = v_endExclusive_437_;
goto v___jp_411_;
}
}
}
v___jp_445_:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = lean_nat_sub(v___x_408_, v___x_405_);
v___x_447_ = lean_box(1);
v_it_412_ = v___x_447_;
v_startInclusive_413_ = v_currPos_420_;
v_endExclusive_414_ = v___x_446_;
goto v___jp_411_;
}
}
}
else
{
lean_dec_ref(v___x_406_);
return v_b_410_;
}
v___jp_411_:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_415_ = lean_nat_add(v___x_405_, v_startInclusive_413_);
lean_dec(v_startInclusive_413_);
v___x_416_ = lean_nat_add(v___x_405_, v_endExclusive_414_);
lean_dec(v_endExclusive_414_);
lean_inc_ref(v___x_406_);
v___x_417_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_417_, 0, v___x_406_);
lean_ctor_set(v___x_417_, 1, v___x_415_);
lean_ctor_set(v___x_417_, 2, v___x_416_);
v___x_418_ = lean_array_push(v_b_410_, v___x_417_);
v_a_409_ = v_it_412_;
v_b_410_ = v___x_418_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Substring_Raw_splitOn_spec__1___redArg___boxed(lean_object* v___x_533_, lean_object* v___x_534_, lean_object* v___x_535_, lean_object* v___x_536_, lean_object* v_a_537_, lean_object* v_b_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Substring_Raw_splitOn_spec__1___redArg(v___x_533_, v___x_534_, v___x_535_, v___x_536_, v_a_537_, v_b_538_);
lean_dec(v___x_536_);
lean_dec_ref(v___x_535_);
lean_dec(v___x_533_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Substring_Raw_splitOn_spec__2(lean_object* v_a_540_, lean_object* v_a_541_){
_start:
{
if (lean_obj_tag(v_a_540_) == 0)
{
lean_object* v___x_542_; 
v___x_542_ = l_List_reverse___redArg(v_a_541_);
return v___x_542_;
}
else
{
lean_object* v_head_543_; lean_object* v_tail_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_562_; 
v_head_543_ = lean_ctor_get(v_a_540_, 0);
v_tail_544_ = lean_ctor_get(v_a_540_, 1);
v_isSharedCheck_562_ = !lean_is_exclusive(v_a_540_);
if (v_isSharedCheck_562_ == 0)
{
v___x_546_ = v_a_540_;
v_isShared_547_ = v_isSharedCheck_562_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_tail_544_);
lean_inc(v_head_543_);
lean_dec(v_a_540_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_562_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v_str_548_; lean_object* v_startInclusive_549_; lean_object* v_endExclusive_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_561_; 
v_str_548_ = lean_ctor_get(v_head_543_, 0);
v_startInclusive_549_ = lean_ctor_get(v_head_543_, 1);
v_endExclusive_550_ = lean_ctor_get(v_head_543_, 2);
v_isSharedCheck_561_ = !lean_is_exclusive(v_head_543_);
if (v_isSharedCheck_561_ == 0)
{
v___x_552_ = v_head_543_;
v_isShared_553_ = v_isSharedCheck_561_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_endExclusive_550_);
lean_inc(v_startInclusive_549_);
lean_inc(v_str_548_);
lean_dec(v_head_543_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_561_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_str_548_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_startInclusive_549_);
lean_ctor_set(v_reuseFailAlloc_560_, 2, v_endExclusive_550_);
v___x_555_ = v_reuseFailAlloc_560_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_557_; 
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 1, v_a_541_);
lean_ctor_set(v___x_546_, 0, v___x_555_);
v___x_557_ = v___x_546_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_555_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_a_541_);
v___x_557_ = v_reuseFailAlloc_559_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
v_a_540_ = v_tail_544_;
v_a_541_ = v___x_557_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_splitOn(lean_object* v_s_565_, lean_object* v_sep_566_){
_start:
{
lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_570_ = ((lean_object*)(l_Substring_Raw_extract___closed__0));
v___x_571_ = lean_string_dec_eq(v_sep_566_, v___x_570_);
if (v___x_571_ == 0)
{
lean_object* v_str_572_; lean_object* v_startPos_573_; lean_object* v_stopPos_574_; uint8_t v___x_575_; 
v_str_572_ = lean_ctor_get(v_s_565_, 0);
v_startPos_573_ = lean_ctor_get(v_s_565_, 1);
v_stopPos_574_ = lean_ctor_get(v_s_565_, 2);
v___x_575_ = lean_string_is_valid_pos(v_str_572_, v_startPos_573_);
if (v___x_575_ == 0)
{
lean_dec_ref(v_sep_566_);
goto v___jp_567_;
}
else
{
uint8_t v___x_576_; 
v___x_576_ = lean_string_is_valid_pos(v_str_572_, v_stopPos_574_);
if (v___x_576_ == 0)
{
lean_dec_ref(v_sep_566_);
goto v___jp_567_;
}
else
{
uint8_t v___x_577_; 
v___x_577_ = lean_nat_dec_le(v_startPos_573_, v_stopPos_574_);
if (v___x_577_ == 0)
{
lean_dec_ref(v_sep_566_);
goto v___jp_567_;
}
else
{
lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_590_; 
lean_inc(v_stopPos_574_);
lean_inc(v_startPos_573_);
lean_inc_ref(v_str_572_);
v_isSharedCheck_590_ = !lean_is_exclusive(v_s_565_);
if (v_isSharedCheck_590_ == 0)
{
lean_object* v_unused_591_; lean_object* v_unused_592_; lean_object* v_unused_593_; 
v_unused_591_ = lean_ctor_get(v_s_565_, 2);
lean_dec(v_unused_591_);
v_unused_592_ = lean_ctor_get(v_s_565_, 1);
lean_dec(v_unused_592_);
v_unused_593_ = lean_ctor_get(v_s_565_, 0);
lean_dec(v_unused_593_);
v___x_579_ = v_s_565_;
v_isShared_580_ = v_isSharedCheck_590_;
goto v_resetjp_578_;
}
else
{
lean_dec(v_s_565_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_590_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
lean_inc(v_stopPos_574_);
lean_inc(v_startPos_573_);
lean_inc_ref(v_str_572_);
if (v_isShared_580_ == 0)
{
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_str_572_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_startPos_573_);
lean_ctor_set(v_reuseFailAlloc_589_, 2, v_stopPos_574_);
v___x_582_ = v_reuseFailAlloc_589_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_583_ = l_String_Slice_splitToSubslice___at___00Substring_Raw_splitOn_spec__0___redArg(v_sep_566_);
v___x_584_ = ((lean_object*)(l_Substring_Raw_splitOn___closed__0));
v___x_585_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Substring_Raw_splitOn_spec__1___redArg(v_startPos_573_, v_str_572_, v___x_582_, v_stopPos_574_, v___x_583_, v___x_584_);
lean_dec(v_stopPos_574_);
lean_dec_ref(v___x_582_);
lean_dec(v_startPos_573_);
v___x_586_ = lean_array_to_list(v___x_585_);
v___x_587_ = lean_box(0);
v___x_588_ = l_List_mapTR_loop___at___00Substring_Raw_splitOn_spec__2(v___x_586_, v___x_587_);
return v___x_588_;
}
}
}
}
}
}
else
{
lean_object* v___x_594_; lean_object* v___x_595_; 
lean_dec_ref(v_sep_566_);
v___x_594_ = lean_box(0);
v___x_595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_595_, 0, v_s_565_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
return v___x_595_;
}
v___jp_567_:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_box(0);
v___x_569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_569_, 0, v_s_565_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
return v___x_569_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Substring_Raw_splitOn_spec__1(lean_object* v___x_596_, lean_object* v___x_597_, lean_object* v_sep_598_, lean_object* v___x_599_, lean_object* v___x_600_, lean_object* v_inst_601_, lean_object* v_R_602_, lean_object* v_a_603_, lean_object* v_b_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Substring_Raw_splitOn_spec__1___redArg(v___x_596_, v___x_597_, v___x_599_, v___x_600_, v_a_603_, v_b_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Substring_Raw_splitOn_spec__1___boxed(lean_object* v___x_606_, lean_object* v___x_607_, lean_object* v_sep_608_, lean_object* v___x_609_, lean_object* v___x_610_, lean_object* v_inst_611_, lean_object* v_R_612_, lean_object* v_a_613_, lean_object* v_b_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Substring_Raw_splitOn_spec__1(v___x_606_, v___x_607_, v_sep_608_, v___x_609_, v___x_610_, v_inst_611_, v_R_612_, v_a_613_, v_b_614_);
lean_dec(v___x_610_);
lean_dec_ref(v___x_609_);
lean_dec_ref(v_sep_608_);
lean_dec(v___x_606_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldl___redArg___lam__0(lean_object* v___y_616_, lean_object* v_f_617_, lean_object* v_it_618_, lean_object* v_acc_619_, lean_object* v_hP_620_, lean_object* v_recur_621_){
_start:
{
lean_object* v_str_622_; lean_object* v_startInclusive_623_; lean_object* v_endExclusive_624_; lean_object* v___x_625_; uint8_t v_decide_626_; 
v_str_622_ = lean_ctor_get(v___y_616_, 0);
v_startInclusive_623_ = lean_ctor_get(v___y_616_, 1);
v_endExclusive_624_ = lean_ctor_get(v___y_616_, 2);
v___x_625_ = lean_nat_sub(v_endExclusive_624_, v_startInclusive_623_);
v_decide_626_ = lean_nat_dec_eq(v_it_618_, v___x_625_);
lean_dec(v___x_625_);
if (v_decide_626_ == 0)
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; uint32_t v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_627_ = lean_nat_add(v_startInclusive_623_, v_it_618_);
v___x_628_ = lean_string_utf8_next_fast(v_str_622_, v___x_627_);
v___x_629_ = lean_nat_sub(v___x_628_, v_startInclusive_623_);
v___x_630_ = lean_string_utf8_get_fast(v_str_622_, v___x_627_);
lean_dec(v___x_627_);
v___x_631_ = lean_box_uint32(v___x_630_);
v___x_632_ = lean_apply_2(v_f_617_, v_acc_619_, v___x_631_);
v___x_633_ = lean_apply_4(v_recur_621_, v___x_629_, v___x_632_, lean_box(0), lean_box(0));
return v___x_633_;
}
else
{
lean_dec(v_recur_621_);
lean_dec(v_f_617_);
return v_acc_619_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldl___redArg___lam__0___boxed(lean_object* v___y_634_, lean_object* v_f_635_, lean_object* v_it_636_, lean_object* v_acc_637_, lean_object* v_hP_638_, lean_object* v_recur_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Substring_Raw_foldl___redArg___lam__0(v___y_634_, v_f_635_, v_it_636_, v_acc_637_, v_hP_638_, v_recur_639_);
lean_dec(v_it_636_);
lean_dec_ref(v___y_634_);
return v_res_640_;
}
}
static lean_object* _init_l_Substring_Raw_foldl___redArg___closed__3(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_644_ = ((lean_object*)(l_Substring_Raw_foldl___redArg___closed__2));
v___x_645_ = lean_unsigned_to_nat(14u);
v___x_646_ = lean_unsigned_to_nat(22u);
v___x_647_ = ((lean_object*)(l_Substring_Raw_foldl___redArg___closed__1));
v___x_648_ = ((lean_object*)(l_Substring_Raw_foldl___redArg___closed__0));
v___x_649_ = l_mkPanicMessageWithDecl(v___x_648_, v___x_647_, v___x_646_, v___x_645_, v___x_644_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldl___redArg(lean_object* v_f_650_, lean_object* v_init_651_, lean_object* v_s_652_){
_start:
{
lean_object* v___y_654_; lean_object* v_str_658_; lean_object* v_startPos_659_; lean_object* v_stopPos_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_674_; 
v_str_658_ = lean_ctor_get(v_s_652_, 0);
v_startPos_659_ = lean_ctor_get(v_s_652_, 1);
v_stopPos_660_ = lean_ctor_get(v_s_652_, 2);
v_isSharedCheck_674_ = !lean_is_exclusive(v_s_652_);
if (v_isSharedCheck_674_ == 0)
{
v___x_662_ = v_s_652_;
v_isShared_663_ = v_isSharedCheck_674_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_stopPos_660_);
lean_inc(v_startPos_659_);
lean_inc(v_str_658_);
lean_dec(v_s_652_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_674_;
goto v_resetjp_661_;
}
v___jp_653_:
{
lean_object* v___f_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___f_655_ = lean_alloc_closure((void*)(l_Substring_Raw_foldl___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_655_, 0, v___y_654_);
lean_closure_set(v___f_655_, 1, v_f_650_);
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_655_, v___x_656_, v_init_651_, lean_box(0));
return v___x_657_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; uint8_t v___x_668_; 
v___x_664_ = l_String_instInhabitedSlice;
v___x_668_ = lean_string_is_valid_pos(v_str_658_, v_startPos_659_);
if (v___x_668_ == 0)
{
lean_del_object(v___x_662_);
lean_dec(v_stopPos_660_);
lean_dec(v_startPos_659_);
lean_dec_ref(v_str_658_);
goto v___jp_665_;
}
else
{
uint8_t v___x_669_; 
v___x_669_ = lean_string_is_valid_pos(v_str_658_, v_stopPos_660_);
if (v___x_669_ == 0)
{
lean_del_object(v___x_662_);
lean_dec(v_stopPos_660_);
lean_dec(v_startPos_659_);
lean_dec_ref(v_str_658_);
goto v___jp_665_;
}
else
{
uint8_t v___x_670_; 
v___x_670_ = lean_nat_dec_le(v_startPos_659_, v_stopPos_660_);
if (v___x_670_ == 0)
{
lean_del_object(v___x_662_);
lean_dec(v_stopPos_660_);
lean_dec(v_startPos_659_);
lean_dec_ref(v_str_658_);
goto v___jp_665_;
}
else
{
lean_object* v___x_672_; 
if (v_isShared_663_ == 0)
{
v___x_672_ = v___x_662_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_str_658_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v_startPos_659_);
lean_ctor_set(v_reuseFailAlloc_673_, 2, v_stopPos_660_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
v___y_654_ = v___x_672_;
goto v___jp_653_;
}
}
}
}
v___jp_665_:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_667_ = l_panic___redArg(v___x_664_, v___x_666_);
v___y_654_ = v___x_667_;
goto v___jp_653_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldl(lean_object* v_00_u03b1_675_, lean_object* v_f_676_, lean_object* v_init_677_, lean_object* v_s_678_){
_start:
{
lean_object* v___y_680_; lean_object* v_str_684_; lean_object* v_startPos_685_; lean_object* v_stopPos_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_700_; 
v_str_684_ = lean_ctor_get(v_s_678_, 0);
v_startPos_685_ = lean_ctor_get(v_s_678_, 1);
v_stopPos_686_ = lean_ctor_get(v_s_678_, 2);
v_isSharedCheck_700_ = !lean_is_exclusive(v_s_678_);
if (v_isSharedCheck_700_ == 0)
{
v___x_688_ = v_s_678_;
v_isShared_689_ = v_isSharedCheck_700_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_stopPos_686_);
lean_inc(v_startPos_685_);
lean_inc(v_str_684_);
lean_dec(v_s_678_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_700_;
goto v_resetjp_687_;
}
v___jp_679_:
{
lean_object* v___f_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___f_681_ = lean_alloc_closure((void*)(l_Substring_Raw_foldl___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_681_, 0, v___y_680_);
lean_closure_set(v___f_681_, 1, v_f_676_);
v___x_682_ = lean_unsigned_to_nat(0u);
v___x_683_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_681_, v___x_682_, v_init_677_, lean_box(0));
return v___x_683_;
}
v_resetjp_687_:
{
lean_object* v___x_690_; uint8_t v___x_694_; 
v___x_690_ = l_String_instInhabitedSlice;
v___x_694_ = lean_string_is_valid_pos(v_str_684_, v_startPos_685_);
if (v___x_694_ == 0)
{
lean_del_object(v___x_688_);
lean_dec(v_stopPos_686_);
lean_dec(v_startPos_685_);
lean_dec_ref(v_str_684_);
goto v___jp_691_;
}
else
{
uint8_t v___x_695_; 
v___x_695_ = lean_string_is_valid_pos(v_str_684_, v_stopPos_686_);
if (v___x_695_ == 0)
{
lean_del_object(v___x_688_);
lean_dec(v_stopPos_686_);
lean_dec(v_startPos_685_);
lean_dec_ref(v_str_684_);
goto v___jp_691_;
}
else
{
uint8_t v___x_696_; 
v___x_696_ = lean_nat_dec_le(v_startPos_685_, v_stopPos_686_);
if (v___x_696_ == 0)
{
lean_del_object(v___x_688_);
lean_dec(v_stopPos_686_);
lean_dec(v_startPos_685_);
lean_dec_ref(v_str_684_);
goto v___jp_691_;
}
else
{
lean_object* v___x_698_; 
if (v_isShared_689_ == 0)
{
v___x_698_ = v___x_688_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_str_684_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_startPos_685_);
lean_ctor_set(v_reuseFailAlloc_699_, 2, v_stopPos_686_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
v___y_680_ = v___x_698_;
goto v___jp_679_;
}
}
}
}
v___jp_691_:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_693_ = l_panic___redArg(v___x_690_, v___x_692_);
v___y_680_ = v___x_693_;
goto v___jp_679_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr___redArg___lam__0(lean_object* v___y_701_, lean_object* v_f_702_, lean_object* v_it_703_, lean_object* v_acc_704_, lean_object* v_hP_705_, lean_object* v_recur_706_){
_start:
{
lean_object* v___x_707_; uint8_t v_decide_708_; 
v___x_707_ = lean_unsigned_to_nat(0u);
v_decide_708_ = lean_nat_dec_eq(v_it_703_, v___x_707_);
if (v_decide_708_ == 0)
{
lean_object* v_str_709_; lean_object* v_startInclusive_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v_prevPos_713_; lean_object* v___x_714_; uint32_t v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v_str_709_ = lean_ctor_get(v___y_701_, 0);
v_startInclusive_710_ = lean_ctor_get(v___y_701_, 1);
v___x_711_ = lean_unsigned_to_nat(1u);
v___x_712_ = lean_nat_sub(v_it_703_, v___x_711_);
v_prevPos_713_ = l_String_Slice_posLE(v___y_701_, v___x_712_);
v___x_714_ = lean_nat_add(v_startInclusive_710_, v_prevPos_713_);
v___x_715_ = lean_string_utf8_get_fast(v_str_709_, v___x_714_);
lean_dec(v___x_714_);
v___x_716_ = lean_box_uint32(v___x_715_);
v___x_717_ = lean_apply_2(v_f_702_, v___x_716_, v_acc_704_);
v___x_718_ = lean_apply_4(v_recur_706_, v_prevPos_713_, v___x_717_, lean_box(0), lean_box(0));
return v___x_718_;
}
else
{
lean_dec(v_recur_706_);
lean_dec(v_f_702_);
return v_acc_704_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr___redArg___lam__0___boxed(lean_object* v___y_719_, lean_object* v_f_720_, lean_object* v_it_721_, lean_object* v_acc_722_, lean_object* v_hP_723_, lean_object* v_recur_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Substring_Raw_foldr___redArg___lam__0(v___y_719_, v_f_720_, v_it_721_, v_acc_722_, v_hP_723_, v_recur_724_);
lean_dec(v_it_721_);
lean_dec_ref(v___y_719_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr___redArg(lean_object* v_f_726_, lean_object* v_init_727_, lean_object* v_s_728_){
_start:
{
lean_object* v___y_730_; lean_object* v_str_734_; lean_object* v_startPos_735_; lean_object* v_stopPos_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_750_; 
v_str_734_ = lean_ctor_get(v_s_728_, 0);
v_startPos_735_ = lean_ctor_get(v_s_728_, 1);
v_stopPos_736_ = lean_ctor_get(v_s_728_, 2);
v_isSharedCheck_750_ = !lean_is_exclusive(v_s_728_);
if (v_isSharedCheck_750_ == 0)
{
v___x_738_ = v_s_728_;
v_isShared_739_ = v_isSharedCheck_750_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_stopPos_736_);
lean_inc(v_startPos_735_);
lean_inc(v_str_734_);
lean_dec(v_s_728_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_750_;
goto v_resetjp_737_;
}
v___jp_729_:
{
lean_object* v___f_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
lean_inc_ref(v___y_730_);
v___f_731_ = lean_alloc_closure((void*)(l_Substring_Raw_foldr___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_731_, 0, v___y_730_);
lean_closure_set(v___f_731_, 1, v_f_726_);
v___x_732_ = l_String_Slice_revPositions(v___y_730_);
lean_dec_ref(v___y_730_);
v___x_733_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_731_, v___x_732_, v_init_727_, lean_box(0));
return v___x_733_;
}
v_resetjp_737_:
{
lean_object* v___x_740_; uint8_t v___x_744_; 
v___x_740_ = l_String_instInhabitedSlice;
v___x_744_ = lean_string_is_valid_pos(v_str_734_, v_startPos_735_);
if (v___x_744_ == 0)
{
lean_del_object(v___x_738_);
lean_dec(v_stopPos_736_);
lean_dec(v_startPos_735_);
lean_dec_ref(v_str_734_);
goto v___jp_741_;
}
else
{
uint8_t v___x_745_; 
v___x_745_ = lean_string_is_valid_pos(v_str_734_, v_stopPos_736_);
if (v___x_745_ == 0)
{
lean_del_object(v___x_738_);
lean_dec(v_stopPos_736_);
lean_dec(v_startPos_735_);
lean_dec_ref(v_str_734_);
goto v___jp_741_;
}
else
{
uint8_t v___x_746_; 
v___x_746_ = lean_nat_dec_le(v_startPos_735_, v_stopPos_736_);
if (v___x_746_ == 0)
{
lean_del_object(v___x_738_);
lean_dec(v_stopPos_736_);
lean_dec(v_startPos_735_);
lean_dec_ref(v_str_734_);
goto v___jp_741_;
}
else
{
lean_object* v___x_748_; 
if (v_isShared_739_ == 0)
{
v___x_748_ = v___x_738_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_str_734_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v_startPos_735_);
lean_ctor_set(v_reuseFailAlloc_749_, 2, v_stopPos_736_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
v___y_730_ = v___x_748_;
goto v___jp_729_;
}
}
}
}
v___jp_741_:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_743_ = l_panic___redArg(v___x_740_, v___x_742_);
v___y_730_ = v___x_743_;
goto v___jp_729_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_foldr(lean_object* v_00_u03b1_751_, lean_object* v_f_752_, lean_object* v_init_753_, lean_object* v_s_754_){
_start:
{
lean_object* v___y_756_; lean_object* v_str_760_; lean_object* v_startPos_761_; lean_object* v_stopPos_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_776_; 
v_str_760_ = lean_ctor_get(v_s_754_, 0);
v_startPos_761_ = lean_ctor_get(v_s_754_, 1);
v_stopPos_762_ = lean_ctor_get(v_s_754_, 2);
v_isSharedCheck_776_ = !lean_is_exclusive(v_s_754_);
if (v_isSharedCheck_776_ == 0)
{
v___x_764_ = v_s_754_;
v_isShared_765_ = v_isSharedCheck_776_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_stopPos_762_);
lean_inc(v_startPos_761_);
lean_inc(v_str_760_);
lean_dec(v_s_754_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_776_;
goto v_resetjp_763_;
}
v___jp_755_:
{
lean_object* v___f_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
lean_inc_ref(v___y_756_);
v___f_757_ = lean_alloc_closure((void*)(l_Substring_Raw_foldr___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_757_, 0, v___y_756_);
lean_closure_set(v___f_757_, 1, v_f_752_);
v___x_758_ = l_String_Slice_revPositions(v___y_756_);
lean_dec_ref(v___y_756_);
v___x_759_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_757_, v___x_758_, v_init_753_, lean_box(0));
return v___x_759_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; uint8_t v___x_770_; 
v___x_766_ = l_String_instInhabitedSlice;
v___x_770_ = lean_string_is_valid_pos(v_str_760_, v_startPos_761_);
if (v___x_770_ == 0)
{
lean_del_object(v___x_764_);
lean_dec(v_stopPos_762_);
lean_dec(v_startPos_761_);
lean_dec_ref(v_str_760_);
goto v___jp_767_;
}
else
{
uint8_t v___x_771_; 
v___x_771_ = lean_string_is_valid_pos(v_str_760_, v_stopPos_762_);
if (v___x_771_ == 0)
{
lean_del_object(v___x_764_);
lean_dec(v_stopPos_762_);
lean_dec(v_startPos_761_);
lean_dec_ref(v_str_760_);
goto v___jp_767_;
}
else
{
uint8_t v___x_772_; 
v___x_772_ = lean_nat_dec_le(v_startPos_761_, v_stopPos_762_);
if (v___x_772_ == 0)
{
lean_del_object(v___x_764_);
lean_dec(v_stopPos_762_);
lean_dec(v_startPos_761_);
lean_dec_ref(v_str_760_);
goto v___jp_767_;
}
else
{
lean_object* v___x_774_; 
if (v_isShared_765_ == 0)
{
v___x_774_ = v___x_764_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_str_760_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_startPos_761_);
lean_ctor_set(v_reuseFailAlloc_775_, 2, v_stopPos_762_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
v___y_756_ = v___x_774_;
goto v___jp_755_;
}
}
}
}
v___jp_767_:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_769_ = l_panic___redArg(v___x_766_, v___x_768_);
v___y_756_ = v___x_769_;
goto v___jp_755_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_any___lam__0(lean_object* v___x_777_, lean_object* v_s_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(v_s_778_, v___x_777_, v___y_779_, lean_box(0), lean_box(0), v___y_782_, v___y_783_, v___y_784_);
return v___x_785_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_any(lean_object* v_s_786_, lean_object* v_p_787_){
_start:
{
lean_object* v___x_788_; lean_object* v_str_789_; lean_object* v_startPos_790_; lean_object* v_stopPos_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_809_; 
lean_inc_ref(v_p_787_);
v___x_788_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v_p_787_);
v_str_789_ = lean_ctor_get(v_s_786_, 0);
v_startPos_790_ = lean_ctor_get(v_s_786_, 1);
v_stopPos_791_ = lean_ctor_get(v_s_786_, 2);
v_isSharedCheck_809_ = !lean_is_exclusive(v_s_786_);
if (v_isSharedCheck_809_ == 0)
{
v___x_793_ = v_s_786_;
v_isShared_794_ = v_isSharedCheck_809_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_stopPos_791_);
lean_inc(v_startPos_790_);
lean_inc(v_str_789_);
lean_dec(v_s_786_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_809_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_795_; lean_object* v___f_796_; lean_object* v___x_797_; uint8_t v___x_802_; 
v___x_795_ = l_String_instInhabitedSlice;
v___f_796_ = lean_alloc_closure((void*)(l_Substring_Raw_any___lam__0), 8, 1);
lean_closure_set(v___f_796_, 0, v___x_788_);
v___x_797_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_797_, 0, lean_box(0));
lean_closure_set(v___x_797_, 1, v_p_787_);
v___x_802_ = lean_string_is_valid_pos(v_str_789_, v_startPos_790_);
if (v___x_802_ == 0)
{
lean_del_object(v___x_793_);
lean_dec(v_stopPos_791_);
lean_dec(v_startPos_790_);
lean_dec_ref(v_str_789_);
goto v___jp_798_;
}
else
{
uint8_t v___x_803_; 
v___x_803_ = lean_string_is_valid_pos(v_str_789_, v_stopPos_791_);
if (v___x_803_ == 0)
{
lean_del_object(v___x_793_);
lean_dec(v_stopPos_791_);
lean_dec(v_startPos_790_);
lean_dec_ref(v_str_789_);
goto v___jp_798_;
}
else
{
uint8_t v___x_804_; 
v___x_804_ = lean_nat_dec_le(v_startPos_790_, v_stopPos_791_);
if (v___x_804_ == 0)
{
lean_del_object(v___x_793_);
lean_dec(v_stopPos_791_);
lean_dec(v_startPos_790_);
lean_dec_ref(v_str_789_);
goto v___jp_798_;
}
else
{
lean_object* v___x_806_; 
if (v_isShared_794_ == 0)
{
v___x_806_ = v___x_793_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_str_789_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_startPos_790_);
lean_ctor_set(v_reuseFailAlloc_808_, 2, v_stopPos_791_);
v___x_806_ = v_reuseFailAlloc_808_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
uint8_t v___x_807_; 
v___x_807_ = l_String_Slice_contains___redArg(v___f_796_, v___x_806_, v___x_797_);
return v___x_807_;
}
}
}
}
v___jp_798_:
{
lean_object* v___x_799_; lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_799_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_800_ = l_panic___redArg(v___x_795_, v___x_799_);
v___x_801_ = l_String_Slice_contains___redArg(v___f_796_, v___x_800_, v___x_797_);
return v___x_801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_any___boxed(lean_object* v_s_810_, lean_object* v_p_811_){
_start:
{
uint8_t v_res_812_; lean_object* v_r_813_; 
v_res_812_ = l_Substring_Raw_any(v_s_810_, v_p_811_);
v_r_813_ = lean_box(v_res_812_);
return v_r_813_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_all(lean_object* v_s_814_, lean_object* v_p_815_){
_start:
{
lean_object* v___y_817_; lean_object* v_startInclusive_818_; lean_object* v_endExclusive_819_; lean_object* v_str_825_; lean_object* v_startPos_826_; lean_object* v_stopPos_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_843_; 
v_str_825_ = lean_ctor_get(v_s_814_, 0);
v_startPos_826_ = lean_ctor_get(v_s_814_, 1);
v_stopPos_827_ = lean_ctor_get(v_s_814_, 2);
v_isSharedCheck_843_ = !lean_is_exclusive(v_s_814_);
if (v_isSharedCheck_843_ == 0)
{
v___x_829_ = v_s_814_;
v_isShared_830_ = v_isSharedCheck_843_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_stopPos_827_);
lean_inc(v_startPos_826_);
lean_inc(v_str_825_);
lean_dec(v_s_814_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_843_;
goto v_resetjp_828_;
}
v___jp_816_:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; uint8_t v_decide_824_; 
v___x_820_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v_p_815_);
v___x_821_ = lean_unsigned_to_nat(0u);
v___x_822_ = l_String_Slice_Pos_skipWhile___redArg(v___y_817_, v___x_821_, v___x_820_);
lean_dec_ref(v___y_817_);
v___x_823_ = lean_nat_sub(v_endExclusive_819_, v_startInclusive_818_);
lean_dec(v_startInclusive_818_);
lean_dec(v_endExclusive_819_);
v_decide_824_ = lean_nat_dec_eq(v___x_822_, v___x_823_);
lean_dec(v___x_823_);
lean_dec(v___x_822_);
return v_decide_824_;
}
v_resetjp_828_:
{
lean_object* v___x_831_; uint8_t v___x_837_; 
v___x_831_ = l_String_instInhabitedSlice;
v___x_837_ = lean_string_is_valid_pos(v_str_825_, v_startPos_826_);
if (v___x_837_ == 0)
{
lean_del_object(v___x_829_);
lean_dec(v_stopPos_827_);
lean_dec(v_startPos_826_);
lean_dec_ref(v_str_825_);
goto v___jp_832_;
}
else
{
uint8_t v___x_838_; 
v___x_838_ = lean_string_is_valid_pos(v_str_825_, v_stopPos_827_);
if (v___x_838_ == 0)
{
lean_del_object(v___x_829_);
lean_dec(v_stopPos_827_);
lean_dec(v_startPos_826_);
lean_dec_ref(v_str_825_);
goto v___jp_832_;
}
else
{
uint8_t v___x_839_; 
v___x_839_ = lean_nat_dec_le(v_startPos_826_, v_stopPos_827_);
if (v___x_839_ == 0)
{
lean_del_object(v___x_829_);
lean_dec(v_stopPos_827_);
lean_dec(v_startPos_826_);
lean_dec_ref(v_str_825_);
goto v___jp_832_;
}
else
{
lean_object* v___x_841_; 
lean_inc(v_stopPos_827_);
lean_inc(v_startPos_826_);
if (v_isShared_830_ == 0)
{
v___x_841_ = v___x_829_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_str_825_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_startPos_826_);
lean_ctor_set(v_reuseFailAlloc_842_, 2, v_stopPos_827_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
v___y_817_ = v___x_841_;
v_startInclusive_818_ = v_startPos_826_;
v_endExclusive_819_ = v_stopPos_827_;
goto v___jp_816_;
}
}
}
}
v___jp_832_:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v_startInclusive_835_; lean_object* v_endExclusive_836_; 
v___x_833_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_834_ = l_panic___redArg(v___x_831_, v___x_833_);
v_startInclusive_835_ = lean_ctor_get(v___x_834_, 1);
lean_inc(v_startInclusive_835_);
v_endExclusive_836_ = lean_ctor_get(v___x_834_, 2);
lean_inc(v_endExclusive_836_);
v___y_817_ = v___x_834_;
v_startInclusive_818_ = v_startInclusive_835_;
v_endExclusive_819_ = v_endExclusive_836_;
goto v___jp_816_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_all___boxed(lean_object* v_s_844_, lean_object* v_p_845_){
_start:
{
uint8_t v_res_846_; lean_object* v_r_847_; 
v_res_846_ = l_Substring_Raw_all(v_s_844_, v_p_845_);
v_r_847_ = lean_box(v_res_846_);
return v_r_847_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(lean_object* v_msg_848_){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = l_String_instInhabitedSlice;
v___x_850_ = lean_panic_fn_borrowed(v___x_849_, v_msg_848_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0(lean_object* v_p_851_, lean_object* v_s_852_, lean_object* v_pos_853_){
_start:
{
lean_object* v_str_854_; lean_object* v_startInclusive_855_; lean_object* v_endExclusive_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; uint8_t v_decide_860_; 
v_str_854_ = lean_ctor_get(v_s_852_, 0);
v_startInclusive_855_ = lean_ctor_get(v_s_852_, 1);
v_endExclusive_856_ = lean_ctor_get(v_s_852_, 2);
v___x_857_ = lean_nat_add(v_startInclusive_855_, v_pos_853_);
v___x_858_ = lean_unsigned_to_nat(0u);
v___x_859_ = lean_nat_sub(v_endExclusive_856_, v___x_857_);
v_decide_860_ = lean_nat_dec_eq(v___x_858_, v___x_859_);
lean_dec(v___x_859_);
if (v_decide_860_ == 0)
{
uint32_t v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; uint8_t v___x_864_; 
v___x_861_ = lean_string_utf8_get_fast(v_str_854_, v___x_857_);
v___x_862_ = lean_box_uint32(v___x_861_);
lean_inc_ref(v_p_851_);
v___x_863_ = lean_apply_1(v_p_851_, v___x_862_);
v___x_864_ = lean_unbox(v___x_863_);
if (v___x_864_ == 0)
{
lean_dec(v___x_857_);
lean_dec_ref(v_p_851_);
return v_pos_853_;
}
else
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; uint8_t v___x_870_; 
v___x_865_ = lean_string_utf8_next_fast(v_str_854_, v___x_857_);
v___x_866_ = lean_nat_sub(v___x_865_, v___x_857_);
lean_dec(v___x_857_);
v___x_867_ = lean_nat_add(v_pos_853_, v___x_866_);
lean_dec(v___x_866_);
v___x_868_ = lean_unsigned_to_nat(1u);
v___x_869_ = lean_nat_add(v_pos_853_, v___x_868_);
v___x_870_ = lean_nat_dec_le(v___x_869_, v___x_867_);
lean_dec(v___x_869_);
if (v___x_870_ == 0)
{
lean_dec(v___x_867_);
lean_dec_ref(v_p_851_);
return v_pos_853_;
}
else
{
lean_dec(v_pos_853_);
v_pos_853_ = v___x_867_;
goto _start;
}
}
}
else
{
lean_dec(v___x_857_);
lean_dec_ref(v_p_851_);
return v_pos_853_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0___boxed(lean_object* v_p_872_, lean_object* v_s_873_, lean_object* v_pos_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0(v_p_872_, v_s_873_, v_pos_874_);
lean_dec_ref(v_s_873_);
return v_res_875_;
}
}
LEAN_EXPORT uint8_t lean_substring_all(lean_object* v_s_876_, lean_object* v_p_877_){
_start:
{
lean_object* v___y_879_; lean_object* v_startInclusive_880_; lean_object* v_endExclusive_881_; lean_object* v_str_891_; lean_object* v_startPos_892_; lean_object* v_stopPos_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_903_; 
v_str_891_ = lean_ctor_get(v_s_876_, 0);
v_startPos_892_ = lean_ctor_get(v_s_876_, 1);
v_stopPos_893_ = lean_ctor_get(v_s_876_, 2);
v_isSharedCheck_903_ = !lean_is_exclusive(v_s_876_);
if (v_isSharedCheck_903_ == 0)
{
v___x_895_ = v_s_876_;
v_isShared_896_ = v_isSharedCheck_903_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_stopPos_893_);
lean_inc(v_startPos_892_);
lean_inc(v_str_891_);
lean_dec(v_s_876_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_903_;
goto v_resetjp_894_;
}
v___jp_878_:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; uint8_t v_decide_885_; 
v___x_882_ = lean_unsigned_to_nat(0u);
v___x_883_ = l_String_Slice_Pos_skipWhile___at___00Substring_Raw_Internal_allImpl_spec__0(v_p_877_, v___y_879_, v___x_882_);
lean_dec_ref(v___y_879_);
v___x_884_ = lean_nat_sub(v_endExclusive_881_, v_startInclusive_880_);
lean_dec(v_startInclusive_880_);
lean_dec(v_endExclusive_881_);
v_decide_885_ = lean_nat_dec_eq(v___x_883_, v___x_884_);
lean_dec(v___x_884_);
lean_dec(v___x_883_);
return v_decide_885_;
}
v___jp_886_:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v_startInclusive_889_; lean_object* v_endExclusive_890_; 
v___x_887_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_888_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_887_);
v_startInclusive_889_ = lean_ctor_get(v___x_888_, 1);
lean_inc(v_startInclusive_889_);
v_endExclusive_890_ = lean_ctor_get(v___x_888_, 2);
lean_inc(v_endExclusive_890_);
v___y_879_ = v___x_888_;
v_startInclusive_880_ = v_startInclusive_889_;
v_endExclusive_881_ = v_endExclusive_890_;
goto v___jp_878_;
}
v_resetjp_894_:
{
uint8_t v___x_897_; 
v___x_897_ = lean_string_is_valid_pos(v_str_891_, v_startPos_892_);
if (v___x_897_ == 0)
{
lean_del_object(v___x_895_);
lean_dec(v_stopPos_893_);
lean_dec(v_startPos_892_);
lean_dec_ref(v_str_891_);
goto v___jp_886_;
}
else
{
uint8_t v___x_898_; 
v___x_898_ = lean_string_is_valid_pos(v_str_891_, v_stopPos_893_);
if (v___x_898_ == 0)
{
lean_del_object(v___x_895_);
lean_dec(v_stopPos_893_);
lean_dec(v_startPos_892_);
lean_dec_ref(v_str_891_);
goto v___jp_886_;
}
else
{
uint8_t v___x_899_; 
v___x_899_ = lean_nat_dec_le(v_startPos_892_, v_stopPos_893_);
if (v___x_899_ == 0)
{
lean_del_object(v___x_895_);
lean_dec(v_stopPos_893_);
lean_dec(v_startPos_892_);
lean_dec_ref(v_str_891_);
goto v___jp_886_;
}
else
{
lean_object* v___x_901_; 
lean_inc(v_stopPos_893_);
lean_inc(v_startPos_892_);
if (v_isShared_896_ == 0)
{
v___x_901_ = v___x_895_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_str_891_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_startPos_892_);
lean_ctor_set(v_reuseFailAlloc_902_, 2, v_stopPos_893_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
v___y_879_ = v___x_901_;
v_startInclusive_880_ = v_startPos_892_;
v_endExclusive_881_ = v_stopPos_893_;
goto v___jp_878_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_allImpl___boxed(lean_object* v_s_904_, lean_object* v_p_905_){
_start:
{
uint8_t v_res_906_; lean_object* v_r_907_; 
v_res_906_ = lean_substring_all(v_s_904_, v_p_905_);
v_r_907_ = lean_box(v_res_906_);
return v_r_907_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_contains___lam__0(uint32_t v_c_908_, uint32_t v_a_909_){
_start:
{
uint8_t v___x_910_; 
v___x_910_ = lean_uint32_dec_eq(v_a_909_, v_c_908_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_contains___lam__0___boxed(lean_object* v_c_911_, lean_object* v_a_912_){
_start:
{
uint32_t v_c_boxed_913_; uint32_t v_a_boxed_914_; uint8_t v_res_915_; lean_object* v_r_916_; 
v_c_boxed_913_ = lean_unbox_uint32(v_c_911_);
lean_dec(v_c_911_);
v_a_boxed_914_ = lean_unbox_uint32(v_a_912_);
lean_dec(v_a_912_);
v_res_915_ = l_Substring_Raw_contains___lam__0(v_c_boxed_913_, v_a_boxed_914_);
v_r_916_ = lean_box(v_res_915_);
return v_r_916_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_contains(lean_object* v_s_917_, uint32_t v_c_918_){
_start:
{
lean_object* v___x_919_; lean_object* v___f_920_; lean_object* v___x_921_; lean_object* v_str_922_; lean_object* v_startPos_923_; lean_object* v_stopPos_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_942_; 
v___x_919_ = lean_box_uint32(v_c_918_);
v___f_920_ = lean_alloc_closure((void*)(l_Substring_Raw_contains___lam__0___boxed), 2, 1);
lean_closure_set(v___f_920_, 0, v___x_919_);
lean_inc_ref(v___f_920_);
v___x_921_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___f_920_);
v_str_922_ = lean_ctor_get(v_s_917_, 0);
v_startPos_923_ = lean_ctor_get(v_s_917_, 1);
v_stopPos_924_ = lean_ctor_get(v_s_917_, 2);
v_isSharedCheck_942_ = !lean_is_exclusive(v_s_917_);
if (v_isSharedCheck_942_ == 0)
{
v___x_926_ = v_s_917_;
v_isShared_927_ = v_isSharedCheck_942_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_stopPos_924_);
lean_inc(v_startPos_923_);
lean_inc(v_str_922_);
lean_dec(v_s_917_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_942_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_928_; lean_object* v___f_929_; lean_object* v___x_930_; uint8_t v___x_935_; 
v___x_928_ = l_String_instInhabitedSlice;
v___f_929_ = lean_alloc_closure((void*)(l_Substring_Raw_any___lam__0), 8, 1);
lean_closure_set(v___f_929_, 0, v___x_921_);
v___x_930_ = lean_alloc_closure((void*)(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed), 3, 2);
lean_closure_set(v___x_930_, 0, lean_box(0));
lean_closure_set(v___x_930_, 1, v___f_920_);
v___x_935_ = lean_string_is_valid_pos(v_str_922_, v_startPos_923_);
if (v___x_935_ == 0)
{
lean_del_object(v___x_926_);
lean_dec(v_stopPos_924_);
lean_dec(v_startPos_923_);
lean_dec_ref(v_str_922_);
goto v___jp_931_;
}
else
{
uint8_t v___x_936_; 
v___x_936_ = lean_string_is_valid_pos(v_str_922_, v_stopPos_924_);
if (v___x_936_ == 0)
{
lean_del_object(v___x_926_);
lean_dec(v_stopPos_924_);
lean_dec(v_startPos_923_);
lean_dec_ref(v_str_922_);
goto v___jp_931_;
}
else
{
uint8_t v___x_937_; 
v___x_937_ = lean_nat_dec_le(v_startPos_923_, v_stopPos_924_);
if (v___x_937_ == 0)
{
lean_del_object(v___x_926_);
lean_dec(v_stopPos_924_);
lean_dec(v_startPos_923_);
lean_dec_ref(v_str_922_);
goto v___jp_931_;
}
else
{
lean_object* v___x_939_; 
if (v_isShared_927_ == 0)
{
v___x_939_ = v___x_926_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_str_922_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_startPos_923_);
lean_ctor_set(v_reuseFailAlloc_941_, 2, v_stopPos_924_);
v___x_939_ = v_reuseFailAlloc_941_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
uint8_t v___x_940_; 
v___x_940_ = l_String_Slice_contains___redArg(v___f_929_, v___x_939_, v___x_930_);
return v___x_940_;
}
}
}
}
v___jp_931_:
{
lean_object* v___x_932_; lean_object* v___x_933_; uint8_t v___x_934_; 
v___x_932_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_933_ = l_panic___redArg(v___x_928_, v___x_932_);
v___x_934_ = l_String_Slice_contains___redArg(v___f_929_, v___x_933_, v___x_930_);
return v___x_934_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_contains___boxed(lean_object* v_s_943_, lean_object* v_c_944_){
_start:
{
uint32_t v_c_boxed_945_; uint8_t v_res_946_; lean_object* v_r_947_; 
v_c_boxed_945_ = lean_unbox_uint32(v_c_944_);
lean_dec(v_c_944_);
v_res_946_ = l_Substring_Raw_contains(v_s_943_, v_c_boxed_945_);
v_r_947_ = lean_box(v_res_946_);
return v_r_947_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux(lean_object* v_s_948_, lean_object* v_stopPos_949_, lean_object* v_p_950_, lean_object* v_i_951_){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; uint8_t v___x_954_; 
v___x_952_ = lean_unsigned_to_nat(1u);
v___x_953_ = lean_nat_add(v_i_951_, v___x_952_);
v___x_954_ = lean_nat_dec_le(v___x_953_, v_stopPos_949_);
lean_dec(v___x_953_);
if (v___x_954_ == 0)
{
lean_dec_ref(v_p_950_);
return v_i_951_;
}
else
{
uint32_t v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; uint8_t v___x_958_; 
v___x_955_ = lean_string_utf8_get(v_s_948_, v_i_951_);
v___x_956_ = lean_box_uint32(v___x_955_);
lean_inc_ref(v_p_950_);
v___x_957_ = lean_apply_1(v_p_950_, v___x_956_);
v___x_958_ = lean_unbox(v___x_957_);
if (v___x_958_ == 0)
{
lean_dec_ref(v_p_950_);
return v_i_951_;
}
else
{
lean_object* v___x_959_; 
v___x_959_ = lean_string_utf8_next(v_s_948_, v_i_951_);
lean_dec(v_i_951_);
v_i_951_ = v___x_959_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___boxed(lean_object* v_s_961_, lean_object* v_stopPos_962_, lean_object* v_p_963_, lean_object* v_i_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Substring_Raw_takeWhileAux(v_s_961_, v_stopPos_962_, v_p_963_, v_i_964_);
lean_dec(v_stopPos_962_);
lean_dec_ref(v_s_961_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhile(lean_object* v_x_966_, lean_object* v_x_967_){
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
lean_object* v_e_974_; lean_object* v___x_976_; 
lean_inc(v_startPos_969_);
v_e_974_ = l_Substring_Raw_takeWhileAux(v_str_968_, v_stopPos_970_, v_x_967_, v_startPos_969_);
lean_dec(v_stopPos_970_);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 2, v_e_974_);
v___x_976_ = v___x_972_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_str_968_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_startPos_969_);
lean_ctor_set(v_reuseFailAlloc_977_, 2, v_e_974_);
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
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(lean_object* v_a_979_, lean_object* v_s_980_, lean_object* v_stopPos_981_, lean_object* v_i_982_){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; uint8_t v___x_985_; 
v___x_983_ = lean_unsigned_to_nat(1u);
v___x_984_ = lean_nat_add(v_i_982_, v___x_983_);
v___x_985_ = lean_nat_dec_le(v___x_984_, v_stopPos_981_);
lean_dec(v___x_984_);
if (v___x_985_ == 0)
{
lean_dec_ref(v_a_979_);
return v_i_982_;
}
else
{
uint32_t v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; uint8_t v___x_989_; 
v___x_986_ = lean_string_utf8_get(v_s_980_, v_i_982_);
v___x_987_ = lean_box_uint32(v___x_986_);
lean_inc_ref(v_a_979_);
v___x_988_ = lean_apply_1(v_a_979_, v___x_987_);
v___x_989_ = lean_unbox(v___x_988_);
if (v___x_989_ == 0)
{
lean_dec_ref(v_a_979_);
return v_i_982_;
}
else
{
lean_object* v___x_990_; 
v___x_990_ = lean_string_utf8_next(v_s_980_, v_i_982_);
lean_dec(v_i_982_);
v_i_982_ = v___x_990_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0___boxed(lean_object* v_a_992_, lean_object* v_s_993_, lean_object* v_stopPos_994_, lean_object* v_i_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(v_a_992_, v_s_993_, v_stopPos_994_, v_i_995_);
lean_dec(v_stopPos_994_);
lean_dec_ref(v_s_993_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* lean_substring_takewhile(lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
lean_object* v_str_999_; lean_object* v_startPos_1000_; lean_object* v_stopPos_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1009_; 
v_str_999_ = lean_ctor_get(v_a_997_, 0);
v_startPos_1000_ = lean_ctor_get(v_a_997_, 1);
v_stopPos_1001_ = lean_ctor_get(v_a_997_, 2);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_a_997_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1003_ = v_a_997_;
v_isShared_1004_ = v_isSharedCheck_1009_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_stopPos_1001_);
lean_inc(v_startPos_1000_);
lean_inc(v_str_999_);
lean_dec(v_a_997_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1009_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v_e_1005_; lean_object* v___x_1007_; 
lean_inc(v_startPos_1000_);
v_e_1005_ = l_Substring_Raw_takeWhileAux___at___00Substring_Raw_Internal_takeWhileImpl_spec__0(v_a_998_, v_str_999_, v_stopPos_1001_, v_startPos_1000_);
lean_dec(v_stopPos_1001_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 2, v_e_1005_);
v___x_1007_ = v___x_1003_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_str_999_);
lean_ctor_set(v_reuseFailAlloc_1008_, 1, v_startPos_1000_);
lean_ctor_set(v_reuseFailAlloc_1008_, 2, v_e_1005_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropWhile(lean_object* v_x_1010_, lean_object* v_x_1011_){
_start:
{
lean_object* v_str_1012_; lean_object* v_startPos_1013_; lean_object* v_stopPos_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1022_; 
v_str_1012_ = lean_ctor_get(v_x_1010_, 0);
v_startPos_1013_ = lean_ctor_get(v_x_1010_, 1);
v_stopPos_1014_ = lean_ctor_get(v_x_1010_, 2);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_x_1010_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1016_ = v_x_1010_;
v_isShared_1017_ = v_isSharedCheck_1022_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_stopPos_1014_);
lean_inc(v_startPos_1013_);
lean_inc(v_str_1012_);
lean_dec(v_x_1010_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1022_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v_b_1018_; lean_object* v___x_1020_; 
v_b_1018_ = l_Substring_Raw_takeWhileAux(v_str_1012_, v_stopPos_1014_, v_x_1011_, v_startPos_1013_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 1, v_b_1018_);
v___x_1020_ = v___x_1016_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_str_1012_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_b_1018_);
lean_ctor_set(v_reuseFailAlloc_1021_, 2, v_stopPos_1014_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux(lean_object* v_s_1023_, lean_object* v_begPos_1024_, lean_object* v_p_1025_, lean_object* v_i_1026_){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; 
v___x_1027_ = lean_unsigned_to_nat(1u);
v___x_1028_ = lean_nat_add(v_begPos_1024_, v___x_1027_);
v___x_1029_ = lean_nat_dec_le(v___x_1028_, v_i_1026_);
lean_dec(v___x_1028_);
if (v___x_1029_ == 0)
{
lean_dec_ref(v_p_1025_);
return v_i_1026_;
}
else
{
lean_object* v_i_x27_1030_; uint32_t v_c_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v_i_x27_1030_ = lean_string_utf8_prev(v_s_1023_, v_i_1026_);
v_c_1031_ = lean_string_utf8_get(v_s_1023_, v_i_x27_1030_);
v___x_1032_ = lean_box_uint32(v_c_1031_);
lean_inc_ref(v_p_1025_);
v___x_1033_ = lean_apply_1(v_p_1025_, v___x_1032_);
v___x_1034_ = lean_unbox(v___x_1033_);
if (v___x_1034_ == 0)
{
lean_dec(v_i_x27_1030_);
lean_dec_ref(v_p_1025_);
return v_i_1026_;
}
else
{
lean_dec(v_i_1026_);
v_i_1026_ = v_i_x27_1030_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux___boxed(lean_object* v_s_1036_, lean_object* v_begPos_1037_, lean_object* v_p_1038_, lean_object* v_i_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Substring_Raw_takeRightWhileAux(v_s_1036_, v_begPos_1037_, v_p_1038_, v_i_1039_);
lean_dec(v_begPos_1037_);
lean_dec_ref(v_s_1036_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhile(lean_object* v_x_1041_, lean_object* v_x_1042_){
_start:
{
lean_object* v_str_1043_; lean_object* v_startPos_1044_; lean_object* v_stopPos_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1053_; 
v_str_1043_ = lean_ctor_get(v_x_1041_, 0);
v_startPos_1044_ = lean_ctor_get(v_x_1041_, 1);
v_stopPos_1045_ = lean_ctor_get(v_x_1041_, 2);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_x_1041_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1047_ = v_x_1041_;
v_isShared_1048_ = v_isSharedCheck_1053_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_stopPos_1045_);
lean_inc(v_startPos_1044_);
lean_inc(v_str_1043_);
lean_dec(v_x_1041_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1053_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v_b_1049_; lean_object* v___x_1051_; 
lean_inc(v_stopPos_1045_);
v_b_1049_ = l_Substring_Raw_takeRightWhileAux(v_str_1043_, v_startPos_1044_, v_x_1042_, v_stopPos_1045_);
lean_dec(v_startPos_1044_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 1, v_b_1049_);
v___x_1051_ = v___x_1047_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_str_1043_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_b_1049_);
lean_ctor_set(v_reuseFailAlloc_1052_, 2, v_stopPos_1045_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropRightWhile(lean_object* v_x_1054_, lean_object* v_x_1055_){
_start:
{
lean_object* v_str_1056_; lean_object* v_startPos_1057_; lean_object* v_stopPos_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1066_; 
v_str_1056_ = lean_ctor_get(v_x_1054_, 0);
v_startPos_1057_ = lean_ctor_get(v_x_1054_, 1);
v_stopPos_1058_ = lean_ctor_get(v_x_1054_, 2);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_x_1054_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1060_ = v_x_1054_;
v_isShared_1061_ = v_isSharedCheck_1066_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_stopPos_1058_);
lean_inc(v_startPos_1057_);
lean_inc(v_str_1056_);
lean_dec(v_x_1054_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1066_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v_e_1062_; lean_object* v___x_1064_; 
v_e_1062_ = l_Substring_Raw_takeRightWhileAux(v_str_1056_, v_startPos_1057_, v_x_1055_, v_stopPos_1058_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 2, v_e_1062_);
v___x_1064_ = v___x_1060_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_str_1056_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v_startPos_1057_);
lean_ctor_set(v_reuseFailAlloc_1065_, 2, v_e_1062_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_trimLeft(lean_object* v_s_1068_){
_start:
{
lean_object* v_str_1069_; lean_object* v_startPos_1070_; lean_object* v_stopPos_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1080_; 
v_str_1069_ = lean_ctor_get(v_s_1068_, 0);
v_startPos_1070_ = lean_ctor_get(v_s_1068_, 1);
v_stopPos_1071_ = lean_ctor_get(v_s_1068_, 2);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_s_1068_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1073_ = v_s_1068_;
v_isShared_1074_ = v_isSharedCheck_1080_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_stopPos_1071_);
lean_inc(v_startPos_1070_);
lean_inc(v_str_1069_);
lean_dec(v_s_1068_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1080_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1075_; lean_object* v_b_1076_; lean_object* v___x_1078_; 
v___x_1075_ = ((lean_object*)(l_Substring_Raw_trimLeft___closed__0));
v_b_1076_ = l_Substring_Raw_takeWhileAux(v_str_1069_, v_stopPos_1071_, v___x_1075_, v_startPos_1070_);
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 1, v_b_1076_);
v___x_1078_ = v___x_1073_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_str_1069_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_b_1076_);
lean_ctor_set(v_reuseFailAlloc_1079_, 2, v_stopPos_1071_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_trimRight(lean_object* v_s_1081_){
_start:
{
lean_object* v_str_1082_; lean_object* v_startPos_1083_; lean_object* v_stopPos_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1093_; 
v_str_1082_ = lean_ctor_get(v_s_1081_, 0);
v_startPos_1083_ = lean_ctor_get(v_s_1081_, 1);
v_stopPos_1084_ = lean_ctor_get(v_s_1081_, 2);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_s_1081_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1086_ = v_s_1081_;
v_isShared_1087_ = v_isSharedCheck_1093_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_stopPos_1084_);
lean_inc(v_startPos_1083_);
lean_inc(v_str_1082_);
lean_dec(v_s_1081_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1093_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1088_; lean_object* v_e_1089_; lean_object* v___x_1091_; 
v___x_1088_ = ((lean_object*)(l_Substring_Raw_trimLeft___closed__0));
v_e_1089_ = l_Substring_Raw_takeRightWhileAux(v_str_1082_, v_startPos_1083_, v___x_1088_, v_stopPos_1084_);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 2, v_e_1089_);
v___x_1091_ = v___x_1086_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_str_1082_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v_startPos_1083_);
lean_ctor_set(v_reuseFailAlloc_1092_, 2, v_e_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_trim(lean_object* v_x_1094_){
_start:
{
lean_object* v_str_1095_; lean_object* v_startPos_1096_; lean_object* v_stopPos_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1107_; 
v_str_1095_ = lean_ctor_get(v_x_1094_, 0);
v_startPos_1096_ = lean_ctor_get(v_x_1094_, 1);
v_stopPos_1097_ = lean_ctor_get(v_x_1094_, 2);
v_isSharedCheck_1107_ = !lean_is_exclusive(v_x_1094_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1099_ = v_x_1094_;
v_isShared_1100_ = v_isSharedCheck_1107_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_stopPos_1097_);
lean_inc(v_startPos_1096_);
lean_inc(v_str_1095_);
lean_dec(v_x_1094_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1107_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1101_; lean_object* v_b_1102_; lean_object* v_e_1103_; lean_object* v___x_1105_; 
v___x_1101_ = ((lean_object*)(l_Substring_Raw_trimLeft___closed__0));
v_b_1102_ = l_Substring_Raw_takeWhileAux(v_str_1095_, v_stopPos_1097_, v___x_1101_, v_startPos_1096_);
v_e_1103_ = l_Substring_Raw_takeRightWhileAux(v_str_1095_, v_b_1102_, v___x_1101_, v_stopPos_1097_);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 2, v_e_1103_);
lean_ctor_set(v___x_1099_, 1, v_b_1102_);
v___x_1105_ = v___x_1099_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_str_1095_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_b_1102_);
lean_ctor_set(v_reuseFailAlloc_1106_, 2, v_e_1103_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___lam__0(lean_object* v___y_1108_, uint8_t v___x_1109_, uint8_t v___x_1110_, lean_object* v_it_1111_, lean_object* v_acc_1112_, lean_object* v_hP_1113_, lean_object* v_recur_1114_){
_start:
{
lean_object* v_str_1115_; lean_object* v_startInclusive_1116_; lean_object* v_endExclusive_1117_; lean_object* v___x_1118_; uint8_t v_decide_1119_; 
v_str_1115_ = lean_ctor_get(v___y_1108_, 0);
v_startInclusive_1116_ = lean_ctor_get(v___y_1108_, 1);
v_endExclusive_1117_ = lean_ctor_get(v___y_1108_, 2);
v___x_1118_ = lean_nat_sub(v_endExclusive_1117_, v_startInclusive_1116_);
v_decide_1119_ = lean_nat_dec_eq(v_it_1111_, v___x_1118_);
lean_dec(v___x_1118_);
if (v_decide_1119_ == 0)
{
lean_object* v_snd_1120_; lean_object* v_snd_1121_; lean_object* v_fst_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1182_; 
v_snd_1120_ = lean_ctor_get(v_acc_1112_, 1);
lean_inc(v_snd_1120_);
v_snd_1121_ = lean_ctor_get(v_snd_1120_, 1);
lean_inc(v_snd_1121_);
v_fst_1122_ = lean_ctor_get(v_acc_1112_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v_acc_1112_);
if (v_isSharedCheck_1182_ == 0)
{
lean_object* v_unused_1183_; 
v_unused_1183_ = lean_ctor_get(v_acc_1112_, 1);
lean_dec(v_unused_1183_);
v___x_1124_ = v_acc_1112_;
v_isShared_1125_ = v_isSharedCheck_1182_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_fst_1122_);
lean_dec(v_acc_1112_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1182_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v_fst_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1180_; 
v_fst_1126_ = lean_ctor_get(v_snd_1120_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v_snd_1120_);
if (v_isSharedCheck_1180_ == 0)
{
lean_object* v_unused_1181_; 
v_unused_1181_ = lean_ctor_get(v_snd_1120_, 1);
lean_dec(v_unused_1181_);
v___x_1128_ = v_snd_1120_;
v_isShared_1129_ = v_isSharedCheck_1180_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_fst_1126_);
lean_dec(v_snd_1120_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1180_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v_snd_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1178_; 
v_snd_1130_ = lean_ctor_get(v_snd_1121_, 1);
v_isSharedCheck_1178_ = !lean_is_exclusive(v_snd_1121_);
if (v_isSharedCheck_1178_ == 0)
{
lean_object* v_unused_1179_; 
v_unused_1179_ = lean_ctor_get(v_snd_1121_, 0);
lean_dec(v_unused_1179_);
v___x_1132_ = v_snd_1121_;
v_isShared_1133_ = v_isSharedCheck_1178_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_snd_1130_);
lean_dec(v_snd_1121_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1178_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1134_; uint32_t v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; uint8_t v___y_1139_; uint8_t v___y_1140_; uint8_t v___y_1158_; uint8_t v___y_1159_; uint8_t v___y_1164_; uint8_t v___y_1165_; uint8_t v___y_1170_; uint32_t v___x_1174_; uint8_t v___x_1175_; 
v___x_1134_ = lean_nat_add(v_startInclusive_1116_, v_it_1111_);
v___x_1135_ = lean_string_utf8_get_fast(v_str_1115_, v___x_1134_);
v___x_1136_ = lean_string_utf8_next_fast(v_str_1115_, v___x_1134_);
lean_dec(v___x_1134_);
v___x_1137_ = lean_nat_sub(v___x_1136_, v_startInclusive_1116_);
v___x_1174_ = 48;
v___x_1175_ = lean_uint32_dec_le(v___x_1174_, v___x_1135_);
if (v___x_1175_ == 0)
{
v___y_1170_ = v___x_1175_;
goto v___jp_1169_;
}
else
{
uint32_t v___x_1176_; uint8_t v___x_1177_; 
v___x_1176_ = 57;
v___x_1177_ = lean_uint32_dec_le(v___x_1135_, v___x_1176_);
v___y_1170_ = v___x_1177_;
goto v___jp_1169_;
}
v___jp_1138_:
{
uint32_t v___x_1141_; uint8_t v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1146_; 
v___x_1141_ = 95;
v___x_1142_ = lean_uint32_dec_eq(v___x_1135_, v___x_1141_);
v___x_1143_ = lean_box(v___y_1139_);
v___x_1144_ = lean_box(v___y_1140_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 1, v___x_1144_);
lean_ctor_set(v___x_1132_, 0, v___x_1143_);
v___x_1146_ = v___x_1132_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1143_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v___x_1144_);
v___x_1146_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1147_; lean_object* v___x_1149_; 
v___x_1147_ = lean_box(v___x_1142_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 1, v___x_1146_);
lean_ctor_set(v___x_1128_, 0, v___x_1147_);
v___x_1149_ = v___x_1128_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1147_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v___x_1146_);
v___x_1149_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
lean_object* v___x_1150_; lean_object* v___x_1152_; 
v___x_1150_ = lean_box(v___x_1109_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 1, v___x_1149_);
lean_ctor_set(v___x_1124_, 0, v___x_1150_);
v___x_1152_ = v___x_1124_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1150_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v___x_1149_);
v___x_1152_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
lean_object* v___x_1153_; 
v___x_1153_ = lean_apply_4(v_recur_1114_, v___x_1137_, v___x_1152_, lean_box(0), lean_box(0));
return v___x_1153_;
}
}
}
}
v___jp_1157_:
{
uint8_t v___x_1160_; 
v___x_1160_ = lean_unbox(v_fst_1126_);
lean_dec(v_fst_1126_);
if (v___x_1160_ == 0)
{
v___y_1139_ = v___y_1158_;
v___y_1140_ = v___y_1159_;
goto v___jp_1138_;
}
else
{
uint32_t v___x_1161_; uint8_t v___x_1162_; 
v___x_1161_ = 95;
v___x_1162_ = lean_uint32_dec_eq(v___x_1135_, v___x_1161_);
if (v___x_1162_ == 0)
{
v___y_1139_ = v___y_1158_;
v___y_1140_ = v___y_1159_;
goto v___jp_1138_;
}
else
{
v___y_1139_ = v___y_1158_;
v___y_1140_ = v___x_1109_;
goto v___jp_1138_;
}
}
}
v___jp_1163_:
{
uint8_t v___x_1166_; 
v___x_1166_ = lean_unbox(v_fst_1122_);
lean_dec(v_fst_1122_);
if (v___x_1166_ == 0)
{
v___y_1158_ = v___y_1164_;
v___y_1159_ = v___y_1165_;
goto v___jp_1157_;
}
else
{
uint32_t v___x_1167_; uint8_t v___x_1168_; 
v___x_1167_ = 95;
v___x_1168_ = lean_uint32_dec_eq(v___x_1135_, v___x_1167_);
if (v___x_1168_ == 0)
{
v___y_1158_ = v___y_1164_;
v___y_1159_ = v___y_1165_;
goto v___jp_1157_;
}
else
{
lean_dec(v_fst_1126_);
v___y_1139_ = v___y_1164_;
v___y_1140_ = v___x_1109_;
goto v___jp_1138_;
}
}
}
v___jp_1169_:
{
uint8_t v___x_1171_; 
v___x_1171_ = lean_unbox(v_snd_1130_);
lean_dec(v_snd_1130_);
if (v___x_1171_ == 0)
{
lean_dec(v_fst_1126_);
lean_dec(v_fst_1122_);
v___y_1139_ = v___y_1170_;
v___y_1140_ = v___x_1109_;
goto v___jp_1138_;
}
else
{
if (v___y_1170_ == 0)
{
uint32_t v___x_1172_; uint8_t v___x_1173_; 
v___x_1172_ = 95;
v___x_1173_ = lean_uint32_dec_eq(v___x_1135_, v___x_1172_);
if (v___x_1173_ == 0)
{
lean_dec(v_fst_1126_);
lean_dec(v_fst_1122_);
v___y_1139_ = v___y_1170_;
v___y_1140_ = v___x_1109_;
goto v___jp_1138_;
}
else
{
v___y_1164_ = v___y_1170_;
v___y_1165_ = v___x_1173_;
goto v___jp_1163_;
}
}
else
{
v___y_1164_ = v___y_1170_;
v___y_1165_ = v___x_1110_;
goto v___jp_1163_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_recur_1114_);
return v_acc_1112_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___lam__0___boxed(lean_object* v___y_1184_, lean_object* v___x_1185_, lean_object* v___x_1186_, lean_object* v_it_1187_, lean_object* v_acc_1188_, lean_object* v_hP_1189_, lean_object* v_recur_1190_){
_start:
{
uint8_t v___x_790__boxed_1191_; uint8_t v___x_791__boxed_1192_; lean_object* v_res_1193_; 
v___x_790__boxed_1191_ = lean_unbox(v___x_1185_);
v___x_791__boxed_1192_ = lean_unbox(v___x_1186_);
v_res_1193_ = l_Substring_Raw_isNat___lam__0(v___y_1184_, v___x_790__boxed_1191_, v___x_791__boxed_1192_, v_it_1187_, v_acc_1188_, v_hP_1189_, v_recur_1190_);
lean_dec(v_it_1187_);
lean_dec_ref(v___y_1184_);
return v_res_1193_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_isNat(lean_object* v_s_1194_){
_start:
{
lean_object* v_str_1195_; lean_object* v_startPos_1196_; lean_object* v_stopPos_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1235_; 
v_str_1195_ = lean_ctor_get(v_s_1194_, 0);
v_startPos_1196_ = lean_ctor_get(v_s_1194_, 1);
v_stopPos_1197_ = lean_ctor_get(v_s_1194_, 2);
v_isSharedCheck_1235_ = !lean_is_exclusive(v_s_1194_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1199_ = v_s_1194_;
v_isShared_1200_ = v_isSharedCheck_1235_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_stopPos_1197_);
lean_inc(v_startPos_1196_);
lean_inc(v_str_1195_);
lean_dec(v_s_1194_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1235_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; uint8_t v___x_1203_; 
v___x_1201_ = lean_nat_sub(v_stopPos_1197_, v_startPos_1196_);
v___x_1202_ = lean_unsigned_to_nat(0u);
v___x_1203_ = lean_nat_dec_eq(v___x_1201_, v___x_1202_);
lean_dec(v___x_1201_);
if (v___x_1203_ == 0)
{
uint8_t v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___y_1213_; lean_object* v___x_1224_; uint8_t v___x_1228_; 
v___x_1204_ = 1;
v___x_1205_ = lean_box(v___x_1203_);
v___x_1206_ = lean_box(v___x_1204_);
v___x_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1205_);
lean_ctor_set(v___x_1207_, 1, v___x_1206_);
v___x_1208_ = lean_box(v___x_1203_);
v___x_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
lean_ctor_set(v___x_1209_, 1, v___x_1207_);
v___x_1210_ = lean_box(v___x_1204_);
v___x_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
lean_ctor_set(v___x_1211_, 1, v___x_1209_);
v___x_1224_ = l_String_instInhabitedSlice;
v___x_1228_ = lean_string_is_valid_pos(v_str_1195_, v_startPos_1196_);
if (v___x_1228_ == 0)
{
lean_del_object(v___x_1199_);
lean_dec(v_stopPos_1197_);
lean_dec(v_startPos_1196_);
lean_dec_ref(v_str_1195_);
goto v___jp_1225_;
}
else
{
uint8_t v___x_1229_; 
v___x_1229_ = lean_string_is_valid_pos(v_str_1195_, v_stopPos_1197_);
if (v___x_1229_ == 0)
{
lean_del_object(v___x_1199_);
lean_dec(v_stopPos_1197_);
lean_dec(v_startPos_1196_);
lean_dec_ref(v_str_1195_);
goto v___jp_1225_;
}
else
{
uint8_t v___x_1230_; 
v___x_1230_ = lean_nat_dec_le(v_startPos_1196_, v_stopPos_1197_);
if (v___x_1230_ == 0)
{
lean_del_object(v___x_1199_);
lean_dec(v_stopPos_1197_);
lean_dec(v_startPos_1196_);
lean_dec_ref(v_str_1195_);
goto v___jp_1225_;
}
else
{
lean_object* v___x_1232_; 
if (v_isShared_1200_ == 0)
{
v___x_1232_ = v___x_1199_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_str_1195_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_startPos_1196_);
lean_ctor_set(v_reuseFailAlloc_1233_, 2, v_stopPos_1197_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
v___y_1213_ = v___x_1232_;
goto v___jp_1212_;
}
}
}
}
v___jp_1212_:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___f_1216_; lean_object* v___x_1217_; lean_object* v_snd_1218_; lean_object* v_snd_1219_; lean_object* v_snd_1220_; uint8_t v___x_1221_; 
v___x_1214_ = lean_box(v___x_1203_);
v___x_1215_ = lean_box(v___x_1204_);
v___f_1216_ = lean_alloc_closure((void*)(l_Substring_Raw_isNat___lam__0___boxed), 7, 3);
lean_closure_set(v___f_1216_, 0, v___y_1213_);
lean_closure_set(v___f_1216_, 1, v___x_1214_);
lean_closure_set(v___f_1216_, 2, v___x_1215_);
v___x_1217_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1216_, v___x_1202_, v___x_1211_, lean_box(0));
v_snd_1218_ = lean_ctor_get(v___x_1217_, 1);
lean_inc(v_snd_1218_);
lean_dec(v___x_1217_);
v_snd_1219_ = lean_ctor_get(v_snd_1218_, 1);
lean_inc(v_snd_1219_);
lean_dec(v_snd_1218_);
v_snd_1220_ = lean_ctor_get(v_snd_1219_, 1);
v___x_1221_ = lean_unbox(v_snd_1220_);
if (v___x_1221_ == 0)
{
lean_dec(v_snd_1219_);
return v___x_1203_;
}
else
{
lean_object* v_fst_1222_; uint8_t v___x_1223_; 
v_fst_1222_ = lean_ctor_get(v_snd_1219_, 0);
lean_inc(v_fst_1222_);
lean_dec(v_snd_1219_);
v___x_1223_ = lean_unbox(v_fst_1222_);
lean_dec(v_fst_1222_);
return v___x_1223_;
}
}
v___jp_1225_:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_1227_ = l_panic___redArg(v___x_1224_, v___x_1226_);
v___y_1213_ = v___x_1227_;
goto v___jp_1212_;
}
}
else
{
uint8_t v___x_1234_; 
lean_del_object(v___x_1199_);
lean_dec(v_stopPos_1197_);
lean_dec(v_startPos_1196_);
lean_dec_ref(v_str_1195_);
v___x_1234_ = 0;
return v___x_1234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_isNat___boxed(lean_object* v_s_1236_){
_start:
{
uint8_t v_res_1237_; lean_object* v_r_1238_; 
v_res_1237_ = l_Substring_Raw_isNat(v_s_1236_);
v_r_1238_ = lean_box(v_res_1237_);
return v_r_1238_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(lean_object* v___y_1239_, lean_object* v_a_1240_, lean_object* v_b_1241_){
_start:
{
lean_object* v_str_1242_; lean_object* v_startInclusive_1243_; lean_object* v_endExclusive_1244_; lean_object* v___x_1245_; uint8_t v_decide_1246_; 
v_str_1242_ = lean_ctor_get(v___y_1239_, 0);
v_startInclusive_1243_ = lean_ctor_get(v___y_1239_, 1);
v_endExclusive_1244_ = lean_ctor_get(v___y_1239_, 2);
v___x_1245_ = lean_nat_sub(v_endExclusive_1244_, v_startInclusive_1243_);
v_decide_1246_ = lean_nat_dec_eq(v_a_1240_, v___x_1245_);
lean_dec(v___x_1245_);
if (v_decide_1246_ == 0)
{
lean_object* v___x_1247_; uint32_t v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; uint32_t v___x_1251_; uint8_t v___x_1252_; 
v___x_1247_ = lean_nat_add(v_startInclusive_1243_, v_a_1240_);
lean_dec(v_a_1240_);
v___x_1248_ = lean_string_utf8_get_fast(v_str_1242_, v___x_1247_);
v___x_1249_ = lean_string_utf8_next_fast(v_str_1242_, v___x_1247_);
lean_dec(v___x_1247_);
v___x_1250_ = lean_nat_sub(v___x_1249_, v_startInclusive_1243_);
v___x_1251_ = 95;
v___x_1252_ = lean_uint32_dec_eq(v___x_1248_, v___x_1251_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1253_ = lean_unsigned_to_nat(10u);
v___x_1254_ = lean_nat_mul(v_b_1241_, v___x_1253_);
lean_dec(v_b_1241_);
v___x_1255_ = lean_uint32_to_nat(v___x_1248_);
v___x_1256_ = lean_unsigned_to_nat(48u);
v___x_1257_ = lean_nat_sub(v___x_1255_, v___x_1256_);
lean_dec(v___x_1255_);
v___x_1258_ = lean_nat_add(v___x_1254_, v___x_1257_);
lean_dec(v___x_1257_);
lean_dec(v___x_1254_);
v_a_1240_ = v___x_1250_;
v_b_1241_ = v___x_1258_;
goto _start;
}
else
{
v_a_1240_ = v___x_1250_;
goto _start;
}
}
else
{
lean_dec(v_a_1240_);
return v_b_1241_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg___boxed(lean_object* v___y_1261_, lean_object* v_a_1262_, lean_object* v_b_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(v___y_1261_, v_a_1262_, v_b_1263_);
lean_dec_ref(v___y_1261_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(lean_object* v___x_1265_, lean_object* v___y_1266_, lean_object* v_a_1267_, lean_object* v_b_1268_){
_start:
{
lean_object* v_str_1269_; lean_object* v_startInclusive_1270_; lean_object* v_endExclusive_1271_; lean_object* v___x_1272_; uint8_t v_decide_1273_; 
v_str_1269_ = lean_ctor_get(v___y_1266_, 0);
v_startInclusive_1270_ = lean_ctor_get(v___y_1266_, 1);
v_endExclusive_1271_ = lean_ctor_get(v___y_1266_, 2);
v___x_1272_ = lean_nat_sub(v_endExclusive_1271_, v_startInclusive_1270_);
v_decide_1273_ = lean_nat_dec_eq(v_a_1267_, v___x_1272_);
lean_dec(v___x_1272_);
if (v_decide_1273_ == 0)
{
lean_object* v_snd_1274_; lean_object* v_snd_1275_; lean_object* v_fst_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1339_; 
v_snd_1274_ = lean_ctor_get(v_b_1268_, 1);
lean_inc(v_snd_1274_);
v_snd_1275_ = lean_ctor_get(v_snd_1274_, 1);
lean_inc(v_snd_1275_);
v_fst_1276_ = lean_ctor_get(v_b_1268_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v_b_1268_);
if (v_isSharedCheck_1339_ == 0)
{
lean_object* v_unused_1340_; 
v_unused_1340_ = lean_ctor_get(v_b_1268_, 1);
lean_dec(v_unused_1340_);
v___x_1278_ = v_b_1268_;
v_isShared_1279_ = v_isSharedCheck_1339_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_fst_1276_);
lean_dec(v_b_1268_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1339_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v_fst_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1337_; 
v_fst_1280_ = lean_ctor_get(v_snd_1274_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_snd_1274_);
if (v_isSharedCheck_1337_ == 0)
{
lean_object* v_unused_1338_; 
v_unused_1338_ = lean_ctor_get(v_snd_1274_, 1);
lean_dec(v_unused_1338_);
v___x_1282_ = v_snd_1274_;
v_isShared_1283_ = v_isSharedCheck_1337_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_fst_1280_);
lean_dec(v_snd_1274_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1337_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v_snd_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1335_; 
v_snd_1284_ = lean_ctor_get(v_snd_1275_, 1);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_snd_1275_);
if (v_isSharedCheck_1335_ == 0)
{
lean_object* v_unused_1336_; 
v_unused_1336_ = lean_ctor_get(v_snd_1275_, 0);
lean_dec(v_unused_1336_);
v___x_1286_ = v_snd_1275_;
v_isShared_1287_ = v_isSharedCheck_1335_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_snd_1284_);
lean_dec(v_snd_1275_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1335_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1288_; uint8_t v___x_1289_; uint8_t v___x_1290_; lean_object* v___x_1291_; uint32_t v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; uint8_t v___y_1296_; uint8_t v___y_1297_; uint8_t v___y_1315_; uint8_t v___y_1316_; uint8_t v___y_1321_; uint8_t v___y_1322_; uint8_t v___y_1327_; uint32_t v___x_1331_; uint8_t v___x_1332_; 
v___x_1288_ = lean_unsigned_to_nat(0u);
v___x_1289_ = lean_nat_dec_eq(v___x_1265_, v___x_1288_);
v___x_1290_ = 1;
v___x_1291_ = lean_nat_add(v_startInclusive_1270_, v_a_1267_);
lean_dec(v_a_1267_);
v___x_1292_ = lean_string_utf8_get_fast(v_str_1269_, v___x_1291_);
v___x_1293_ = lean_string_utf8_next_fast(v_str_1269_, v___x_1291_);
lean_dec(v___x_1291_);
v___x_1294_ = lean_nat_sub(v___x_1293_, v_startInclusive_1270_);
v___x_1331_ = 48;
v___x_1332_ = lean_uint32_dec_le(v___x_1331_, v___x_1292_);
if (v___x_1332_ == 0)
{
v___y_1327_ = v___x_1332_;
goto v___jp_1326_;
}
else
{
uint32_t v___x_1333_; uint8_t v___x_1334_; 
v___x_1333_ = 57;
v___x_1334_ = lean_uint32_dec_le(v___x_1292_, v___x_1333_);
v___y_1327_ = v___x_1334_;
goto v___jp_1326_;
}
v___jp_1295_:
{
uint32_t v___x_1298_; uint8_t v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1303_; 
v___x_1298_ = 95;
v___x_1299_ = lean_uint32_dec_eq(v___x_1292_, v___x_1298_);
v___x_1300_ = lean_box(v___y_1296_);
v___x_1301_ = lean_box(v___y_1297_);
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 1, v___x_1301_);
lean_ctor_set(v___x_1286_, 0, v___x_1300_);
v___x_1303_ = v___x_1286_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1300_);
lean_ctor_set(v_reuseFailAlloc_1313_, 1, v___x_1301_);
v___x_1303_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v___x_1304_; lean_object* v___x_1306_; 
v___x_1304_ = lean_box(v___x_1299_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 1, v___x_1303_);
lean_ctor_set(v___x_1282_, 0, v___x_1304_);
v___x_1306_ = v___x_1282_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1304_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v___x_1303_);
v___x_1306_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
lean_object* v___x_1307_; lean_object* v___x_1309_; 
v___x_1307_ = lean_box(v___x_1289_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 1, v___x_1306_);
lean_ctor_set(v___x_1278_, 0, v___x_1307_);
v___x_1309_ = v___x_1278_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v___x_1306_);
v___x_1309_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
v_a_1267_ = v___x_1294_;
v_b_1268_ = v___x_1309_;
goto _start;
}
}
}
}
v___jp_1314_:
{
uint8_t v___x_1317_; 
v___x_1317_ = lean_unbox(v_fst_1280_);
lean_dec(v_fst_1280_);
if (v___x_1317_ == 0)
{
v___y_1296_ = v___y_1315_;
v___y_1297_ = v___y_1316_;
goto v___jp_1295_;
}
else
{
uint32_t v___x_1318_; uint8_t v___x_1319_; 
v___x_1318_ = 95;
v___x_1319_ = lean_uint32_dec_eq(v___x_1292_, v___x_1318_);
if (v___x_1319_ == 0)
{
v___y_1296_ = v___y_1315_;
v___y_1297_ = v___y_1316_;
goto v___jp_1295_;
}
else
{
v___y_1296_ = v___y_1315_;
v___y_1297_ = v___x_1289_;
goto v___jp_1295_;
}
}
}
v___jp_1320_:
{
uint8_t v___x_1323_; 
v___x_1323_ = lean_unbox(v_fst_1276_);
lean_dec(v_fst_1276_);
if (v___x_1323_ == 0)
{
v___y_1315_ = v___y_1321_;
v___y_1316_ = v___y_1322_;
goto v___jp_1314_;
}
else
{
uint32_t v___x_1324_; uint8_t v___x_1325_; 
v___x_1324_ = 95;
v___x_1325_ = lean_uint32_dec_eq(v___x_1292_, v___x_1324_);
if (v___x_1325_ == 0)
{
v___y_1315_ = v___y_1321_;
v___y_1316_ = v___y_1322_;
goto v___jp_1314_;
}
else
{
lean_dec(v_fst_1280_);
v___y_1296_ = v___y_1321_;
v___y_1297_ = v___x_1289_;
goto v___jp_1295_;
}
}
}
v___jp_1326_:
{
uint8_t v___x_1328_; 
v___x_1328_ = lean_unbox(v_snd_1284_);
lean_dec(v_snd_1284_);
if (v___x_1328_ == 0)
{
lean_dec(v_fst_1280_);
lean_dec(v_fst_1276_);
v___y_1296_ = v___y_1327_;
v___y_1297_ = v___x_1289_;
goto v___jp_1295_;
}
else
{
if (v___y_1327_ == 0)
{
uint32_t v___x_1329_; uint8_t v___x_1330_; 
v___x_1329_ = 95;
v___x_1330_ = lean_uint32_dec_eq(v___x_1292_, v___x_1329_);
if (v___x_1330_ == 0)
{
lean_dec(v_fst_1280_);
lean_dec(v_fst_1276_);
v___y_1296_ = v___y_1327_;
v___y_1297_ = v___x_1289_;
goto v___jp_1295_;
}
else
{
v___y_1321_ = v___y_1327_;
v___y_1322_ = v___x_1330_;
goto v___jp_1320_;
}
}
else
{
v___y_1321_ = v___y_1327_;
v___y_1322_ = v___x_1290_;
goto v___jp_1320_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1267_);
return v_b_1268_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg___boxed(lean_object* v___x_1341_, lean_object* v___y_1342_, lean_object* v_a_1343_, lean_object* v_b_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(v___x_1341_, v___y_1342_, v_a_1343_, v_b_1344_);
lean_dec_ref(v___y_1342_);
lean_dec(v___x_1341_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toNat_x3f(lean_object* v_s_1346_){
_start:
{
lean_object* v_str_1347_; lean_object* v_startPos_1348_; lean_object* v_stopPos_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1396_; 
v_str_1347_ = lean_ctor_get(v_s_1346_, 0);
v_startPos_1348_ = lean_ctor_get(v_s_1346_, 1);
v_stopPos_1349_ = lean_ctor_get(v_s_1346_, 2);
v_isSharedCheck_1396_ = !lean_is_exclusive(v_s_1346_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1351_ = v_s_1346_;
v_isShared_1352_ = v_isSharedCheck_1396_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_stopPos_1349_);
lean_inc(v_startPos_1348_);
lean_inc(v_str_1347_);
lean_dec(v_s_1346_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1396_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___y_1356_; uint8_t v___x_1362_; 
v___x_1353_ = lean_nat_sub(v_stopPos_1349_, v_startPos_1348_);
v___x_1354_ = lean_unsigned_to_nat(0u);
v___x_1362_ = lean_nat_dec_eq(v___x_1353_, v___x_1354_);
if (v___x_1362_ == 0)
{
uint8_t v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___y_1372_; uint8_t v___x_1391_; 
v___x_1363_ = 1;
v___x_1364_ = lean_box(v___x_1362_);
v___x_1365_ = lean_box(v___x_1363_);
v___x_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1364_);
lean_ctor_set(v___x_1366_, 1, v___x_1365_);
v___x_1367_ = lean_box(v___x_1362_);
v___x_1368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
lean_ctor_set(v___x_1368_, 1, v___x_1366_);
v___x_1369_ = lean_box(v___x_1363_);
v___x_1370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1369_);
lean_ctor_set(v___x_1370_, 1, v___x_1368_);
v___x_1391_ = lean_string_is_valid_pos(v_str_1347_, v_startPos_1348_);
if (v___x_1391_ == 0)
{
goto v___jp_1388_;
}
else
{
uint8_t v___x_1392_; 
v___x_1392_ = lean_string_is_valid_pos(v_str_1347_, v_stopPos_1349_);
if (v___x_1392_ == 0)
{
goto v___jp_1388_;
}
else
{
uint8_t v___x_1393_; 
v___x_1393_ = lean_nat_dec_le(v_startPos_1348_, v_stopPos_1349_);
if (v___x_1393_ == 0)
{
goto v___jp_1388_;
}
else
{
lean_object* v___x_1394_; 
lean_inc(v_stopPos_1349_);
lean_inc(v_startPos_1348_);
lean_inc_ref(v_str_1347_);
v___x_1394_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1394_, 0, v_str_1347_);
lean_ctor_set(v___x_1394_, 1, v_startPos_1348_);
lean_ctor_set(v___x_1394_, 2, v_stopPos_1349_);
v___y_1372_ = v___x_1394_;
goto v___jp_1371_;
}
}
}
v___jp_1371_:
{
lean_object* v___x_1373_; lean_object* v_snd_1374_; lean_object* v_snd_1375_; lean_object* v_snd_1376_; uint8_t v___x_1377_; 
v___x_1373_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(v___x_1353_, v___y_1372_, v___x_1354_, v___x_1370_);
lean_dec_ref(v___y_1372_);
lean_dec(v___x_1353_);
v_snd_1374_ = lean_ctor_get(v___x_1373_, 1);
lean_inc(v_snd_1374_);
lean_dec_ref(v___x_1373_);
v_snd_1375_ = lean_ctor_get(v_snd_1374_, 1);
lean_inc(v_snd_1375_);
lean_dec(v_snd_1374_);
v_snd_1376_ = lean_ctor_get(v_snd_1375_, 1);
v___x_1377_ = lean_unbox(v_snd_1376_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; 
lean_dec(v_snd_1375_);
lean_del_object(v___x_1351_);
lean_dec(v_stopPos_1349_);
lean_dec(v_startPos_1348_);
lean_dec_ref(v_str_1347_);
v___x_1378_ = lean_box(0);
return v___x_1378_;
}
else
{
lean_object* v_fst_1379_; uint8_t v___x_1380_; 
v_fst_1379_ = lean_ctor_get(v_snd_1375_, 0);
lean_inc(v_fst_1379_);
lean_dec(v_snd_1375_);
v___x_1380_ = lean_unbox(v_fst_1379_);
lean_dec(v_fst_1379_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; 
lean_del_object(v___x_1351_);
lean_dec(v_stopPos_1349_);
lean_dec(v_startPos_1348_);
lean_dec_ref(v_str_1347_);
v___x_1381_ = lean_box(0);
return v___x_1381_;
}
else
{
uint8_t v___x_1382_; 
v___x_1382_ = lean_string_is_valid_pos(v_str_1347_, v_startPos_1348_);
if (v___x_1382_ == 0)
{
lean_del_object(v___x_1351_);
lean_dec(v_stopPos_1349_);
lean_dec(v_startPos_1348_);
lean_dec_ref(v_str_1347_);
goto v___jp_1359_;
}
else
{
uint8_t v___x_1383_; 
v___x_1383_ = lean_string_is_valid_pos(v_str_1347_, v_stopPos_1349_);
if (v___x_1383_ == 0)
{
lean_del_object(v___x_1351_);
lean_dec(v_stopPos_1349_);
lean_dec(v_startPos_1348_);
lean_dec_ref(v_str_1347_);
goto v___jp_1359_;
}
else
{
uint8_t v___x_1384_; 
v___x_1384_ = lean_nat_dec_le(v_startPos_1348_, v_stopPos_1349_);
if (v___x_1384_ == 0)
{
lean_del_object(v___x_1351_);
lean_dec(v_stopPos_1349_);
lean_dec(v_startPos_1348_);
lean_dec_ref(v_str_1347_);
goto v___jp_1359_;
}
else
{
lean_object* v___x_1386_; 
if (v_isShared_1352_ == 0)
{
v___x_1386_ = v___x_1351_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_str_1347_);
lean_ctor_set(v_reuseFailAlloc_1387_, 1, v_startPos_1348_);
lean_ctor_set(v_reuseFailAlloc_1387_, 2, v_stopPos_1349_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
v___y_1356_ = v___x_1386_;
goto v___jp_1355_;
}
}
}
}
}
}
}
v___jp_1388_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1389_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_1390_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_1389_);
v___y_1372_ = v___x_1390_;
goto v___jp_1371_;
}
}
else
{
lean_object* v___x_1395_; 
lean_dec(v___x_1353_);
lean_del_object(v___x_1351_);
lean_dec(v_stopPos_1349_);
lean_dec(v_startPos_1348_);
lean_dec_ref(v_str_1347_);
v___x_1395_ = lean_box(0);
return v___x_1395_;
}
v___jp_1355_:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1357_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(v___y_1356_, v___x_1354_, v___x_1354_);
lean_dec_ref(v___y_1356_);
v___x_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
return v___x_1358_;
}
v___jp_1359_:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = lean_obj_once(&l_Substring_Raw_foldl___redArg___closed__3, &l_Substring_Raw_foldl___redArg___closed__3_once, _init_l_Substring_Raw_foldl___redArg___closed__3);
v___x_1361_ = l_panic___at___00Substring_Raw_Internal_allImpl_spec__1(v___x_1360_);
v___y_1356_ = v___x_1361_;
goto v___jp_1355_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0(lean_object* v___x_1397_, lean_object* v___y_1398_, lean_object* v_inst_1399_, lean_object* v_R_1400_, lean_object* v_a_1401_, lean_object* v_b_1402_, lean_object* v_c_1403_){
_start:
{
lean_object* v___x_1404_; 
v___x_1404_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___redArg(v___x_1397_, v___y_1398_, v_a_1401_, v_b_1402_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0___boxed(lean_object* v___x_1405_, lean_object* v___y_1406_, lean_object* v_inst_1407_, lean_object* v_R_1408_, lean_object* v_a_1409_, lean_object* v_b_1410_, lean_object* v_c_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__0(v___x_1405_, v___y_1406_, v_inst_1407_, v_R_1408_, v_a_1409_, v_b_1410_, v_c_1411_);
lean_dec_ref(v___y_1406_);
lean_dec(v___x_1405_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1(lean_object* v___y_1413_, lean_object* v_inst_1414_, lean_object* v_R_1415_, lean_object* v_a_1416_, lean_object* v_b_1417_, lean_object* v_c_1418_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___redArg(v___y_1413_, v_a_1416_, v_b_1417_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1___boxed(lean_object* v___y_1420_, lean_object* v_inst_1421_, lean_object* v_R_1422_, lean_object* v_a_1423_, lean_object* v_b_1424_, lean_object* v_c_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_WellFounded_opaqueFix_u2083___at___00Substring_Raw_toNat_x3f_spec__1(v___y_1420_, v_inst_1421_, v_R_1422_, v_a_1423_, v_b_1424_, v_c_1425_);
lean_dec_ref(v___y_1420_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_repair(lean_object* v_x_1427_){
_start:
{
lean_object* v_str_1428_; lean_object* v_startPos_1429_; lean_object* v_stopPos_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1446_; 
v_str_1428_ = lean_ctor_get(v_x_1427_, 0);
v_startPos_1429_ = lean_ctor_get(v_x_1427_, 1);
v_stopPos_1430_ = lean_ctor_get(v_x_1427_, 2);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_x_1427_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1432_ = v_x_1427_;
v_isShared_1433_ = v_isSharedCheck_1446_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_stopPos_1430_);
lean_inc(v_startPos_1429_);
lean_inc(v_str_1428_);
lean_dec(v_x_1427_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1446_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___y_1435_; uint8_t v___x_1444_; 
v___x_1444_ = lean_string_is_valid_pos(v_str_1428_, v_startPos_1429_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; 
lean_dec(v_startPos_1429_);
v___x_1445_ = lean_string_utf8_byte_size(v_str_1428_);
v___y_1435_ = v___x_1445_;
goto v___jp_1434_;
}
else
{
v___y_1435_ = v_startPos_1429_;
goto v___jp_1434_;
}
v___jp_1434_:
{
uint8_t v___x_1436_; 
v___x_1436_ = lean_string_is_valid_pos(v_str_1428_, v_stopPos_1430_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; lean_object* v___x_1439_; 
lean_dec(v_stopPos_1430_);
v___x_1437_ = lean_string_utf8_byte_size(v_str_1428_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 2, v___x_1437_);
lean_ctor_set(v___x_1432_, 1, v___y_1435_);
v___x_1439_ = v___x_1432_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_str_1428_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v___y_1435_);
lean_ctor_set(v_reuseFailAlloc_1440_, 2, v___x_1437_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
else
{
lean_object* v___x_1442_; 
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 1, v___y_1435_);
v___x_1442_ = v___x_1432_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_str_1428_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v___y_1435_);
lean_ctor_set(v_reuseFailAlloc_1443_, 2, v_stopPos_1430_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_beq(lean_object* v_ss1_1447_, lean_object* v_ss2_1448_){
_start:
{
lean_object* v_ss1_1449_; lean_object* v_str_1450_; lean_object* v_startPos_1451_; lean_object* v_stopPos_1452_; lean_object* v_ss2_1453_; lean_object* v_str_1454_; lean_object* v_startPos_1455_; lean_object* v_stopPos_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; uint8_t v___x_1459_; 
v_ss1_1449_ = l_Substring_Raw_repair(v_ss1_1447_);
v_str_1450_ = lean_ctor_get(v_ss1_1449_, 0);
lean_inc_ref(v_str_1450_);
v_startPos_1451_ = lean_ctor_get(v_ss1_1449_, 1);
lean_inc(v_startPos_1451_);
v_stopPos_1452_ = lean_ctor_get(v_ss1_1449_, 2);
lean_inc(v_stopPos_1452_);
lean_dec_ref(v_ss1_1449_);
v_ss2_1453_ = l_Substring_Raw_repair(v_ss2_1448_);
v_str_1454_ = lean_ctor_get(v_ss2_1453_, 0);
lean_inc_ref(v_str_1454_);
v_startPos_1455_ = lean_ctor_get(v_ss2_1453_, 1);
lean_inc(v_startPos_1455_);
v_stopPos_1456_ = lean_ctor_get(v_ss2_1453_, 2);
lean_inc(v_stopPos_1456_);
lean_dec_ref(v_ss2_1453_);
v___x_1457_ = lean_nat_sub(v_stopPos_1452_, v_startPos_1451_);
lean_dec(v_stopPos_1452_);
v___x_1458_ = lean_nat_sub(v_stopPos_1456_, v_startPos_1455_);
lean_dec(v_stopPos_1456_);
v___x_1459_ = lean_nat_dec_eq(v___x_1457_, v___x_1458_);
lean_dec(v___x_1458_);
if (v___x_1459_ == 0)
{
lean_dec(v___x_1457_);
lean_dec(v_startPos_1455_);
lean_dec_ref(v_str_1454_);
lean_dec(v_startPos_1451_);
lean_dec_ref(v_str_1450_);
return v___x_1459_;
}
else
{
uint8_t v___x_1460_; 
v___x_1460_ = l_String_Pos_Raw_substrEq(v_str_1450_, v_startPos_1451_, v_str_1454_, v_startPos_1455_, v___x_1457_);
lean_dec(v___x_1457_);
lean_dec_ref(v_str_1454_);
lean_dec_ref(v_str_1450_);
return v___x_1460_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_beq___boxed(lean_object* v_ss1_1461_, lean_object* v_ss2_1462_){
_start:
{
uint8_t v_res_1463_; lean_object* v_r_1464_; 
v_res_1463_ = l_Substring_Raw_beq(v_ss1_1461_, v_ss2_1462_);
v_r_1464_ = lean_box(v_res_1463_);
return v_r_1464_;
}
}
LEAN_EXPORT uint8_t lean_substring_beq(lean_object* v_ss1_1465_, lean_object* v_ss2_1466_){
_start:
{
uint8_t v___x_1467_; 
v___x_1467_ = l_Substring_Raw_beq(v_ss1_1465_, v_ss2_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_Internal_beqImpl___boxed(lean_object* v_ss1_1468_, lean_object* v_ss2_1469_){
_start:
{
uint8_t v_res_1470_; lean_object* v_r_1471_; 
v_res_1470_ = lean_substring_beq(v_ss1_1468_, v_ss2_1469_);
v_r_1471_ = lean_box(v_res_1470_);
return v_r_1471_;
}
}
LEAN_EXPORT uint8_t l_Substring_Raw_sameAs(lean_object* v_ss1_1474_, lean_object* v_ss2_1475_){
_start:
{
lean_object* v_startPos_1476_; lean_object* v_startPos_1477_; uint8_t v_decide_1478_; 
v_startPos_1476_ = lean_ctor_get(v_ss1_1474_, 1);
v_startPos_1477_ = lean_ctor_get(v_ss2_1475_, 1);
v_decide_1478_ = lean_nat_dec_eq(v_startPos_1476_, v_startPos_1477_);
if (v_decide_1478_ == 0)
{
lean_dec_ref(v_ss2_1475_);
lean_dec_ref(v_ss1_1474_);
return v_decide_1478_;
}
else
{
uint8_t v___x_1479_; 
v___x_1479_ = l_Substring_Raw_beq(v_ss1_1474_, v_ss2_1475_);
return v___x_1479_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_sameAs___boxed(lean_object* v_ss1_1480_, lean_object* v_ss2_1481_){
_start:
{
uint8_t v_res_1482_; lean_object* v_r_1483_; 
v_res_1482_ = l_Substring_Raw_sameAs(v_ss1_1480_, v_ss2_1481_);
v_r_1483_ = lean_box(v_res_1482_);
return v_r_1483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(lean_object* v_s_1484_, lean_object* v_t_1485_, lean_object* v_spos_1486_, lean_object* v_tpos_1487_){
_start:
{
lean_object* v_str_1488_; lean_object* v_stopPos_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; uint8_t v___x_1492_; 
v_str_1488_ = lean_ctor_get(v_s_1484_, 0);
v_stopPos_1489_ = lean_ctor_get(v_s_1484_, 2);
v___x_1490_ = lean_unsigned_to_nat(1u);
v___x_1491_ = lean_nat_add(v_spos_1486_, v___x_1490_);
v___x_1492_ = lean_nat_dec_le(v___x_1491_, v_stopPos_1489_);
lean_dec(v___x_1491_);
if (v___x_1492_ == 0)
{
lean_dec(v_tpos_1487_);
return v_spos_1486_;
}
else
{
lean_object* v_str_1493_; lean_object* v_stopPos_1494_; lean_object* v___x_1495_; uint8_t v___x_1496_; 
v_str_1493_ = lean_ctor_get(v_t_1485_, 0);
v_stopPos_1494_ = lean_ctor_get(v_t_1485_, 2);
v___x_1495_ = lean_nat_add(v_tpos_1487_, v___x_1490_);
v___x_1496_ = lean_nat_dec_le(v___x_1495_, v_stopPos_1494_);
lean_dec(v___x_1495_);
if (v___x_1496_ == 0)
{
lean_dec(v_tpos_1487_);
return v_spos_1486_;
}
else
{
uint32_t v___x_1497_; uint32_t v___x_1498_; uint8_t v___x_1499_; 
v___x_1497_ = lean_string_utf8_get(v_str_1488_, v_spos_1486_);
v___x_1498_ = lean_string_utf8_get(v_str_1493_, v_tpos_1487_);
v___x_1499_ = lean_uint32_dec_eq(v___x_1497_, v___x_1498_);
if (v___x_1499_ == 0)
{
lean_dec(v_tpos_1487_);
return v_spos_1486_;
}
else
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = lean_string_utf8_next(v_str_1488_, v_spos_1486_);
lean_dec(v_spos_1486_);
v___x_1501_ = lean_string_utf8_next(v_str_1493_, v_tpos_1487_);
lean_dec(v_tpos_1487_);
v_spos_1486_ = v___x_1500_;
v_tpos_1487_ = v___x_1501_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop___boxed(lean_object* v_s_1503_, lean_object* v_t_1504_, lean_object* v_spos_1505_, lean_object* v_tpos_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(v_s_1503_, v_t_1504_, v_spos_1505_, v_tpos_1506_);
lean_dec_ref(v_t_1504_);
lean_dec_ref(v_s_1503_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_commonPrefix(lean_object* v_s_1508_, lean_object* v_t_1509_){
_start:
{
lean_object* v_str_1510_; lean_object* v_startPos_1511_; lean_object* v_startPos_1512_; lean_object* v___x_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
v_str_1510_ = lean_ctor_get(v_s_1508_, 0);
lean_inc_ref(v_str_1510_);
v_startPos_1511_ = lean_ctor_get(v_s_1508_, 1);
lean_inc_n(v_startPos_1511_, 2);
v_startPos_1512_ = lean_ctor_get(v_t_1509_, 1);
lean_inc(v_startPos_1512_);
v___x_1513_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonPrefix_loop(v_s_1508_, v_t_1509_, v_startPos_1511_, v_startPos_1512_);
lean_dec_ref(v_s_1508_);
v_isSharedCheck_1520_ = !lean_is_exclusive(v_t_1509_);
if (v_isSharedCheck_1520_ == 0)
{
lean_object* v_unused_1521_; lean_object* v_unused_1522_; lean_object* v_unused_1523_; 
v_unused_1521_ = lean_ctor_get(v_t_1509_, 2);
lean_dec(v_unused_1521_);
v_unused_1522_ = lean_ctor_get(v_t_1509_, 1);
lean_dec(v_unused_1522_);
v_unused_1523_ = lean_ctor_get(v_t_1509_, 0);
lean_dec(v_unused_1523_);
v___x_1515_ = v_t_1509_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_dec(v_t_1509_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 2, v___x_1513_);
lean_ctor_set(v___x_1515_, 1, v_startPos_1511_);
lean_ctor_set(v___x_1515_, 0, v_str_1510_);
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_str_1510_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v_startPos_1511_);
lean_ctor_set(v_reuseFailAlloc_1519_, 2, v___x_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(lean_object* v_s_1524_, lean_object* v_t_1525_, lean_object* v_spos_1526_, lean_object* v_tpos_1527_){
_start:
{
lean_object* v_str_1528_; lean_object* v_startPos_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; uint8_t v___x_1532_; 
v_str_1528_ = lean_ctor_get(v_s_1524_, 0);
v_startPos_1529_ = lean_ctor_get(v_s_1524_, 1);
v___x_1530_ = lean_unsigned_to_nat(1u);
v___x_1531_ = lean_nat_add(v_startPos_1529_, v___x_1530_);
v___x_1532_ = lean_nat_dec_le(v___x_1531_, v_spos_1526_);
lean_dec(v___x_1531_);
if (v___x_1532_ == 0)
{
lean_dec(v_tpos_1527_);
return v_spos_1526_;
}
else
{
lean_object* v_str_1533_; lean_object* v_startPos_1534_; lean_object* v___x_1535_; uint8_t v___x_1536_; 
v_str_1533_ = lean_ctor_get(v_t_1525_, 0);
v_startPos_1534_ = lean_ctor_get(v_t_1525_, 1);
v___x_1535_ = lean_nat_add(v_startPos_1534_, v___x_1530_);
v___x_1536_ = lean_nat_dec_le(v___x_1535_, v_tpos_1527_);
lean_dec(v___x_1535_);
if (v___x_1536_ == 0)
{
lean_dec(v_tpos_1527_);
return v_spos_1526_;
}
else
{
lean_object* v_spos_x27_1537_; lean_object* v_tpos_x27_1538_; uint32_t v___x_1539_; uint32_t v___x_1540_; uint8_t v___x_1541_; 
v_spos_x27_1537_ = lean_string_utf8_prev(v_str_1528_, v_spos_1526_);
v_tpos_x27_1538_ = lean_string_utf8_prev(v_str_1533_, v_tpos_1527_);
lean_dec(v_tpos_1527_);
v___x_1539_ = lean_string_utf8_get(v_str_1528_, v_spos_x27_1537_);
v___x_1540_ = lean_string_utf8_get(v_str_1533_, v_tpos_x27_1538_);
v___x_1541_ = lean_uint32_dec_eq(v___x_1539_, v___x_1540_);
if (v___x_1541_ == 0)
{
lean_dec(v_tpos_x27_1538_);
lean_dec(v_spos_x27_1537_);
return v_spos_1526_;
}
else
{
lean_dec(v_spos_1526_);
v_spos_1526_ = v_spos_x27_1537_;
v_tpos_1527_ = v_tpos_x27_1538_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop___boxed(lean_object* v_s_1543_, lean_object* v_t_1544_, lean_object* v_spos_1545_, lean_object* v_tpos_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(v_s_1543_, v_t_1544_, v_spos_1545_, v_tpos_1546_);
lean_dec_ref(v_t_1544_);
lean_dec_ref(v_s_1543_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_commonSuffix(lean_object* v_s_1548_, lean_object* v_t_1549_){
_start:
{
lean_object* v_str_1550_; lean_object* v_stopPos_1551_; lean_object* v_stopPos_1552_; lean_object* v___x_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
v_str_1550_ = lean_ctor_get(v_s_1548_, 0);
lean_inc_ref(v_str_1550_);
v_stopPos_1551_ = lean_ctor_get(v_s_1548_, 2);
lean_inc_n(v_stopPos_1551_, 2);
v_stopPos_1552_ = lean_ctor_get(v_t_1549_, 2);
lean_inc(v_stopPos_1552_);
v___x_1553_ = l___private_Init_Data_String_Substring_0__Substring_Raw_commonSuffix_loop(v_s_1548_, v_t_1549_, v_stopPos_1551_, v_stopPos_1552_);
lean_dec_ref(v_s_1548_);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_t_1549_);
if (v_isSharedCheck_1560_ == 0)
{
lean_object* v_unused_1561_; lean_object* v_unused_1562_; lean_object* v_unused_1563_; 
v_unused_1561_ = lean_ctor_get(v_t_1549_, 2);
lean_dec(v_unused_1561_);
v_unused_1562_ = lean_ctor_get(v_t_1549_, 1);
lean_dec(v_unused_1562_);
v_unused_1563_ = lean_ctor_get(v_t_1549_, 0);
lean_dec(v_unused_1563_);
v___x_1555_ = v_t_1549_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_dec(v_t_1549_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 2, v_stopPos_1551_);
lean_ctor_set(v___x_1555_, 1, v___x_1553_);
lean_ctor_set(v___x_1555_, 0, v_str_1550_);
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_str_1550_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v___x_1553_);
lean_ctor_set(v_reuseFailAlloc_1559_, 2, v_stopPos_1551_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropPrefix_x3f(lean_object* v_s_1564_, lean_object* v_pre_1565_){
_start:
{
lean_object* v_t_1566_; lean_object* v_startPos_1567_; lean_object* v_stopPos_1568_; lean_object* v_startPos_1569_; lean_object* v_stopPos_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; uint8_t v___x_1573_; 
lean_inc_ref(v_pre_1565_);
lean_inc_ref(v_s_1564_);
v_t_1566_ = l_Substring_Raw_commonPrefix(v_s_1564_, v_pre_1565_);
v_startPos_1567_ = lean_ctor_get(v_t_1566_, 1);
lean_inc(v_startPos_1567_);
v_stopPos_1568_ = lean_ctor_get(v_t_1566_, 2);
lean_inc(v_stopPos_1568_);
lean_dec_ref(v_t_1566_);
v_startPos_1569_ = lean_ctor_get(v_pre_1565_, 1);
lean_inc(v_startPos_1569_);
v_stopPos_1570_ = lean_ctor_get(v_pre_1565_, 2);
lean_inc(v_stopPos_1570_);
lean_dec_ref(v_pre_1565_);
v___x_1571_ = lean_nat_sub(v_stopPos_1568_, v_startPos_1567_);
lean_dec(v_startPos_1567_);
v___x_1572_ = lean_nat_sub(v_stopPos_1570_, v_startPos_1569_);
lean_dec(v_startPos_1569_);
lean_dec(v_stopPos_1570_);
v___x_1573_ = lean_nat_dec_eq(v___x_1571_, v___x_1572_);
lean_dec(v___x_1572_);
lean_dec(v___x_1571_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; 
lean_dec(v_stopPos_1568_);
lean_dec_ref(v_s_1564_);
v___x_1574_ = lean_box(0);
return v___x_1574_;
}
else
{
lean_object* v_str_1575_; lean_object* v_stopPos_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1584_; 
v_str_1575_ = lean_ctor_get(v_s_1564_, 0);
v_stopPos_1576_ = lean_ctor_get(v_s_1564_, 2);
v_isSharedCheck_1584_ = !lean_is_exclusive(v_s_1564_);
if (v_isSharedCheck_1584_ == 0)
{
lean_object* v_unused_1585_; 
v_unused_1585_ = lean_ctor_get(v_s_1564_, 1);
lean_dec(v_unused_1585_);
v___x_1578_ = v_s_1564_;
v_isShared_1579_ = v_isSharedCheck_1584_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_stopPos_1576_);
lean_inc(v_str_1575_);
lean_dec(v_s_1564_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1584_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 1, v_stopPos_1568_);
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_str_1575_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v_stopPos_1568_);
lean_ctor_set(v_reuseFailAlloc_1583_, 2, v_stopPos_1576_);
v___x_1581_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1582_; 
v___x_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
return v___x_1582_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_dropSuffix_x3f(lean_object* v_s_1586_, lean_object* v_suff_1587_){
_start:
{
lean_object* v_t_1588_; lean_object* v_startPos_1589_; lean_object* v_stopPos_1590_; lean_object* v_startPos_1591_; lean_object* v_stopPos_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; uint8_t v___x_1595_; 
lean_inc_ref(v_suff_1587_);
lean_inc_ref(v_s_1586_);
v_t_1588_ = l_Substring_Raw_commonSuffix(v_s_1586_, v_suff_1587_);
v_startPos_1589_ = lean_ctor_get(v_t_1588_, 1);
lean_inc(v_startPos_1589_);
v_stopPos_1590_ = lean_ctor_get(v_t_1588_, 2);
lean_inc(v_stopPos_1590_);
lean_dec_ref(v_t_1588_);
v_startPos_1591_ = lean_ctor_get(v_suff_1587_, 1);
lean_inc(v_startPos_1591_);
v_stopPos_1592_ = lean_ctor_get(v_suff_1587_, 2);
lean_inc(v_stopPos_1592_);
lean_dec_ref(v_suff_1587_);
v___x_1593_ = lean_nat_sub(v_stopPos_1590_, v_startPos_1589_);
lean_dec(v_stopPos_1590_);
v___x_1594_ = lean_nat_sub(v_stopPos_1592_, v_startPos_1591_);
lean_dec(v_startPos_1591_);
lean_dec(v_stopPos_1592_);
v___x_1595_ = lean_nat_dec_eq(v___x_1593_, v___x_1594_);
lean_dec(v___x_1594_);
lean_dec(v___x_1593_);
if (v___x_1595_ == 0)
{
lean_object* v___x_1596_; 
lean_dec(v_startPos_1589_);
lean_dec_ref(v_s_1586_);
v___x_1596_ = lean_box(0);
return v___x_1596_;
}
else
{
lean_object* v_str_1597_; lean_object* v_startPos_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1606_; 
v_str_1597_ = lean_ctor_get(v_s_1586_, 0);
v_startPos_1598_ = lean_ctor_get(v_s_1586_, 1);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_s_1586_);
if (v_isSharedCheck_1606_ == 0)
{
lean_object* v_unused_1607_; 
v_unused_1607_ = lean_ctor_get(v_s_1586_, 2);
lean_dec(v_unused_1607_);
v___x_1600_ = v_s_1586_;
v_isShared_1601_ = v_isSharedCheck_1606_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_startPos_1598_);
lean_inc(v_str_1597_);
lean_dec(v_s_1586_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1606_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 2, v_startPos_1589_);
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_str_1597_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_startPos_1598_);
lean_ctor_set(v_reuseFailAlloc_1605_, 2, v_startPos_1589_);
v___x_1603_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
lean_object* v___x_1604_; 
v___x_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
return v___x_1604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg(lean_object* v_x_1608_, lean_object* v_x_1609_, lean_object* v_x_1610_, lean_object* v_h__1_1611_, lean_object* v_h__2_1612_){
_start:
{
lean_object* v_zero_1613_; uint8_t v_isZero_1614_; 
v_zero_1613_ = lean_unsigned_to_nat(0u);
v_isZero_1614_ = lean_nat_dec_eq(v_x_1609_, v_zero_1613_);
if (v_isZero_1614_ == 1)
{
lean_object* v___x_1615_; 
lean_dec(v_h__2_1612_);
v___x_1615_ = lean_apply_2(v_h__1_1611_, v_x_1608_, v_x_1610_);
return v___x_1615_;
}
else
{
lean_object* v_one_1616_; lean_object* v_n_1617_; lean_object* v___x_1618_; 
lean_dec(v_h__1_1611_);
v_one_1616_ = lean_unsigned_to_nat(1u);
v_n_1617_ = lean_nat_sub(v_x_1609_, v_one_1616_);
v___x_1618_ = lean_apply_3(v_h__2_1612_, v_x_1608_, v_n_1617_, v_x_1610_);
return v___x_1618_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg___boxed(lean_object* v_x_1619_, lean_object* v_x_1620_, lean_object* v_x_1621_, lean_object* v_h__1_1622_, lean_object* v_h__2_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___redArg(v_x_1619_, v_x_1620_, v_x_1621_, v_h__1_1622_, v_h__2_1623_);
lean_dec(v_x_1620_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter(lean_object* v_motive_1625_, lean_object* v_x_1626_, lean_object* v_x_1627_, lean_object* v_x_1628_, lean_object* v_h__1_1629_, lean_object* v_h__2_1630_){
_start:
{
lean_object* v_zero_1631_; uint8_t v_isZero_1632_; 
v_zero_1631_ = lean_unsigned_to_nat(0u);
v_isZero_1632_ = lean_nat_dec_eq(v_x_1627_, v_zero_1631_);
if (v_isZero_1632_ == 1)
{
lean_object* v___x_1633_; 
lean_dec(v_h__2_1630_);
v___x_1633_ = lean_apply_2(v_h__1_1629_, v_x_1626_, v_x_1628_);
return v___x_1633_;
}
else
{
lean_object* v_one_1634_; lean_object* v_n_1635_; lean_object* v___x_1636_; 
lean_dec(v_h__1_1629_);
v_one_1634_ = lean_unsigned_to_nat(1u);
v_n_1635_ = lean_nat_sub(v_x_1627_, v_one_1634_);
v___x_1636_ = lean_apply_3(v_h__2_1630_, v_x_1626_, v_n_1635_, v_x_1628_);
return v___x_1636_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter___boxed(lean_object* v_motive_1637_, lean_object* v_x_1638_, lean_object* v_x_1639_, lean_object* v_x_1640_, lean_object* v_h__1_1641_, lean_object* v_h__2_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l___private_Init_Data_String_Substring_0__Substring_Raw_nextn_match__1_splitter(v_motive_1637_, v_x_1638_, v_x_1639_, v_x_1640_, v_h__1_1641_, v_h__2_1642_);
lean_dec(v_x_1639_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l_Substring_bsize(lean_object* v_a_1644_){
_start:
{
lean_object* v_startPos_1645_; lean_object* v_stopPos_1646_; lean_object* v___x_1647_; 
v_startPos_1645_ = lean_ctor_get(v_a_1644_, 1);
v_stopPos_1646_ = lean_ctor_get(v_a_1644_, 2);
v___x_1647_ = lean_nat_sub(v_stopPos_1646_, v_startPos_1645_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Substring_bsize___boxed(lean_object* v_a_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_Substring_bsize(v_a_1648_);
lean_dec_ref(v_a_1648_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Substring_toString(lean_object* v_a_1650_){
_start:
{
lean_object* v_str_1651_; lean_object* v_startPos_1652_; lean_object* v_stopPos_1653_; lean_object* v___x_1654_; 
v_str_1651_ = lean_ctor_get(v_a_1650_, 0);
v_startPos_1652_ = lean_ctor_get(v_a_1650_, 1);
v_stopPos_1653_ = lean_ctor_get(v_a_1650_, 2);
v___x_1654_ = lean_string_utf8_extract(v_str_1651_, v_startPos_1652_, v_stopPos_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Substring_toString___boxed(lean_object* v_a_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Substring_toString(v_a_1655_);
lean_dec_ref(v_a_1655_);
return v_res_1656_;
}
}
LEAN_EXPORT uint8_t l_Substring_isEmpty(lean_object* v_ss_1657_){
_start:
{
lean_object* v_startPos_1658_; lean_object* v_stopPos_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; uint8_t v___x_1662_; 
v_startPos_1658_ = lean_ctor_get(v_ss_1657_, 1);
v_stopPos_1659_ = lean_ctor_get(v_ss_1657_, 2);
v___x_1660_ = lean_nat_sub(v_stopPos_1659_, v_startPos_1658_);
v___x_1661_ = lean_unsigned_to_nat(0u);
v___x_1662_ = lean_nat_dec_eq(v___x_1660_, v___x_1661_);
lean_dec(v___x_1660_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Substring_isEmpty___boxed(lean_object* v_ss_1663_){
_start:
{
uint8_t v_res_1664_; lean_object* v_r_1665_; 
v_res_1664_ = l_Substring_isEmpty(v_ss_1663_);
lean_dec_ref(v_ss_1663_);
v_r_1665_ = lean_box(v_res_1664_);
return v_r_1665_;
}
}
LEAN_EXPORT lean_object* l_Substring_next(lean_object* v_a_1666_, lean_object* v_a_1667_){
_start:
{
lean_object* v_str_1668_; lean_object* v_startPos_1669_; lean_object* v_stopPos_1670_; lean_object* v_absP_1671_; uint8_t v_decide_1672_; 
v_str_1668_ = lean_ctor_get(v_a_1666_, 0);
v_startPos_1669_ = lean_ctor_get(v_a_1666_, 1);
v_stopPos_1670_ = lean_ctor_get(v_a_1666_, 2);
v_absP_1671_ = lean_nat_add(v_startPos_1669_, v_a_1667_);
v_decide_1672_ = lean_nat_dec_eq(v_absP_1671_, v_stopPos_1670_);
if (v_decide_1672_ == 0)
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1673_ = lean_string_utf8_next(v_str_1668_, v_absP_1671_);
lean_dec(v_absP_1671_);
v___x_1674_ = lean_nat_sub(v___x_1673_, v_startPos_1669_);
lean_dec(v___x_1673_);
return v___x_1674_;
}
else
{
lean_dec(v_absP_1671_);
lean_inc(v_a_1667_);
return v_a_1667_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_next___boxed(lean_object* v_a_1675_, lean_object* v_a_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Substring_next(v_a_1675_, v_a_1676_);
lean_dec(v_a_1676_);
lean_dec_ref(v_a_1675_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Substring_prev(lean_object* v_a_1678_, lean_object* v_a_1679_){
_start:
{
lean_object* v_str_1680_; lean_object* v_startPos_1681_; lean_object* v_absP_1682_; uint8_t v_decide_1683_; 
v_str_1680_ = lean_ctor_get(v_a_1678_, 0);
v_startPos_1681_ = lean_ctor_get(v_a_1678_, 1);
v_absP_1682_ = lean_nat_add(v_startPos_1681_, v_a_1679_);
v_decide_1683_ = lean_nat_dec_eq(v_absP_1682_, v_startPos_1681_);
if (v_decide_1683_ == 0)
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1684_ = lean_string_utf8_prev(v_str_1680_, v_absP_1682_);
lean_dec(v_absP_1682_);
v___x_1685_ = lean_nat_sub(v___x_1684_, v_startPos_1681_);
lean_dec(v___x_1684_);
return v___x_1685_;
}
else
{
lean_dec(v_absP_1682_);
lean_inc(v_a_1679_);
return v_a_1679_;
}
}
}
LEAN_EXPORT lean_object* l_Substring_prev___boxed(lean_object* v_a_1686_, lean_object* v_a_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Substring_prev(v_a_1686_, v_a_1687_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
return v_res_1688_;
}
}
LEAN_EXPORT uint8_t l_Substring_atEnd(lean_object* v_a_1689_, lean_object* v_a_1690_){
_start:
{
lean_object* v_startPos_1691_; lean_object* v_stopPos_1692_; lean_object* v___x_1693_; uint8_t v_decide_1694_; 
v_startPos_1691_ = lean_ctor_get(v_a_1689_, 1);
v_stopPos_1692_ = lean_ctor_get(v_a_1689_, 2);
v___x_1693_ = lean_nat_add(v_startPos_1691_, v_a_1690_);
v_decide_1694_ = lean_nat_dec_eq(v___x_1693_, v_stopPos_1692_);
lean_dec(v___x_1693_);
return v_decide_1694_;
}
}
LEAN_EXPORT lean_object* l_Substring_atEnd___boxed(lean_object* v_a_1695_, lean_object* v_a_1696_){
_start:
{
uint8_t v_res_1697_; lean_object* v_r_1698_; 
v_res_1697_ = l_Substring_atEnd(v_a_1695_, v_a_1696_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
v_r_1698_ = lean_box(v_res_1697_);
return v_r_1698_;
}
}
LEAN_EXPORT uint8_t l_Substring_beq(lean_object* v_ss1_1699_, lean_object* v_ss2_1700_){
_start:
{
uint8_t v___x_1701_; 
v___x_1701_ = l_Substring_Raw_beq(v_ss1_1699_, v_ss2_1700_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Substring_beq___boxed(lean_object* v_ss1_1702_, lean_object* v_ss2_1703_){
_start:
{
uint8_t v_res_1704_; lean_object* v_r_1705_; 
v_res_1704_ = l_Substring_beq(v_ss1_1702_, v_ss2_1703_);
v_r_1705_ = lean_box(v_res_1704_);
return v_r_1705_;
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

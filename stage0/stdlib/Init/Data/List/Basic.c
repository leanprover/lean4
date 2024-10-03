// Lean compiler output
// Module: Init.Data.List.Basic
// Imports: Init.SimpLemmas Init.Data.Nat.Basic Init.Data.List.Notation
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
LEAN_EXPORT lean_object* l_List_indexOf_x3f___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_minimum_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_head_x3f(lean_object*);
LEAN_EXPORT lean_object* l_List_partition___rarg(lean_object*, lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__2;
LEAN_EXPORT lean_object* l_List_head(lean_object*);
LEAN_EXPORT lean_object* l_List_eraseReps(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_length_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_join___rarg(lean_object*);
LEAN_EXPORT lean_object* l_List_iota(lean_object*);
LEAN_EXPORT lean_object* l_List_getLast(lean_object*);
LEAN_EXPORT lean_object* l_List_instBEq___rarg(lean_object*);
LEAN_EXPORT uint8_t l_List_contains___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_isSuffixOf___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_iota_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_all(lean_object*);
LEAN_EXPORT lean_object* l_List_rotateRight(lean_object*);
LEAN_EXPORT lean_object* l_List_replicate(lean_object*);
LEAN_EXPORT lean_object* l_List_getLast___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_groupBy(lean_object*);
static lean_object* l_List_term___x7e_____closed__3;
LEAN_EXPORT lean_object* l_List_countP(lean_object*);
LEAN_EXPORT lean_object* l_List_unzipTR___rarg(lean_object*);
LEAN_EXPORT lean_object* l_List_enum___rarg(lean_object*);
LEAN_EXPORT lean_object* l_List_join(lean_object*);
LEAN_EXPORT lean_object* l_List_min_x3f(lean_object*);
LEAN_EXPORT lean_object* l_List_zipWith(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_pure(lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__4;
LEAN_EXPORT lean_object* l_List_mapTR_loop(lean_object*, lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isSublist___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_iotaTR_go_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_reduceOption___rarg(lean_object*);
LEAN_EXPORT uint8_t l_List_all___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_tail___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_eraseIdx(lean_object*);
LEAN_EXPORT lean_object* l_List_isPrefixOf___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_reverseAux_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR___rarg(lean_object*, lean_object*);
static lean_object* l_List_term___x3c_x2b_____closed__2;
LEAN_EXPORT lean_object* l_List_instDecidableRelSubsetOfDecidableEq___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_takeWhile___rarg(lean_object*, lean_object*);
static lean_object* l_List_partition___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_concat_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseDups_loop(lean_object*);
LEAN_EXPORT lean_object* l_List_nodupDecidable(lean_object*);
LEAN_EXPORT lean_object* l_List_getLastD___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_unzip___rarg(lean_object*);
LEAN_EXPORT lean_object* l_List_getLast_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_concat_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_range_x27TR_go(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1;
LEAN_EXPORT uint8_t l_List_instDecidableMemOfLawfulBEq___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_reverseAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWith___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_or___closed__1;
LEAN_EXPORT lean_object* l_List_elem(lean_object*);
LEAN_EXPORT lean_object* l_List_replicateTR_loop___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop(lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_rotateRight___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_any___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replicate___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_bind___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_rotateRight___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_map(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_nodupDecidable___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_range_x27TR(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_term___x3c_x2b_x3a_____closed__4;
LEAN_EXPORT lean_object* l_List_head_x3f___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_countP_go___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__6;
LEAN_EXPORT lean_object* l_List_term___x3c_x3a_x2b__;
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__2;
LEAN_EXPORT lean_object* l_List_isEqv(lean_object*);
LEAN_EXPORT lean_object* l_List_contains(lean_object*);
LEAN_EXPORT lean_object* l_List_getD___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLastD_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_tail_x3f(lean_object*);
LEAN_EXPORT lean_object* l_List_filterMap___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_removeAll(lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__8;
static lean_object* l_List_term___x3c_x3a_x2b_x3a_____closed__2;
LEAN_EXPORT lean_object* l_List_iotaTR_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_head_x3f___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_range_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidableMemOfLawfulBEq___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__12;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_iotaTR_go_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_iota_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_term___x3c_x2b_____closed__9;
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__4;
LEAN_EXPORT lean_object* l_List_instHasSubset(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_join_match__1_splitter(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_bind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f(lean_object*);
LEAN_EXPORT lean_object* l_List_reverseAux(lean_object*);
LEAN_EXPORT uint8_t l_List_nodupDecidable___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_and___boxed(lean_object*);
static lean_object* l_List_term___x3c_x2b_____closed__4;
LEAN_EXPORT lean_object* l_List_zipWithAll___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__15;
LEAN_EXPORT lean_object* l_List_map___at_List_zipWithAll___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseIdx___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1;
static lean_object* l_List_term___x3c_x3a_x2b_x3a_____closed__1;
LEAN_EXPORT lean_object* l_List_eraseIdx___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_intersperseTR(lean_object*);
LEAN_EXPORT lean_object* l_List_isEqv___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_rightpad___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instEmptyCollection(lean_object*);
LEAN_EXPORT lean_object* l_List_head___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_term___x3c_x2b__;
LEAN_EXPORT lean_object* l_List_getD(lean_object*);
LEAN_EXPORT uint8_t l_List_instDecidableLeOfDecidableRelLt___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_span_loop(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_dropLast_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_contains___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_removeAll___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_map___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidableLeOfDecidableRelLt___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_take___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_beq_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_isSublist___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_term___x3c_x3a_x2b_x3a__;
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__5;
LEAN_EXPORT lean_object* l_List_groupBy___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_take___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isEmpty___rarg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_List_notElem___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_term___x3c_x2b_____closed__3;
LEAN_EXPORT lean_object* l_List_filterMap___at_List_reduceOption___spec__1___rarg(lean_object*);
uint8_t l_instDecidableNot___rarg(uint8_t);
LEAN_EXPORT uint8_t l_List_or(lean_object*);
LEAN_EXPORT lean_object* l_List_tail_x3f___rarg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_List_instDecidablePairwise___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_hasDecidableLt___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findIdx_x3f(lean_object*);
LEAN_EXPORT lean_object* l_List_findIdx___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_indexOf(lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at_List_unzipTR___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_lengthTRAux_match__1_splitter(lean_object*, lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__13;
LEAN_EXPORT lean_object* l_List_filter___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instLEOfLT(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_List_zipWithAll(lean_object*, lean_object*, lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__4;
LEAN_EXPORT lean_object* l_List_findSome_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_dropLast(lean_object*);
LEAN_EXPORT lean_object* l_List_replicate___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_isPerm___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1;
LEAN_EXPORT lean_object* l_List_span___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_countP_go(lean_object*);
LEAN_EXPORT uint8_t l_List_removeAll___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_range(lean_object*);
LEAN_EXPORT lean_object* l_List_rotateLeft___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_splitAt___rarg(lean_object*, lean_object*);
static lean_object* l_List_term___x3c_x3a_x2b_x3a_____closed__4;
static lean_object* l_List_term___x3c_x2b_x3a_____closed__5;
LEAN_EXPORT lean_object* l_List_maximum_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___rarg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_mapTR_loop_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__2;
LEAN_EXPORT lean_object* l_List_tail___rarg(lean_object*);
LEAN_EXPORT uint8_t l_List_hasDecidableLt___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replicateTR(lean_object*);
static lean_object* l_List_term___x3c_x2b_____closed__1;
LEAN_EXPORT lean_object* l_List_count___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__3;
LEAN_EXPORT lean_object* l_List_leftpad___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseDups(lean_object*);
LEAN_EXPORT lean_object* l_List_indexOf_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_intersperseTR_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replace(lean_object*);
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f(lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_getD___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_map___at_List_zipWithAll___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_max_x3f(lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_tail(lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at_List_unzipTR___spec__1___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_List_term___x3c_x2b_____closed__12;
LEAN_EXPORT lean_object* l_List_decidableBAll(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_List_all___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isSublist(lean_object*);
LEAN_EXPORT lean_object* l_List_instLT(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_and(lean_object*);
LEAN_EXPORT lean_object* l_List_isPrefixOf(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_groupBy_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_drop___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_List_term___x3c_x2b_x3a_____closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_isPrefixOf_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_set_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_erase___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_indexOf___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_splitAt_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at_Nat_sum___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseDups___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replicateTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_enumFrom(lean_object*);
LEAN_EXPORT lean_object* l_List_dropLast___rarg(lean_object*);
LEAN_EXPORT lean_object* l_List_head___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_span_loop___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_term___x3c_x2b_____closed__5;
LEAN_EXPORT lean_object* l_List_notElem(lean_object*);
static lean_object* l_List_term___x3c_x3a_x2b_____closed__1;
LEAN_EXPORT lean_object* l_List_replace___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_append(lean_object*);
LEAN_EXPORT lean_object* l_List_map___at_List_zipWithAll___spec__2___rarg(lean_object*, lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__5;
LEAN_EXPORT lean_object* l_List_lookup___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_headD(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_beq_match__1_splitter(lean_object*, lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_mapTR_loop_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isPerm(lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidableRelSubsetOfDecidableEq(lean_object*);
LEAN_EXPORT lean_object* l_List_removeAll___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__6;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_unzip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_length_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_count(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__2;
LEAN_EXPORT lean_object* l_List_erase(lean_object*);
LEAN_EXPORT lean_object* l_List_findIdx_go___at_List_indexOf___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidableLeOfDecidableRelLt(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
static lean_object* l_List_term___x3c_x2b_____closed__10;
LEAN_EXPORT lean_object* l_Nat_sum(lean_object*);
LEAN_EXPORT lean_object* l_List_span(lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at_Nat_sum___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__9;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_zipWith_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_leftpad(lean_object*);
LEAN_EXPORT uint8_t l_List_elem___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_term___x3c_x3a_x2b_x3a_____closed__5;
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_reverseAux_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_intercalate___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instMembership(lean_object*);
LEAN_EXPORT lean_object* l_List_drop(lean_object*);
LEAN_EXPORT lean_object* l_List_filterMap___at_List_reduceOption___spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLast_x3f_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidablePairwise___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_decidableBAll___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findIdx_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_isPrefixOf___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findSome_x3f(lean_object*, lean_object*);
static lean_object* l_List_term___x3c_x3a_x2b_____closed__6;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_zipWith_match__1_splitter(lean_object*, lean_object*, lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__2;
LEAN_EXPORT lean_object* l_List_indexOf_x3f(lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__3;
LEAN_EXPORT lean_object* l_List_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_join_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidableRelSubsetOfDecidableEq___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_term___x7e_____closed__1;
LEAN_EXPORT lean_object* l_List_lookup(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_range_x27TR_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_groupBy_loop(lean_object*);
LEAN_EXPORT lean_object* l_List_term___x3c_x2b_x3a__;
static lean_object* l_List_term___x3c_x2b_x3a_____closed__1;
LEAN_EXPORT lean_object* l_List_filter(lean_object*);
LEAN_EXPORT lean_object* l_List_getLastD(lean_object*);
LEAN_EXPORT lean_object* l_List_isSuffixOf(lean_object*);
static lean_object* l_List_term___x3c_x2b_x3a_____closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLast_x3f_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_decidableBEx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_length_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__5;
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__7;
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instLEOfLT___boxed(lean_object*, lean_object*);
static lean_object* l_List_term___x3c_x2b_____closed__11;
static lean_object* l_List_term___x3c_x3a_x2b_____closed__2;
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_tail_x3f___rarg(lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__10;
LEAN_EXPORT lean_object* l_List_rightpad___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_getLast_x3f___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_dropLast_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_countP_go___at_List_count___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_term___x3c_x2b_____closed__8;
LEAN_EXPORT lean_object* l_List_decidableBAll___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_tailD___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findIdx(lean_object*);
LEAN_EXPORT lean_object* l_List_instLT___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_intercalate(lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__6;
LEAN_EXPORT lean_object* l_List_zip___rarg(lean_object*, lean_object*);
static lean_object* l_List_term___x7e_____closed__4;
LEAN_EXPORT lean_object* l_List_reverse(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_set_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR(lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__3;
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1;
static lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLastD_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseReps_loop(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_dropLast_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_hasDecidableLt(lean_object*);
LEAN_EXPORT lean_object* l_List_insert___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_range_x27TR___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_headD___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_sum___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_drop___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_notElem___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_rotateLeft(lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at_List_intersperseTR___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_leftpadTR(lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__14;
static lean_object* l_List_term___x7e_____closed__6;
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__11;
LEAN_EXPORT lean_object* l_List_instDecidablePairwise(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_intersperseTR_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_term___x3c_x2b_x3a_____closed__6;
LEAN_EXPORT lean_object* l_List_any(lean_object*);
lean_object* l_id___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_leftpadTR___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_List_term___x3c_x2b_____closed__7;
LEAN_EXPORT lean_object* l_List_eraseReps___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_splitAt(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l_List_instBEq(lean_object*);
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_headD___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__4;
LEAN_EXPORT lean_object* l_List_splitAt_go(lean_object*);
static lean_object* l_List_term___x3c_x3a_x2b_x3a_____closed__3;
LEAN_EXPORT lean_object* l_List_get_x3f(lean_object*);
LEAN_EXPORT lean_object* l_List_beq(lean_object*);
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_intersperse___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_leftpad___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_instDecidableRelSubsetOfDecidableEq___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_decidableBEx___rarg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_tailD___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findIdx_go___at_List_indexOf___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5;
LEAN_EXPORT lean_object* l_List_intersperseTR___rarg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__8;
LEAN_EXPORT lean_object* l_List_leftpadTR___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_term___x7e_____closed__5;
LEAN_EXPORT lean_object* l_List_nodupDecidable___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_countP_go___at_List_count___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_tailD(lean_object*);
LEAN_EXPORT lean_object* l_List_iotaTR(lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__9;
LEAN_EXPORT lean_object* l_List_reduceOption(lean_object*);
LEAN_EXPORT lean_object* l_List_findIdx_go___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__5;
LEAN_EXPORT lean_object* l_List_min_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_rotateLeft___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWith___at_List_zip___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_get_x3f___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_List_instAppend(lean_object*);
LEAN_EXPORT lean_object* l_List_range_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_iota_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMap(lean_object*, lean_object*);
static lean_object* l_List_term___x3c_x3a_x2b_x3a_____closed__6;
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_dropWhile___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidableMemOfLawfulBEq(lean_object*);
LEAN_EXPORT lean_object* l_List_pure___rarg(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR(lean_object*, lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__4;
static lean_object* l_List_term___x3c_x3a_x2b_____closed__4;
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__7;
LEAN_EXPORT lean_object* l_List_minimum_x3f(lean_object*);
LEAN_EXPORT lean_object* l_List_append___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_intersperseTR_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseP(lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop(lean_object*);
LEAN_EXPORT lean_object* l_List_decidableBEx___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findIdx_go(lean_object*);
LEAN_EXPORT lean_object* l_List_intersperse(lean_object*);
LEAN_EXPORT lean_object* l_List_dropWhile(lean_object*);
LEAN_EXPORT uint8_t l_List_instDecidableRelSubsetOfDecidableEq___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_maximum_x3f(lean_object*);
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f(lean_object*);
LEAN_EXPORT lean_object* l_List_or___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldr(lean_object*, lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__3;
LEAN_EXPORT lean_object* l_List_appendTR(lean_object*);
LEAN_EXPORT lean_object* l_List_takeWhile(lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__6;
LEAN_EXPORT lean_object* l_List_rightpad(lean_object*);
LEAN_EXPORT lean_object* l_List_take(lean_object*);
LEAN_EXPORT lean_object* l_List_eraseP___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isPerm___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_term___x3c_x3a_x2b_____closed__3;
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__16;
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isSuffixOf___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replicateTR_loop(lean_object*);
static lean_object* l_List_instAppend___closed__1;
LEAN_EXPORT lean_object* l_List_getLastD___rarg___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_insert(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLast_x3f_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_beq_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_map___at_List_zipWithAll___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_iotaTR_go_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_unzipTR(lean_object*, lean_object*);
static lean_object* l_List_term___x3c_x2b_____closed__6;
LEAN_EXPORT lean_object* l_List_enumFrom___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at_List_intersperseTR___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_isEqv___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_lengthTRAux_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
LEAN_EXPORT lean_object* l_List_term___x7e__;
LEAN_EXPORT lean_object* l_List_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_enum(lean_object*);
LEAN_EXPORT lean_object* l_List_nodupDecidable___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_range_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWith___at_List_zip___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at_List_unzipTR___spec__1(lean_object*, lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__6;
static lean_object* l_List_term___x3c_x3a_x2b_____closed__5;
static lean_object* l_List_term___x7e_____closed__2;
LEAN_EXPORT lean_object* l_List_foldr___at_List_intersperseTR___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_get_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseDups_loop___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_join_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_isPrefixOf_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseReps_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_countP___rarg(lean_object*, lean_object*);
lean_object* l_List_length___rarg(lean_object*);
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__2;
static lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3;
LEAN_EXPORT lean_object* l_List_max_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_set_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
x_7 = lean_apply_2(x_6, x_2, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_2, x_12);
lean_dec(x_2);
x_14 = lean_apply_4(x_5, x_8, x_9, x_13, x_3);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_2);
x_15 = lean_apply_3(x_4, x_8, x_9, x_3);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_set_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_List_Basic_0__List_set_match__1_splitter___rarg), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_concat_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
x_5 = lean_apply_1(x_3, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_3(x_4, x_6, x_7, x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_concat_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_List_Basic_0__List_concat_match__1_splitter___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT uint8_t l_List_beq___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 0;
return x_5;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
lean_inc(x_1);
x_11 = lean_apply_2(x_1, x_7, x_9);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_1);
x_13 = 0;
return x_13;
}
else
{
x_2 = x_8;
x_3 = x_10;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_beq___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_beq___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_beq___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_instBEq___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_beq___rarg___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_instBEq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_instBEq___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_beq_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_5);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_6; 
x_6 = lean_apply_4(x_5, x_1, x_2, lean_box(0), lean_box(0));
return x_6;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_apply_4(x_5, x_1, x_2, lean_box(0), lean_box(0));
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_apply_4(x_4, x_8, x_9, x_10, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_beq_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_List_Basic_0__List_beq_match__1_splitter___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_beq_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_List_Basic_0__List_beq_match__1_splitter___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l_List_isEqv___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = 0;
return x_5;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_3);
x_11 = lean_apply_2(x_3, x_7, x_9);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_3);
x_13 = 0;
return x_13;
}
else
{
x_1 = x_8;
x_2 = x_10;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isEqv(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_isEqv___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_isEqv___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_isEqv___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_instLT(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_instLT___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_instLT(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_List_hasDecidableLt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 1;
return x_6;
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
lean_inc(x_2);
lean_inc(x_10);
lean_inc(x_8);
x_12 = lean_apply_2(x_2, x_8, x_10);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
lean_inc(x_2);
x_14 = lean_apply_2(x_2, x_10, x_8);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
x_3 = x_9;
x_4 = x_11;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_2);
x_17 = 0;
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_18 = 1;
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_hasDecidableLt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_hasDecidableLt___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_hasDecidableLt___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_List_hasDecidableLt___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_instLEOfLT(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_instLEOfLT___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_instLEOfLT(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableLeOfDecidableRelLt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; 
x_5 = l_List_hasDecidableLt___rarg(x_1, x_2, x_4, x_3);
x_6 = l_instDecidableNot___rarg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableLeOfDecidableRelLt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_instDecidableLeOfDecidableRelLt___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableLeOfDecidableRelLt___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_List_instDecidableLeOfDecidableRelLt___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_get_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_2, x_8);
lean_dec(x_2);
x_1 = x_5;
x_2 = x_9;
goto _start;
}
else
{
lean_object* x_11; 
lean_dec(x_2);
lean_inc(x_4);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_4);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_List_get_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_get_x3f___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_get_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_get_x3f___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_getD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_get_x3f___rarg(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_List_getD(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_getD___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_getD___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_getD___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_getLast___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
x_1 = x_3;
x_2 = lean_box(0);
goto _start;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_1 = x_9;
x_2 = lean_box(0);
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_getLast(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_getLast___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_getLast_x3f___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_List_getLast___rarg(x_1, lean_box(0));
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_List_getLast___rarg(x_8, lean_box(0));
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_List_getLast_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_getLast_x3f___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_getLastD___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = l_List_getLast___rarg(x_1, lean_box(0));
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_List_getLast___rarg(x_7, lean_box(0));
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_List_getLastD(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_getLastD___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_getLastD___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_getLastD___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_head___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_head(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_head___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_head___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_head___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_head_x3f___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_List_head_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_head_x3f___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_head_x3f___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_head_x3f___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_headD___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_List_headD(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_headD___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_headD___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_headD___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_tail___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_List_tail(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_tail___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_tail___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_tail___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_tail_x3f___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_List_tail_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_tail_x3f___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_tail_x3f___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_tail_x3f___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_tailD___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_List_tailD(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_tailD___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_tailD___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_tailD___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_map___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_7 = lean_apply_1(x_1, x_5);
x_8 = l_List_map___rarg(x_1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
lean_inc(x_1);
x_11 = lean_apply_1(x_1, x_9);
x_12 = l_List_map___rarg(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_List_map(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_map___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_filter___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
lean_inc(x_5);
x_7 = lean_apply_1(x_1, x_5);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_free_object(x_2);
lean_dec(x_5);
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_10; 
x_10 = l_List_filter___rarg(x_1, x_6);
lean_ctor_set(x_2, 1, x_10);
return x_2;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_11);
x_13 = lean_apply_1(x_1, x_11);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_11);
x_2 = x_12;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_List_filter___rarg(x_1, x_12);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_filter___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_filterMap___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_7 = lean_apply_1(x_1, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_free_object(x_2);
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_List_filterMap___rarg(x_1, x_6);
lean_ctor_set(x_2, 1, x_10);
lean_ctor_set(x_2, 0, x_9);
return x_2;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_1);
x_13 = lean_apply_1(x_1, x_11);
if (lean_obj_tag(x_13) == 0)
{
x_2 = x_12;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_List_filterMap___rarg(x_1, x_12);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMap(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_filterMap___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldr___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_1);
x_6 = l_List_foldr___rarg(x_1, x_2, x_5);
x_7 = lean_apply_2(x_1, x_4, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_List_foldr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_foldr___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldr___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldr___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_reverseAux___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_4;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_2);
x_1 = x_7;
x_2 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_reverseAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_reverseAux___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_reverse___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_List_reverseAux___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_reverse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_reverse___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_reverseAux_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
x_5 = lean_apply_1(x_3, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_3(x_4, x_6, x_7, x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_reverseAux_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_List_Basic_0__List_reverseAux_match__1_splitter___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_append___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_List_append___rarg(x_4, x_2);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = l_List_append___rarg(x_7, x_2);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_List_append(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_append___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_append___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_append___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_appendTR___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_List_reverse___rarg(x_1);
x_4 = l_List_reverseAux___rarg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_appendTR(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_appendTR___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_List_instAppend___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_appendTR___rarg), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_instAppend(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_instAppend___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_join___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_List_join___rarg(x_4);
x_6 = l_List_appendTR___rarg(x_3, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_List_join(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_join___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_pure___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_pure(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_pure___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_bind___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_List_map___rarg(x_2, x_1);
x_4 = l_List_join___rarg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_bind(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_bind___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_join_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_3, x_4, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_join_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_List_Basic_0__List_join_match__1_splitter___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_join_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_List_Basic_0__List_join_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_replicate___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_1, x_5);
lean_inc(x_2);
x_7 = l_List_replicate___rarg(x_6, x_2);
lean_dec(x_6);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_box(0);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_List_replicate(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_replicate___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_replicate___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_replicate___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_leftpad___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_List_length___rarg(x_3);
x_5 = lean_nat_sub(x_1, x_4);
lean_dec(x_4);
x_6 = l_List_replicate___rarg(x_5, x_2);
lean_dec(x_5);
x_7 = l_List_appendTR___rarg(x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_leftpad(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_leftpad___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_leftpad___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_leftpad___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_rightpad___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_List_length___rarg(x_3);
x_5 = lean_nat_sub(x_1, x_4);
lean_dec(x_4);
x_6 = l_List_replicate___rarg(x_5, x_2);
lean_dec(x_5);
x_7 = l_List_appendTR___rarg(x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_rightpad(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_rightpad___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_rightpad___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_rightpad___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_filterMap___at_List_reduceOption___spec__1___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_1 = x_4;
goto _start;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_List_filterMap___at_List_reduceOption___spec__1___rarg(x_7);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = l_List_filterMap___at_List_reduceOption___spec__1___rarg(x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMap___at_List_reduceOption___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_filterMap___at_List_reduceOption___spec__1___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_reduceOption___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_filterMap___at_List_reduceOption___spec__1___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_reduceOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_reduceOption___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_instEmptyCollection(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_List_isEmpty___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_List_isEmpty(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_isEmpty___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_isEmpty___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_List_isEmpty___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_List_elem___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_7 = lean_apply_2(x_1, x_2, x_5);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
x_3 = x_6;
goto _start;
}
else
{
uint8_t x_10; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_10 = 1;
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_elem___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_elem___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_elem___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_List_notElem___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_List_elem___rarg(x_1, x_2, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_List_notElem(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_notElem___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_notElem___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_notElem___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_List_contains___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_List_elem___rarg(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_contains(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_contains___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_contains___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_contains___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_instMembership(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLast_x3f_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_3, x_4, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLast_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_List_Basic_0__List_getLast_x3f_match__1_splitter___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLast_x3f_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_List_Basic_0__List_getLast_x3f_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (x_1 == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___rarg(x_4, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableMemOfLawfulBEq___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_List_elem___rarg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableMemOfLawfulBEq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_instDecidableMemOfLawfulBEq___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableMemOfLawfulBEq___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_List_instDecidableMemOfLawfulBEq___rarg(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_List_decidableBEx___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
lean_inc(x_1);
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_9; 
lean_dec(x_5);
lean_dec(x_1);
x_9 = 1;
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_List_decidableBEx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_decidableBEx___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_decidableBEx___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_decidableBEx___rarg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_List_decidableBAll___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = 1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
lean_inc(x_1);
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
lean_dec(x_1);
x_8 = 0;
return x_8;
}
else
{
x_2 = x_5;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_decidableBAll(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_decidableBAll___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_decidableBAll___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_decidableBAll___rarg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_take___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_1, x_8);
x_10 = l_List_take___rarg(x_9, x_7);
lean_dec(x_9);
lean_ctor_set(x_2, 1, x_10);
return x_2;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_1, x_13);
x_15 = l_List_take___rarg(x_14, x_12);
lean_dec(x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
else
{
lean_object* x_17; 
lean_dec(x_2);
x_17 = lean_box(0);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_List_take(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_take___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_take___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_take___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_drop___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_1, x_7);
lean_dec(x_1);
x_1 = x_8;
x_2 = x_6;
goto _start;
}
}
else
{
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_List_drop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_drop___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_drop___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_drop___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_takeWhile___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
lean_inc(x_5);
x_7 = lean_apply_1(x_1, x_5);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l_List_takeWhile___rarg(x_1, x_6);
lean_ctor_set(x_2, 1, x_10);
return x_2;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_11);
x_13 = lean_apply_1(x_1, x_11);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_List_takeWhile___rarg(x_1, x_12);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_takeWhile(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_takeWhile___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_dropWhile___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
lean_inc(x_5);
x_7 = lean_apply_1(x_1, x_5);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_free_object(x_2);
lean_dec(x_5);
x_2 = x_6;
goto _start;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_10);
x_12 = lean_apply_1(x_1, x_10);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_dec(x_10);
x_2 = x_11;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_dropWhile(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_dropWhile___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = l_List_reverse___rarg(x_5);
x_8 = l_List_reverse___rarg(x_6);
lean_ctor_set(x_3, 1, x_8);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = l_List_reverse___rarg(x_9);
x_12 = l_List_reverse___rarg(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
lean_inc(x_16);
x_20 = lean_apply_1(x_1, x_16);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_ctor_set(x_2, 1, x_19);
lean_ctor_set(x_3, 1, x_2);
x_2 = x_17;
goto _start;
}
else
{
lean_ctor_set(x_2, 1, x_18);
lean_ctor_set(x_3, 0, x_2);
x_2 = x_17;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
x_26 = lean_ctor_get(x_3, 0);
x_27 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_24);
x_28 = lean_apply_1(x_1, x_24);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_ctor_set(x_2, 1, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_2);
x_2 = x_25;
x_3 = x_30;
goto _start;
}
else
{
lean_object* x_32; 
lean_ctor_set(x_2, 1, x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_27);
x_2 = x_25;
x_3 = x_32;
goto _start;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_34 = lean_ctor_get(x_2, 0);
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_2);
x_36 = lean_ctor_get(x_3, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_3, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_38 = x_3;
} else {
 lean_dec_ref(x_3);
 x_38 = lean_box(0);
}
lean_inc(x_1);
lean_inc(x_34);
x_39 = lean_apply_1(x_1, x_34);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_37);
if (lean_is_scalar(x_38)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_38;
}
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_41);
x_2 = x_35;
x_3 = x_42;
goto _start;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_34);
lean_ctor_set(x_44, 1, x_36);
if (lean_is_scalar(x_38)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_38;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_37);
x_2 = x_35;
x_3 = x_45;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_partition_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_partition_loop___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_List_partition___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_partition___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_List_partition___rarg___closed__1;
x_4 = l_List_partition_loop___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_partition(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_partition___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_dropLast___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
lean_inc(x_3);
x_6 = l_List_dropLast___rarg(x_3);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_3, 0);
lean_dec(x_9);
lean_ctor_set(x_3, 1, x_6);
lean_ctor_set(x_3, 0, x_5);
return x_3;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_dropLast(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_dropLast___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_dropLast_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_3(x_4, x_8, x_5, lean_box(0));
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_dropLast_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_List_Basic_0__List_dropLast_match__1_splitter___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_dropLast_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_List_Basic_0__List_dropLast_match__1_splitter___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_instHasSubset(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableRelSubsetOfDecidableEq___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___rarg), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_List_elem___rarg(x_4, x_3, x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableRelSubsetOfDecidableEq___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_alloc_closure((void*)(l_List_instDecidableRelSubsetOfDecidableEq___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
x_5 = l_List_decidableBAll___rarg(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableRelSubsetOfDecidableEq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_instDecidableRelSubsetOfDecidableEq___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableRelSubsetOfDecidableEq___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_instDecidableRelSubsetOfDecidableEq___rarg___lambda__1(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableRelSubsetOfDecidableEq___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_instDecidableRelSubsetOfDecidableEq___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l_List_term___x3c_x2b_____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("List", 4, 4);
return x_1;
}
}
static lean_object* _init_l_List_term___x3c_x2b_____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term_<+_", 8, 8);
return x_1;
}
}
static lean_object* _init_l_List_term___x3c_x2b_____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_term___x3c_x2b_____closed__1;
x_2 = l_List_term___x3c_x2b_____closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_term___x3c_x2b_____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("andthen", 7, 7);
return x_1;
}
}
static lean_object* _init_l_List_term___x3c_x2b_____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List_term___x3c_x2b_____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_term___x3c_x2b_____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" <+ ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_List_term___x3c_x2b_____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_term___x3c_x2b_____closed__6;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_term___x3c_x2b_____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_List_term___x3c_x2b_____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List_term___x3c_x2b_____closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_term___x3c_x2b_____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_term___x3c_x2b_____closed__9;
x_2 = lean_unsigned_to_nat(51u);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_term___x3c_x2b_____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_List_term___x3c_x2b_____closed__5;
x_2 = l_List_term___x3c_x2b_____closed__7;
x_3 = l_List_term___x3c_x2b_____closed__10;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_List_term___x3c_x2b_____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_List_term___x3c_x2b_____closed__3;
x_2 = lean_unsigned_to_nat(50u);
x_3 = l_List_term___x3c_x2b_____closed__11;
x_4 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_3);
return x_4;
}
}
static lean_object* _init_l_List_term___x3c_x2b__() {
_start:
{
lean_object* x_1; 
x_1 = l_List_term___x3c_x2b_____closed__12;
return x_1;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("app", 3, 3);
return x_1;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1;
x_2 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__2;
x_3 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3;
x_4 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Sublist", 7, 7);
return x_1;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__6;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_term___x3c_x2b_____closed__1;
x_2 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__6;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__11;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__11;
x_2 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__12;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__10;
x_2 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_List_term___x3c_x2b_____closed__3;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = lean_ctor_get(x_2, 5);
lean_inc(x_12);
x_13 = 0;
x_14 = l_Lean_SourceInfo_fromRef(x_12, x_13);
lean_dec(x_12);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__8;
x_18 = l_Lean_addMacroScope(x_16, x_17, x_15);
x_19 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__7;
x_20 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__14;
lean_inc(x_14);
x_21 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_20);
x_22 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__16;
lean_inc(x_14);
x_23 = l_Lean_Syntax_node2(x_14, x_22, x_9, x_11);
x_24 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5;
x_25 = l_Lean_Syntax_node2(x_14, x_24, x_21, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_3);
return x_26;
}
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ident", 5, 5);
return x_1;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__2;
lean_inc(x_9);
x_11 = l_Lean_Syntax_isOfKind(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = lean_unsigned_to_nat(2u);
lean_inc(x_15);
x_17 = l_Lean_Syntax_matchesNull(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_9);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = l_Lean_Syntax_getArg(x_15, x_8);
x_21 = l_Lean_Syntax_getArg(x_15, x_14);
lean_dec(x_15);
x_22 = l_Lean_replaceRef(x_9, x_2);
lean_dec(x_9);
x_23 = 0;
x_24 = l_Lean_SourceInfo_fromRef(x_22, x_23);
lean_dec(x_22);
x_25 = l_List_term___x3c_x2b_____closed__6;
lean_inc(x_24);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_List_term___x3c_x2b_____closed__3;
x_28 = l_Lean_Syntax_node3(x_24, x_27, x_20, x_26, x_21);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_3);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_List_isSublist___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
lean_dec(x_3);
lean_dec(x_1);
x_4 = 1;
return x_4;
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
lean_inc(x_1);
x_10 = lean_apply_2(x_1, x_6, x_8);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_dec(x_7);
x_3 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
x_2 = x_7;
x_3 = x_9;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isSublist(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_isSublist___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_isSublist___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_isSublist___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l_List_term___x3c_x2b_x3a_____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term_<+:_", 9, 9);
return x_1;
}
}
static lean_object* _init_l_List_term___x3c_x2b_x3a_____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_term___x3c_x2b_____closed__1;
x_2 = l_List_term___x3c_x2b_x3a_____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_term___x3c_x2b_x3a_____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" <+: ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_List_term___x3c_x2b_x3a_____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_term___x3c_x2b_x3a_____closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_term___x3c_x2b_x3a_____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_List_term___x3c_x2b_____closed__5;
x_2 = l_List_term___x3c_x2b_x3a_____closed__4;
x_3 = l_List_term___x3c_x2b_____closed__10;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_List_term___x3c_x2b_x3a_____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_List_term___x3c_x2b_x3a_____closed__2;
x_2 = lean_unsigned_to_nat(50u);
x_3 = l_List_term___x3c_x2b_x3a_____closed__5;
x_4 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_3);
return x_4;
}
}
static lean_object* _init_l_List_term___x3c_x2b_x3a__() {
_start:
{
lean_object* x_1; 
x_1 = l_List_term___x3c_x2b_x3a_____closed__6;
return x_1;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IsPrefix", 8, 8);
return x_1;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_term___x3c_x2b_____closed__1;
x_2 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_List_term___x3c_x2b_x3a_____closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = lean_ctor_get(x_2, 5);
lean_inc(x_12);
x_13 = 0;
x_14 = l_Lean_SourceInfo_fromRef(x_12, x_13);
lean_dec(x_12);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__3;
x_18 = l_Lean_addMacroScope(x_16, x_17, x_15);
x_19 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__2;
x_20 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__6;
lean_inc(x_14);
x_21 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_20);
x_22 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__16;
lean_inc(x_14);
x_23 = l_Lean_Syntax_node2(x_14, x_22, x_9, x_11);
x_24 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5;
x_25 = l_Lean_Syntax_node2(x_14, x_24, x_21, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_3);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__2;
lean_inc(x_9);
x_11 = l_Lean_Syntax_isOfKind(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = lean_unsigned_to_nat(2u);
lean_inc(x_15);
x_17 = l_Lean_Syntax_matchesNull(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_9);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = l_Lean_Syntax_getArg(x_15, x_8);
x_21 = l_Lean_Syntax_getArg(x_15, x_14);
lean_dec(x_15);
x_22 = l_Lean_replaceRef(x_9, x_2);
lean_dec(x_9);
x_23 = 0;
x_24 = l_Lean_SourceInfo_fromRef(x_22, x_23);
lean_dec(x_22);
x_25 = l_List_term___x3c_x2b_x3a_____closed__3;
lean_inc(x_24);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_List_term___x3c_x2b_x3a_____closed__2;
x_28 = l_Lean_Syntax_node3(x_24, x_27, x_20, x_26, x_21);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_3);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_List_isPrefixOf___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
lean_dec(x_3);
lean_dec(x_1);
x_4 = 1;
return x_4;
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
lean_inc(x_1);
x_10 = lean_apply_2(x_1, x_6, x_8);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_1);
x_12 = 0;
return x_12;
}
else
{
x_2 = x_7;
x_3 = x_9;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_isPrefixOf___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_isPrefixOf___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_isPrefixOf_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_5);
lean_dec(x_4);
x_6 = lean_apply_1(x_3, x_2);
return x_6;
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = lean_apply_2(x_4, x_1, lean_box(0));
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_apply_4(x_5, x_8, x_9, x_10, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_isPrefixOf_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_List_Basic_0__List_isPrefixOf_match__1_splitter___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
lean_inc(x_1);
x_10 = lean_apply_2(x_1, x_6, x_8);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_1);
x_12 = lean_box(0);
return x_12;
}
else
{
x_2 = x_7;
x_3 = x_9;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPrefixOf_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_isPrefixOf_x3f___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_List_isSuffixOf___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_List_reverse___rarg(x_2);
x_5 = l_List_reverse___rarg(x_3);
x_6 = l_List_isPrefixOf___rarg(x_1, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_isSuffixOf___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_isSuffixOf___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_List_reverse___rarg(x_2);
x_5 = l_List_reverse___rarg(x_3);
x_6 = l_List_isPrefixOf_x3f___rarg(x_1, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = l_List_reverse___rarg(x_9);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = l_List_reverse___rarg(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_List_isSuffixOf_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_isSuffixOf_x3f___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_List_term___x3c_x3a_x2b_____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term_<:+_", 9, 9);
return x_1;
}
}
static lean_object* _init_l_List_term___x3c_x3a_x2b_____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_term___x3c_x2b_____closed__1;
x_2 = l_List_term___x3c_x3a_x2b_____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_term___x3c_x3a_x2b_____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" <:+ ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_List_term___x3c_x3a_x2b_____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_term___x3c_x3a_x2b_____closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_term___x3c_x3a_x2b_____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_List_term___x3c_x2b_____closed__5;
x_2 = l_List_term___x3c_x3a_x2b_____closed__4;
x_3 = l_List_term___x3c_x2b_____closed__10;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_List_term___x3c_x3a_x2b_____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_List_term___x3c_x3a_x2b_____closed__2;
x_2 = lean_unsigned_to_nat(50u);
x_3 = l_List_term___x3c_x3a_x2b_____closed__5;
x_4 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_3);
return x_4;
}
}
static lean_object* _init_l_List_term___x3c_x3a_x2b__() {
_start:
{
lean_object* x_1; 
x_1 = l_List_term___x3c_x3a_x2b_____closed__6;
return x_1;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IsSuffix", 8, 8);
return x_1;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_term___x3c_x2b_____closed__1;
x_2 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_List_term___x3c_x3a_x2b_____closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = lean_ctor_get(x_2, 5);
lean_inc(x_12);
x_13 = 0;
x_14 = l_Lean_SourceInfo_fromRef(x_12, x_13);
lean_dec(x_12);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__3;
x_18 = l_Lean_addMacroScope(x_16, x_17, x_15);
x_19 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__2;
x_20 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__6;
lean_inc(x_14);
x_21 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_20);
x_22 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__16;
lean_inc(x_14);
x_23 = l_Lean_Syntax_node2(x_14, x_22, x_9, x_11);
x_24 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5;
x_25 = l_Lean_Syntax_node2(x_14, x_24, x_21, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_3);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__2;
lean_inc(x_9);
x_11 = l_Lean_Syntax_isOfKind(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = lean_unsigned_to_nat(2u);
lean_inc(x_15);
x_17 = l_Lean_Syntax_matchesNull(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_9);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = l_Lean_Syntax_getArg(x_15, x_8);
x_21 = l_Lean_Syntax_getArg(x_15, x_14);
lean_dec(x_15);
x_22 = l_Lean_replaceRef(x_9, x_2);
lean_dec(x_9);
x_23 = 0;
x_24 = l_Lean_SourceInfo_fromRef(x_22, x_23);
lean_dec(x_22);
x_25 = l_List_term___x3c_x3a_x2b_____closed__3;
lean_inc(x_24);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_List_term___x3c_x3a_x2b_____closed__2;
x_28 = l_Lean_Syntax_node3(x_24, x_27, x_20, x_26, x_21);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_3);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_List_term___x3c_x3a_x2b_x3a_____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term_<:+:_", 10, 10);
return x_1;
}
}
static lean_object* _init_l_List_term___x3c_x3a_x2b_x3a_____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_term___x3c_x2b_____closed__1;
x_2 = l_List_term___x3c_x3a_x2b_x3a_____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_term___x3c_x3a_x2b_x3a_____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" <:+: ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_List_term___x3c_x3a_x2b_x3a_____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_term___x3c_x3a_x2b_x3a_____closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_term___x3c_x3a_x2b_x3a_____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_List_term___x3c_x2b_____closed__5;
x_2 = l_List_term___x3c_x3a_x2b_x3a_____closed__4;
x_3 = l_List_term___x3c_x2b_____closed__10;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_List_term___x3c_x3a_x2b_x3a_____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_List_term___x3c_x3a_x2b_x3a_____closed__2;
x_2 = lean_unsigned_to_nat(50u);
x_3 = l_List_term___x3c_x3a_x2b_x3a_____closed__5;
x_4 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_3);
return x_4;
}
}
static lean_object* _init_l_List_term___x3c_x3a_x2b_x3a__() {
_start:
{
lean_object* x_1; 
x_1 = l_List_term___x3c_x3a_x2b_x3a_____closed__6;
return x_1;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IsInfix", 7, 7);
return x_1;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_term___x3c_x2b_____closed__1;
x_2 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_List_term___x3c_x3a_x2b_x3a_____closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = lean_ctor_get(x_2, 5);
lean_inc(x_12);
x_13 = 0;
x_14 = l_Lean_SourceInfo_fromRef(x_12, x_13);
lean_dec(x_12);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__3;
x_18 = l_Lean_addMacroScope(x_16, x_17, x_15);
x_19 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__2;
x_20 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__6;
lean_inc(x_14);
x_21 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_20);
x_22 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__16;
lean_inc(x_14);
x_23 = l_Lean_Syntax_node2(x_14, x_22, x_9, x_11);
x_24 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5;
x_25 = l_Lean_Syntax_node2(x_14, x_24, x_21, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_3);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__2;
lean_inc(x_9);
x_11 = l_Lean_Syntax_isOfKind(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = lean_unsigned_to_nat(2u);
lean_inc(x_15);
x_17 = l_Lean_Syntax_matchesNull(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_9);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = l_Lean_Syntax_getArg(x_15, x_8);
x_21 = l_Lean_Syntax_getArg(x_15, x_14);
lean_dec(x_15);
x_22 = l_Lean_replaceRef(x_9, x_2);
lean_dec(x_9);
x_23 = 0;
x_24 = l_Lean_SourceInfo_fromRef(x_22, x_23);
lean_dec(x_22);
x_25 = l_List_term___x3c_x3a_x2b_x3a_____closed__3;
lean_inc(x_24);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_List_term___x3c_x3a_x2b_x3a_____closed__2;
x_28 = l_Lean_Syntax_node3(x_24, x_27, x_20, x_26, x_21);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_3);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_splitAt_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_3, x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_2, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_2, 0);
lean_dec(x_13);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_3, x_14);
lean_dec(x_3);
lean_ctor_set(x_2, 1, x_4);
{
lean_object* _tmp_1 = x_8;
lean_object* _tmp_2 = x_15;
lean_object* _tmp_3 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_3, x_17);
lean_dec(x_3);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_4);
x_2 = x_8;
x_3 = x_18;
x_4 = x_19;
goto _start;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_21 = l_List_reverse___rarg(x_4);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_2);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_List_splitAt_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_splitAt_go___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_splitAt___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
lean_inc(x_2);
x_4 = l_List_splitAt_go___rarg(x_2, x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_splitAt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_splitAt___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_rotateLeft___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_List_length___rarg(x_1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_nat_mod(x_2, x_3);
lean_dec(x_3);
lean_inc(x_1);
x_7 = l_List_take___rarg(x_6, x_1);
x_8 = l_List_drop___rarg(x_6, x_1);
lean_dec(x_1);
x_9 = l_List_appendTR___rarg(x_8, x_7);
return x_9;
}
else
{
lean_dec(x_3);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_List_rotateLeft(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_rotateLeft___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_rotateLeft___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_rotateLeft___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_rotateRight___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_List_length___rarg(x_1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_nat_mod(x_2, x_3);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_inc(x_1);
x_8 = l_List_take___rarg(x_7, x_1);
x_9 = l_List_drop___rarg(x_7, x_1);
lean_dec(x_1);
x_10 = l_List_appendTR___rarg(x_9, x_8);
return x_10;
}
else
{
lean_dec(x_3);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_List_rotateRight(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_rotateRight___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_rotateRight___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_rotateRight___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_List_instDecidablePairwise___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = 1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
lean_inc(x_5);
lean_inc(x_1);
x_6 = l_List_instDecidablePairwise___rarg(x_1, x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_apply_1(x_1, x_4);
x_9 = l_List_decidableBAll___rarg(x_8, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_List_instDecidablePairwise(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_instDecidablePairwise___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_instDecidablePairwise___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_instDecidablePairwise___rarg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_List_nodupDecidable___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; uint8_t x_6; 
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_instDecidableNot___rarg(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_List_nodupDecidable___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_alloc_closure((void*)(l_List_nodupDecidable___rarg___lambda__1___boxed), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_List_instDecidablePairwise___rarg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_nodupDecidable(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_nodupDecidable___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_nodupDecidable___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_nodupDecidable___rarg___lambda__1(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_nodupDecidable___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_nodupDecidable___rarg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_replace___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_3);
x_9 = lean_apply_2(x_1, x_3, x_7);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_List_replace___rarg(x_1, x_8, x_3, x_4);
lean_ctor_set(x_2, 1, x_11);
return x_2;
}
else
{
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_2, 0, x_4);
return x_2;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_12);
lean_inc(x_3);
x_14 = lean_apply_2(x_1, x_3, x_12);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_List_replace___rarg(x_1, x_13, x_3, x_4);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_1);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_replace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_replace___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_List_elem___rarg(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_dec(x_2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_List_insert(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_insert___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_erase___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_6);
x_8 = lean_apply_2(x_1, x_6, x_3);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_List_erase___rarg(x_1, x_7, x_3);
lean_ctor_set(x_2, 1, x_10);
return x_2;
}
else
{
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_11);
x_13 = lean_apply_2(x_1, x_11, x_3);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_List_erase___rarg(x_1, x_12, x_3);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_erase(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_erase___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLastD_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
x_5 = lean_apply_1(x_3, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_3(x_4, x_6, x_7, x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_getLastD_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_List_Basic_0__List_getLastD_match__1_splitter___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_eraseP___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
lean_inc(x_5);
x_7 = lean_apply_1(x_1, x_5);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_List_eraseP___rarg(x_1, x_6);
lean_ctor_set(x_2, 1, x_9);
return x_2;
}
else
{
lean_free_object(x_2);
lean_dec(x_5);
lean_dec(x_1);
return x_6;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_10);
x_12 = lean_apply_1(x_1, x_10);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_List_eraseP___rarg(x_1, x_11);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
lean_dec(x_10);
lean_dec(x_1);
return x_11;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseP(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_eraseP___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_2, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_2, x_9);
x_11 = l_List_eraseIdx___rarg(x_6, x_10);
lean_dec(x_10);
lean_ctor_set(x_1, 1, x_11);
return x_1;
}
else
{
lean_free_object(x_1);
lean_dec(x_5);
return x_6;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_2, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_2, x_16);
x_18 = l_List_eraseIdx___rarg(x_13, x_17);
lean_dec(x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
else
{
lean_dec(x_12);
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_eraseIdx___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdx___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_eraseIdx___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_4);
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_find_x3f___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_findSome_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
lean_inc(x_1);
x_6 = lean_apply_1(x_1, x_4);
if (lean_obj_tag(x_6) == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
lean_dec(x_5);
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_findSome_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_findSome_x3f___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
lean_inc(x_1);
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_3, x_8);
lean_dec(x_3);
x_2 = x_5;
x_3 = x_9;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_1);
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findIdx_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_findIdx_go___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_findIdx___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_List_findIdx_go___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_findIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_findIdx___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_go___at_List_indexOf___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_7 = lean_apply_2(x_1, x_5, x_2);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_4, x_9);
lean_dec(x_4);
x_3 = x_6;
x_4 = x_10;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findIdx_go___at_List_indexOf___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_findIdx_go___at_List_indexOf___spec__1___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_indexOf___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_List_findIdx_go___at_List_indexOf___spec__1___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_indexOf(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_indexOf___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
lean_inc(x_1);
x_7 = lean_apply_1(x_1, x_5);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_2 = x_6;
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findIdx_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_findIdx_x3f___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_indexOf_x3f___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_indexOf_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_List_indexOf_x3f___rarg___lambda__1), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_List_findIdx_x3f___rarg(x_4, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_indexOf_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_indexOf_x3f___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_countP_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
lean_inc(x_1);
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_2 = x_5;
x_3 = x_10;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_countP_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_countP_go___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_countP___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_List_countP_go___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_countP(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_countP___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_countP_go___at_List_count___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_7 = lean_apply_2(x_1, x_5, x_2);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_3 = x_6;
x_4 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_countP_go___at_List_count___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_countP_go___at_List_count___spec__1___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_count___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_List_countP_go___at_List_count___spec__1___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_count(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_count___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_lookup___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
lean_inc(x_1);
lean_inc(x_2);
x_9 = lean_apply_2(x_1, x_2, x_7);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_8);
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_8);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_List_lookup(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_lookup___rarg), 3, 0);
return x_3;
}
}
static lean_object* _init_l_List_term___x7e_____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term_~_", 7, 7);
return x_1;
}
}
static lean_object* _init_l_List_term___x7e_____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_term___x3c_x2b_____closed__1;
x_2 = l_List_term___x7e_____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_term___x7e_____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ~ ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_List_term___x7e_____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_term___x7e_____closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_term___x7e_____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_List_term___x3c_x2b_____closed__5;
x_2 = l_List_term___x7e_____closed__4;
x_3 = l_List_term___x3c_x2b_____closed__10;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_List_term___x7e_____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_List_term___x7e_____closed__2;
x_2 = lean_unsigned_to_nat(50u);
x_3 = l_List_term___x7e_____closed__5;
x_4 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_3);
return x_4;
}
}
static lean_object* _init_l_List_term___x7e__() {
_start:
{
lean_object* x_1; 
x_1 = l_List_term___x7e_____closed__6;
return x_1;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Perm", 4, 4);
return x_1;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_term___x3c_x2b_____closed__1;
x_2 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__6;
x_2 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__5;
x_2 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_List_term___x7e_____closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = lean_ctor_get(x_2, 5);
lean_inc(x_12);
x_13 = 0;
x_14 = l_Lean_SourceInfo_fromRef(x_12, x_13);
lean_dec(x_12);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__3;
x_18 = l_Lean_addMacroScope(x_16, x_17, x_15);
x_19 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__2;
x_20 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__9;
lean_inc(x_14);
x_21 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_20);
x_22 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__16;
lean_inc(x_14);
x_23 = l_Lean_Syntax_node2(x_14, x_22, x_9, x_11);
x_24 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5;
x_25 = l_Lean_Syntax_node2(x_14, x_24, x_21, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_3);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__2;
lean_inc(x_9);
x_11 = l_Lean_Syntax_isOfKind(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = lean_unsigned_to_nat(2u);
lean_inc(x_15);
x_17 = l_Lean_Syntax_matchesNull(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_9);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = l_Lean_Syntax_getArg(x_15, x_8);
x_21 = l_Lean_Syntax_getArg(x_15, x_14);
lean_dec(x_15);
x_22 = l_Lean_replaceRef(x_9, x_2);
lean_dec(x_9);
x_23 = 0;
x_24 = l_Lean_SourceInfo_fromRef(x_22, x_23);
lean_dec(x_22);
x_25 = l_List_term___x7e_____closed__3;
lean_inc(x_24);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_List_term___x7e_____closed__2;
x_28 = l_Lean_Syntax_node3(x_24, x_27, x_20, x_26, x_21);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_3);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_List_isPerm___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = l_List_isEmpty___rarg(x_3);
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
lean_inc(x_3);
lean_inc(x_5);
lean_inc(x_1);
x_7 = l_List_elem___rarg(x_1, x_5, x_3);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = l_List_erase___rarg(x_1, x_3, x_5);
x_2 = x_6;
x_3 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPerm(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_isPerm___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_isPerm___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_isPerm___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_List_any___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
lean_dec(x_2);
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
lean_inc(x_2);
x_6 = lean_apply_1(x_2, x_4);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
x_1 = x_5;
goto _start;
}
else
{
uint8_t x_9; 
lean_dec(x_5);
lean_dec(x_2);
x_9 = 1;
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_any___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_any___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_any___rarg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_List_all___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
lean_dec(x_2);
x_3 = 1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
lean_inc(x_2);
x_6 = lean_apply_1(x_2, x_4);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
lean_dec(x_2);
x_8 = 0;
return x_8;
}
else
{
x_1 = x_5;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_all___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_all___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_all___rarg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_List_or___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_List_or(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_List_or___closed__1;
x_3 = l_List_any___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_or___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_List_or(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_List_and(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_List_or___closed__1;
x_3 = l_List_all___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_and___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_List_and(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_zipWith___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
x_11 = lean_apply_2(x_1, x_6, x_9);
x_12 = l_List_zipWith___rarg(x_1, x_7, x_10);
lean_ctor_set(x_3, 1, x_12);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
lean_inc(x_1);
x_15 = lean_apply_2(x_1, x_6, x_13);
x_16 = l_List_zipWith___rarg(x_1, x_7, x_14);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWith(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_List_zipWith___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_zipWith_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_apply_3(x_4, x_1, x_2, lean_box(0));
return x_5;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_apply_3(x_4, x_1, x_2, lean_box(0));
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_apply_4(x_3, x_7, x_8, x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_zipWith_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Init_Data_List_Basic_0__List_zipWith_match__1_splitter___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_zipWith___at_List_zip___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_8);
x_10 = l_List_zipWith___at_List_zip___spec__1___rarg(x_7, x_9);
lean_ctor_set(x_2, 1, x_10);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_12);
x_14 = l_List_zipWith___at_List_zip___spec__1___rarg(x_11, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_1);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_20 = x_2;
} else {
 lean_dec_ref(x_2);
 x_20 = lean_box(0);
}
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_18);
x_22 = l_List_zipWith___at_List_zip___spec__1___rarg(x_17, x_19);
if (lean_is_scalar(x_20)) {
 x_23 = lean_alloc_ctor(1, 2, 0);
} else {
 x_23 = x_20;
}
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWith___at_List_zip___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_zipWith___at_List_zip___spec__1___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_zip___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_zipWith___at_List_zip___spec__1___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_zip(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_zip___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_map___at_List_zipWithAll___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_5);
lean_inc(x_1);
x_9 = lean_apply_2(x_1, x_7, x_8);
x_10 = l_List_map___at_List_zipWithAll___spec__1___rarg(x_1, x_6);
lean_ctor_set(x_2, 1, x_10);
lean_ctor_set(x_2, 0, x_9);
return x_2;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_11);
lean_inc(x_1);
x_15 = lean_apply_2(x_1, x_13, x_14);
x_16 = l_List_map___at_List_zipWithAll___spec__1___rarg(x_1, x_12);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_List_map___at_List_zipWithAll___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_List_map___at_List_zipWithAll___spec__1___rarg), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_map___at_List_zipWithAll___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_5);
x_8 = lean_box(0);
lean_inc(x_1);
x_9 = lean_apply_2(x_1, x_7, x_8);
x_10 = l_List_map___at_List_zipWithAll___spec__2___rarg(x_1, x_6);
lean_ctor_set(x_2, 1, x_10);
lean_ctor_set(x_2, 0, x_9);
return x_2;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = lean_box(0);
lean_inc(x_1);
x_15 = lean_apply_2(x_1, x_13, x_14);
x_16 = l_List_map___at_List_zipWithAll___spec__2___rarg(x_1, x_12);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_List_map___at_List_zipWithAll___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_List_map___at_List_zipWithAll___spec__2___rarg), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = l_List_map___at_List_zipWithAll___spec__1___rarg(x_1, x_3);
return x_4;
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_List_map___at_List_zipWithAll___spec__2___rarg(x_1, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_2);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_List_map___at_List_zipWithAll___spec__2___rarg(x_1, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
lean_inc(x_1);
x_18 = lean_apply_2(x_1, x_16, x_17);
x_19 = l_List_zipWithAll___rarg(x_1, x_12, x_15);
lean_ctor_set(x_3, 1, x_19);
lean_ctor_set(x_3, 0, x_18);
return x_3;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_3);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_11);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_20);
lean_inc(x_1);
x_24 = lean_apply_2(x_1, x_22, x_23);
x_25 = l_List_zipWithAll___rarg(x_1, x_12, x_21);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_List_zipWithAll___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_unzip___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_partition___rarg___closed__1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = l_List_unzip___rarg(x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_7);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 1, x_12);
lean_ctor_set(x_4, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_7);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 1, x_14);
lean_ctor_set(x_4, 0, x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
x_19 = l_List_unzip___rarg(x_16);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_22 = x_19;
} else {
 lean_dec_ref(x_19);
 x_22 = lean_box(0);
}
lean_ctor_set(x_1, 1, x_20);
lean_ctor_set(x_1, 0, x_17);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_21);
if (lean_is_scalar(x_22)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_22;
}
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_1);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_29 = x_25;
} else {
 lean_dec_ref(x_25);
 x_29 = lean_box(0);
}
x_30 = l_List_unzip___rarg(x_26);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_31);
if (lean_is_scalar(x_29)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_29;
 lean_ctor_set_tag(x_35, 1);
}
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_32);
if (lean_is_scalar(x_33)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_33;
}
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_List_unzip(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_unzip___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at_Nat_sum___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_List_foldr___at_Nat_sum___spec__1(x_1, x_4);
x_6 = lean_nat_add(x_3, x_5);
lean_dec(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Nat_sum(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_List_foldr___at_Nat_sum___spec__1(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at_Nat_sum___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldr___at_Nat_sum___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_sum___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_sum(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_range_loop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_1, x_5);
lean_dec(x_1);
lean_inc(x_6);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_1 = x_6;
x_2 = x_7;
goto _start;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_List_range(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_List_range_loop(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_range_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = lean_nat_add(x_1, x_3);
x_9 = l_List_range_x27(x_8, x_7, x_3);
lean_dec(x_7);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_box(0);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_List_range_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_range_x27(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_iota(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_1, x_4);
x_6 = l_List_iota(x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_List_enumFrom___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_5);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_1, x_8);
lean_dec(x_1);
x_10 = l_List_enumFrom___rarg(x_9, x_6);
lean_ctor_set(x_2, 1, x_10);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_1, x_14);
lean_dec(x_1);
x_16 = l_List_enumFrom___rarg(x_15, x_12);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_List_enumFrom(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_enumFrom___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_enum___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_List_enumFrom___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_enum(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_enum___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_min_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_List_foldl___rarg(x_1, x_4, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_List_min_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_min_x3f___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_minimum_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_min_x3f___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_minimum_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_minimum_x3f___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_List_foldl___rarg(x_1, x_4, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_List_max_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_max_x3f___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_maximum_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_max_x3f___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_maximum_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_maximum_x3f___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_intersperse___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 1);
lean_dec(x_6);
x_7 = lean_box(0);
lean_ctor_set(x_2, 1, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_2, 1);
lean_dec(x_12);
lean_inc(x_4);
lean_inc(x_1);
x_13 = l_List_intersperse___rarg(x_1, x_4);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_4, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_4, 0);
lean_dec(x_16);
lean_ctor_set(x_4, 1, x_13);
lean_ctor_set(x_4, 0, x_1);
return x_2;
}
else
{
lean_object* x_17; 
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_2, 1, x_17);
return x_2;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
lean_inc(x_4);
lean_inc(x_1);
x_19 = l_List_intersperse___rarg(x_1, x_4);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_20 = x_4;
} else {
 lean_dec_ref(x_4);
 x_20 = lean_box(0);
}
if (lean_is_scalar(x_20)) {
 x_21 = lean_alloc_ctor(1, 2, 0);
} else {
 x_21 = x_20;
}
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_intersperse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_intersperse___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_intercalate___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_List_intersperse___rarg(x_1, x_2);
x_4 = l_List_join___rarg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_intercalate(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_intercalate___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_inc(x_6);
lean_inc(x_1);
x_8 = l_List_elem___rarg(x_1, x_6, x_3);
if (x_8 == 0)
{
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_free_object(x_2);
lean_dec(x_6);
x_2 = x_7;
goto _start;
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_3);
lean_inc(x_11);
lean_inc(x_1);
x_13 = l_List_elem___rarg(x_1, x_11, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_3);
x_2 = x_12;
x_3 = x_14;
goto _start;
}
else
{
lean_dec(x_11);
x_2 = x_12;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseDups_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_eraseDups_loop___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_List_eraseDups_loop___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_eraseDups___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_eraseReps_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_List_reverse___rarg(x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_2);
x_10 = lean_apply_2(x_1, x_2, x_8);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_2);
{
lean_object* _tmp_1 = x_8;
lean_object* _tmp_2 = x_9;
lean_object* _tmp_3 = x_3;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_free_object(x_3);
lean_dec(x_8);
x_3 = x_9;
goto _start;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_14);
lean_inc(x_2);
x_16 = lean_apply_2(x_1, x_2, x_14);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_4);
x_2 = x_14;
x_3 = x_15;
x_4 = x_18;
goto _start;
}
else
{
lean_dec(x_14);
x_3 = x_15;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseReps_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_eraseReps_loop___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_eraseReps___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = l_List_eraseReps_loop___rarg(x_1, x_4, x_5, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_List_eraseReps(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_eraseReps___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_span_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
lean_inc(x_8);
x_10 = lean_apply_1(x_1, x_8);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = l_List_reverse___rarg(x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
return x_13;
}
else
{
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_9;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_15);
x_17 = lean_apply_1(x_1, x_15);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_19 = l_List_reverse___rarg(x_3);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_3);
x_2 = x_16;
x_3 = x_22;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_span_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_span_loop___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_span___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_List_span_loop___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_span(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_span___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_groupBy_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
x_7 = l_List_reverse___rarg(x_6);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
x_9 = l_List_reverse___rarg(x_8);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
lean_inc(x_11);
lean_inc(x_3);
x_13 = lean_apply_2(x_1, x_3, x_11);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_box(0);
lean_ctor_set(x_2, 1, x_4);
lean_ctor_set(x_2, 0, x_3);
x_16 = l_List_reverse___rarg(x_2);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_5);
x_2 = x_12;
x_3 = x_11;
x_4 = x_15;
x_5 = x_17;
goto _start;
}
else
{
lean_ctor_set(x_2, 1, x_4);
lean_ctor_set(x_2, 0, x_3);
{
lean_object* _tmp_1 = x_12;
lean_object* _tmp_2 = x_11;
lean_object* _tmp_3 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_20);
lean_inc(x_3);
x_22 = lean_apply_2(x_1, x_3, x_20);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_4);
x_26 = l_List_reverse___rarg(x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_5);
x_2 = x_21;
x_3 = x_20;
x_4 = x_24;
x_5 = x_27;
goto _start;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_3);
lean_ctor_set(x_29, 1, x_4);
x_2 = x_21;
x_3 = x_20;
x_4 = x_29;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_groupBy_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_groupBy_loop___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_groupBy___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = l_List_groupBy_loop___rarg(x_1, x_5, x_4, x_6, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_List_groupBy(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_groupBy___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_List_removeAll___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_List_elem___rarg(x_1, x_3, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_List_removeAll___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_List_removeAll___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
x_5 = l_List_filter___rarg(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_removeAll(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_removeAll___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_removeAll___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_removeAll___rarg___lambda__1(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_length_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_3, x_4, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_length_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_List_Basic_0__List_length_match__1_splitter___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_length_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_List_Basic_0__List_length_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_lengthTRAux_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
x_5 = lean_apply_1(x_3, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_3(x_4, x_6, x_7, x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_lengthTRAux_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_List_Basic_0__List_lengthTRAux_match__1_splitter___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_8 = lean_apply_1(x_1, x_6);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_12 = lean_apply_1(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_mapTR_loop___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapTR___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_List_mapTR_loop___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTR(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_mapTR___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_mapTR_loop_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
x_5 = lean_apply_1(x_3, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_3(x_4, x_6, x_7, x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_mapTR_loop_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Init_Data_List_Basic_0__List_mapTR_loop_match__1_splitter___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
lean_inc(x_6);
x_8 = lean_apply_1(x_1, x_6);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_free_object(x_2);
lean_dec(x_6);
x_2 = x_7;
goto _start;
}
else
{
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_12);
x_14 = lean_apply_1(x_1, x_12);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_12);
x_2 = x_13;
goto _start;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_3);
x_2 = x_13;
x_3 = x_17;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_filterTR_loop___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_filterTR___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_List_filterTR_loop___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_filterTR(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_filterTR___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_replicateTR_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
lean_dec(x_2);
lean_inc(x_1);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_3);
x_2 = x_7;
x_3 = x_8;
goto _start;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_List_replicateTR_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_replicateTR_loop___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_replicateTR___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_List_replicateTR_loop___rarg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_replicateTR(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_replicateTR___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_1, x_7);
x_9 = lean_apply_2(x_4, x_8, x_2);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_apply_1(x_3, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_1, x_7);
x_9 = lean_apply_2(x_4, x_8, x_2);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_apply_1(x_3, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_List_lengthTRAux___rarg(x_3, x_4);
x_6 = lean_nat_sub(x_1, x_5);
lean_dec(x_5);
x_7 = l_List_replicateTR_loop___rarg(x_2, x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_leftpadTR___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_leftpadTR___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_leftpadTR___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at_List_unzipTR___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_List_foldr___at_List_unzipTR___spec__1___rarg(x_1, x_5);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_ctor_set(x_2, 1, x_11);
lean_ctor_set(x_2, 0, x_9);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 1, x_12);
lean_ctor_set(x_4, 0, x_10);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
lean_ctor_set(x_2, 1, x_15);
lean_ctor_set(x_2, 0, x_13);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 1, x_16);
lean_ctor_set(x_4, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_4);
x_20 = lean_ctor_get(x_6, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_22 = x_6;
} else {
 lean_dec_ref(x_6);
 x_22 = lean_box(0);
}
lean_ctor_set(x_2, 1, x_20);
lean_ctor_set(x_2, 0, x_18);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_21);
if (lean_is_scalar(x_22)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_22;
}
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
x_27 = l_List_foldr___at_List_unzipTR___spec__1___rarg(x_1, x_26);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_30 = x_25;
} else {
 lean_dec_ref(x_25);
 x_30 = lean_box(0);
}
x_31 = lean_ctor_get(x_27, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_33 = x_27;
} else {
 lean_dec_ref(x_27);
 x_33 = lean_box(0);
}
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_31);
if (lean_is_scalar(x_30)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_30;
 lean_ctor_set_tag(x_35, 1);
}
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_32);
if (lean_is_scalar(x_33)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_33;
}
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at_List_unzipTR___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_foldr___at_List_unzipTR___spec__1___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_unzipTR___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_List_partition___rarg___closed__1;
x_3 = l_List_foldr___at_List_unzipTR___spec__1___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_unzipTR(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_unzipTR___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at_List_unzipTR___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldr___at_List_unzipTR___spec__1___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_2, x_7);
lean_dec(x_2);
x_9 = lean_nat_sub(x_3, x_1);
lean_dec(x_3);
lean_inc(x_9);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
x_2 = x_8;
x_3 = x_9;
x_4 = x_10;
goto _start;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_range_x27TR_go(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_nat_mul(x_3, x_2);
x_5 = lean_nat_add(x_1, x_4);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = l_List_range_x27TR_go(x_3, x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_range_x27TR___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_range_x27TR(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_1, x_8);
x_10 = lean_apply_3(x_5, x_9, x_2, x_3);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_5);
x_11 = lean_apply_2(x_4, x_2, x_3);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_iotaTR_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_1, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
x_1 = x_6;
x_2 = x_7;
goto _start;
}
else
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = l_List_reverse___rarg(x_2);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_List_iotaTR(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_List_iotaTR_go(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_iota_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
else
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_iota_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_List_Basic_0__List_iota_match__1_splitter___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_iota_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_List_Basic_0__List_iota_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_iotaTR_go_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_1, x_7);
x_9 = lean_apply_2(x_4, x_8, x_2);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_apply_1(x_3, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_iotaTR_go_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_List_Basic_0__List_iotaTR_go_match__1_splitter___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_iotaTR_go_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_List_Basic_0__List_iotaTR_go_match__1_splitter___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at_List_intersperseTR___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
x_6 = l_List_foldr___at_List_intersperseTR___spec__1___rarg(x_1, x_2, x_5);
lean_ctor_set(x_3, 1, x_6);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
lean_inc(x_1);
x_10 = l_List_foldr___at_List_intersperseTR___spec__1___rarg(x_1, x_2, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at_List_intersperseTR___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldr___at_List_intersperseTR___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_intersperseTR___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 1);
lean_dec(x_6);
x_7 = lean_box(0);
lean_ctor_set(x_2, 1, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_4, 1);
x_16 = lean_box(0);
lean_inc(x_1);
x_17 = l_List_foldr___at_List_intersperseTR___spec__1___rarg(x_1, x_16, x_15);
lean_ctor_set(x_4, 1, x_17);
lean_ctor_set(x_2, 0, x_1);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_4);
x_21 = lean_box(0);
lean_inc(x_1);
x_22 = l_List_foldr___at_List_intersperseTR___spec__1___rarg(x_1, x_21, x_20);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_2, 1, x_23);
lean_ctor_set(x_2, 0, x_1);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_2);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_2, 0);
lean_inc(x_25);
lean_dec(x_2);
x_26 = lean_ctor_get(x_4, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_4, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_28 = x_4;
} else {
 lean_dec_ref(x_4);
 x_28 = lean_box(0);
}
x_29 = lean_box(0);
lean_inc(x_1);
x_30 = l_List_foldr___at_List_intersperseTR___spec__1___rarg(x_1, x_29, x_27);
if (lean_is_scalar(x_28)) {
 x_31 = lean_alloc_ctor(1, 2, 0);
} else {
 x_31 = x_28;
}
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_intersperseTR(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_intersperseTR___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at_List_intersperseTR___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldr___at_List_intersperseTR___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_intersperseTR_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_apply_3(x_4, x_8, x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_intersperseTR_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_List_Basic_0__List_intersperseTR_match__1_splitter___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Basic_0__List_intersperseTR_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_List_Basic_0__List_intersperseTR_match__1_splitter___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Init_SimpLemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Nat_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Notation(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_SimpLemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Notation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_List_instAppend___closed__1 = _init_l_List_instAppend___closed__1();
lean_mark_persistent(l_List_instAppend___closed__1);
l_List_partition___rarg___closed__1 = _init_l_List_partition___rarg___closed__1();
lean_mark_persistent(l_List_partition___rarg___closed__1);
l_List_term___x3c_x2b_____closed__1 = _init_l_List_term___x3c_x2b_____closed__1();
lean_mark_persistent(l_List_term___x3c_x2b_____closed__1);
l_List_term___x3c_x2b_____closed__2 = _init_l_List_term___x3c_x2b_____closed__2();
lean_mark_persistent(l_List_term___x3c_x2b_____closed__2);
l_List_term___x3c_x2b_____closed__3 = _init_l_List_term___x3c_x2b_____closed__3();
lean_mark_persistent(l_List_term___x3c_x2b_____closed__3);
l_List_term___x3c_x2b_____closed__4 = _init_l_List_term___x3c_x2b_____closed__4();
lean_mark_persistent(l_List_term___x3c_x2b_____closed__4);
l_List_term___x3c_x2b_____closed__5 = _init_l_List_term___x3c_x2b_____closed__5();
lean_mark_persistent(l_List_term___x3c_x2b_____closed__5);
l_List_term___x3c_x2b_____closed__6 = _init_l_List_term___x3c_x2b_____closed__6();
lean_mark_persistent(l_List_term___x3c_x2b_____closed__6);
l_List_term___x3c_x2b_____closed__7 = _init_l_List_term___x3c_x2b_____closed__7();
lean_mark_persistent(l_List_term___x3c_x2b_____closed__7);
l_List_term___x3c_x2b_____closed__8 = _init_l_List_term___x3c_x2b_____closed__8();
lean_mark_persistent(l_List_term___x3c_x2b_____closed__8);
l_List_term___x3c_x2b_____closed__9 = _init_l_List_term___x3c_x2b_____closed__9();
lean_mark_persistent(l_List_term___x3c_x2b_____closed__9);
l_List_term___x3c_x2b_____closed__10 = _init_l_List_term___x3c_x2b_____closed__10();
lean_mark_persistent(l_List_term___x3c_x2b_____closed__10);
l_List_term___x3c_x2b_____closed__11 = _init_l_List_term___x3c_x2b_____closed__11();
lean_mark_persistent(l_List_term___x3c_x2b_____closed__11);
l_List_term___x3c_x2b_____closed__12 = _init_l_List_term___x3c_x2b_____closed__12();
lean_mark_persistent(l_List_term___x3c_x2b_____closed__12);
l_List_term___x3c_x2b__ = _init_l_List_term___x3c_x2b__();
lean_mark_persistent(l_List_term___x3c_x2b__);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__2 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__2();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__2);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__4 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__4();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__4);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__6 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__6();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__6);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__7 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__7();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__7);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__8 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__8();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__8);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__9 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__9();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__9);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__10 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__10();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__10);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__11 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__11();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__11);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__12 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__12();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__12);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__13 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__13();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__13);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__14 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__14();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__14);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__15 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__15();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__15);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__16 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__16();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__16);
l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1 = _init_l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1);
l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__2 = _init_l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__2();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__2);
l_List_term___x3c_x2b_x3a_____closed__1 = _init_l_List_term___x3c_x2b_x3a_____closed__1();
lean_mark_persistent(l_List_term___x3c_x2b_x3a_____closed__1);
l_List_term___x3c_x2b_x3a_____closed__2 = _init_l_List_term___x3c_x2b_x3a_____closed__2();
lean_mark_persistent(l_List_term___x3c_x2b_x3a_____closed__2);
l_List_term___x3c_x2b_x3a_____closed__3 = _init_l_List_term___x3c_x2b_x3a_____closed__3();
lean_mark_persistent(l_List_term___x3c_x2b_x3a_____closed__3);
l_List_term___x3c_x2b_x3a_____closed__4 = _init_l_List_term___x3c_x2b_x3a_____closed__4();
lean_mark_persistent(l_List_term___x3c_x2b_x3a_____closed__4);
l_List_term___x3c_x2b_x3a_____closed__5 = _init_l_List_term___x3c_x2b_x3a_____closed__5();
lean_mark_persistent(l_List_term___x3c_x2b_x3a_____closed__5);
l_List_term___x3c_x2b_x3a_____closed__6 = _init_l_List_term___x3c_x2b_x3a_____closed__6();
lean_mark_persistent(l_List_term___x3c_x2b_x3a_____closed__6);
l_List_term___x3c_x2b_x3a__ = _init_l_List_term___x3c_x2b_x3a__();
lean_mark_persistent(l_List_term___x3c_x2b_x3a__);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__2 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__2();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__2);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__3 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__3();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__3);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__4 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__4();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__4);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__5 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__5();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__5);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__6 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__6();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__6);
l_List_term___x3c_x3a_x2b_____closed__1 = _init_l_List_term___x3c_x3a_x2b_____closed__1();
lean_mark_persistent(l_List_term___x3c_x3a_x2b_____closed__1);
l_List_term___x3c_x3a_x2b_____closed__2 = _init_l_List_term___x3c_x3a_x2b_____closed__2();
lean_mark_persistent(l_List_term___x3c_x3a_x2b_____closed__2);
l_List_term___x3c_x3a_x2b_____closed__3 = _init_l_List_term___x3c_x3a_x2b_____closed__3();
lean_mark_persistent(l_List_term___x3c_x3a_x2b_____closed__3);
l_List_term___x3c_x3a_x2b_____closed__4 = _init_l_List_term___x3c_x3a_x2b_____closed__4();
lean_mark_persistent(l_List_term___x3c_x3a_x2b_____closed__4);
l_List_term___x3c_x3a_x2b_____closed__5 = _init_l_List_term___x3c_x3a_x2b_____closed__5();
lean_mark_persistent(l_List_term___x3c_x3a_x2b_____closed__5);
l_List_term___x3c_x3a_x2b_____closed__6 = _init_l_List_term___x3c_x3a_x2b_____closed__6();
lean_mark_persistent(l_List_term___x3c_x3a_x2b_____closed__6);
l_List_term___x3c_x3a_x2b__ = _init_l_List_term___x3c_x3a_x2b__();
lean_mark_persistent(l_List_term___x3c_x3a_x2b__);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__2 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__2();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__2);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__3 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__3();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__3);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__4 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__4();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__4);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__5 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__5();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__5);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__6 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__6();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__6);
l_List_term___x3c_x3a_x2b_x3a_____closed__1 = _init_l_List_term___x3c_x3a_x2b_x3a_____closed__1();
lean_mark_persistent(l_List_term___x3c_x3a_x2b_x3a_____closed__1);
l_List_term___x3c_x3a_x2b_x3a_____closed__2 = _init_l_List_term___x3c_x3a_x2b_x3a_____closed__2();
lean_mark_persistent(l_List_term___x3c_x3a_x2b_x3a_____closed__2);
l_List_term___x3c_x3a_x2b_x3a_____closed__3 = _init_l_List_term___x3c_x3a_x2b_x3a_____closed__3();
lean_mark_persistent(l_List_term___x3c_x3a_x2b_x3a_____closed__3);
l_List_term___x3c_x3a_x2b_x3a_____closed__4 = _init_l_List_term___x3c_x3a_x2b_x3a_____closed__4();
lean_mark_persistent(l_List_term___x3c_x3a_x2b_x3a_____closed__4);
l_List_term___x3c_x3a_x2b_x3a_____closed__5 = _init_l_List_term___x3c_x3a_x2b_x3a_____closed__5();
lean_mark_persistent(l_List_term___x3c_x3a_x2b_x3a_____closed__5);
l_List_term___x3c_x3a_x2b_x3a_____closed__6 = _init_l_List_term___x3c_x3a_x2b_x3a_____closed__6();
lean_mark_persistent(l_List_term___x3c_x3a_x2b_x3a_____closed__6);
l_List_term___x3c_x3a_x2b_x3a__ = _init_l_List_term___x3c_x3a_x2b_x3a__();
lean_mark_persistent(l_List_term___x3c_x3a_x2b_x3a__);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__2 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__2();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__2);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__3 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__3();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__3);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__4 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__4();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__4);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__5 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__5();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__5);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__6 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__6();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__6);
l_List_term___x7e_____closed__1 = _init_l_List_term___x7e_____closed__1();
lean_mark_persistent(l_List_term___x7e_____closed__1);
l_List_term___x7e_____closed__2 = _init_l_List_term___x7e_____closed__2();
lean_mark_persistent(l_List_term___x7e_____closed__2);
l_List_term___x7e_____closed__3 = _init_l_List_term___x7e_____closed__3();
lean_mark_persistent(l_List_term___x7e_____closed__3);
l_List_term___x7e_____closed__4 = _init_l_List_term___x7e_____closed__4();
lean_mark_persistent(l_List_term___x7e_____closed__4);
l_List_term___x7e_____closed__5 = _init_l_List_term___x7e_____closed__5();
lean_mark_persistent(l_List_term___x7e_____closed__5);
l_List_term___x7e_____closed__6 = _init_l_List_term___x7e_____closed__6();
lean_mark_persistent(l_List_term___x7e_____closed__6);
l_List_term___x7e__ = _init_l_List_term___x7e__();
lean_mark_persistent(l_List_term___x7e__);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__2 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__2();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__2);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__3 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__3();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__3);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__4 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__4();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__4);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__5 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__5();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__5);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__6 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__6();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__6);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__7 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__7();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__7);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__8 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__8();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__8);
l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__9 = _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__9();
lean_mark_persistent(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__9);
l_List_or___closed__1 = _init_l_List_or___closed__1();
lean_mark_persistent(l_List_or___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Lean.Level
// Imports: Init Std.Data.HashMap Std.Data.HashSet Std.Data.PersistentHashMap Std.Data.PersistentHashSet Lean.Hygiene Lean.Data.Name Lean.Data.Format
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
lean_object* l_Lean_Level_dec(lean_object*);
lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(lean_object*, lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_Level_instantiateParams_match__1(lean_object*);
lean_object* l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsort_sort___at_Lean_Level_normalize___spec__2___closed__1;
lean_object* l_Lean_Level_getOffsetAux_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
uint8_t l_Lean_Level_isNeverZero(lean_object*);
extern lean_object* l_Lean_Name_getString_x21___closed__3;
lean_object* l_Array_qsort_sort___at_Lean_Level_normalize___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_isMax___boxed(lean_object*);
lean_object* l_Lean_Level_isSucc_match__1(lean_object*);
lean_object* l_Lean_Level_collectMVars(lean_object*, lean_object*);
lean_object* l_Lean_Level_mvarId_x21___closed__2;
extern lean_object* l_Lean_myMacro____x40_Init_NotationExtra___hyg_1136____closed__30;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_precMax___closed__3;
lean_object* l_Lean_Level_PP_Result_format___closed__4;
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t l_UInt64_decEq(uint64_t, uint64_t);
lean_object* l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_data___boxed(lean_object*);
lean_object* l_Lean_Level_mvarId_x21___closed__1;
lean_object* l_Lean_Level_mvarId_x21___boxed(lean_object*);
size_t l_UInt32_toUSize(uint32_t);
lean_object* l_Lean_Level_PP_Result_format___closed__1;
lean_object* l_Lean_Level_collectMVars_match__1(lean_object*);
lean_object* l_Lean_Level_quote___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Level_instantiateParams_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Level_isMVar___boxed(lean_object*);
lean_object* l_Lean_Level_updateIMax___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qpartition_loop___at_Lean_Level_normalize___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_mkData___closed__3;
extern lean_object* l_Std_Format_defWidth;
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint64_t l_UInt64_add(uint64_t, uint64_t);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*);
lean_object* l_Lean_Level_isExplicit_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Bool_toUInt64(uint8_t);
lean_object* l___private_Lean_Level_0__Lean_Level_mkIMaxAux(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Level_PP_Result_quote___spec__2(size_t, size_t, lean_object*);
lean_object* l_Lean_Level_getOffsetAux___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Level_updateMax_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_normLtAux_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_level_mk_max(lean_object*, lean_object*);
lean_object* l_Lean_Level_instHashableLevel___closed__1;
lean_object* l_Lean_Level_instToStringLevel(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Level_mkData___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_mkData___closed__1;
lean_object* l_Lean_Level_ctorToNat___boxed(lean_object*);
lean_object* lean_level_mk_succ(lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
lean_object* l_Lean_Level_data_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Level_PP_Result_quote___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Level_hasMVarEx___boxed(lean_object*);
lean_object* l_Lean_Level_mkData___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Level_PP_Result_quote_match__1(lean_object*);
uint8_t l_Lean_Level_isEquiv(lean_object*, lean_object*);
lean_object* l_Lean_Level_find_x3f_visit_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_PP_Result_imax_match__1(lean_object*);
lean_object* l_Lean_Level_instBEqLevel;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Level_PP_Result_quote___spec__1(lean_object*, lean_object*);
uint8_t lean_level_has_param(lean_object*);
size_t l_Lean_Level_hash(lean_object*);
lean_object* l_Lean_Level_PP_Result_quote_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_isExplicit___boxed(lean_object*);
size_t lean_level_hash(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Level_hasParamEx___boxed(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Level_isMVar_match__1(lean_object*);
lean_object* l_Lean_Level_mkData___closed__4;
lean_object* l_Nat_max(lean_object*, lean_object*);
lean_object* l_Lean_Level_PP_toResult___closed__1;
lean_object* l_Lean_Level_getOffsetAux(lean_object*, lean_object*);
uint8_t l_Lean_Level_hasParam(lean_object*);
lean_object* l_Lean_Level_depth(lean_object*);
extern lean_object* l_Std_Format_paren___closed__2;
lean_object* l_Lean_Level_isSucc___boxed(lean_object*);
lean_object* l_Lean_Level_updateIMax_x21___closed__1;
uint8_t l___private_Lean_Level_0__Lean_Level_isAlreadyNormalizedCheap(lean_object*);
lean_object* l_Lean_Level_mvarId_x21(lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Lean_Level_instToFormatLevel(lean_object*);
lean_object* l_Lean_levelZero;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Level_updateMax_x21___closed__2;
lean_object* l_Lean_Level_PP_Result_max_match__1(lean_object*);
lean_object* l___private_Lean_Level_0__Lean_Level_isAlreadyNormalizedCheap___boxed(lean_object*);
lean_object* l_Lean_Name_toStringWithSep(lean_object*, lean_object*);
lean_object* l_Lean_Level_isParam_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_addOffsetAux_match__1(lean_object*);
lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux_match__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_mvarId_x21___closed__3;
extern uint64_t l_instInhabitedUInt64;
lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_Data_hash___boxed(lean_object*);
lean_object* l___private_Lean_Level_0__Lean_Level_mkIMaxAux_match__1(lean_object*);
lean_object* l_Lean_Level_isParam_match__1(lean_object*);
lean_object* l_Lean_Level_getLevelOffset___boxed(lean_object*);
lean_object* l_Lean_Level_Data_hasMVar___boxed(lean_object*);
lean_object* l_Lean_Level_updateIMax_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_level_has_mvar(lean_object*);
lean_object* l_Lean_Level_isNeverZero___boxed(lean_object*);
uint8_t l_Lean_Level_normLtAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_PP_Result_format___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isParam(lean_object*);
lean_object* l_Lean_Level_PP_Result_format___closed__2;
lean_object* l_Lean_Level_updateSucc_x21(lean_object*, lean_object*);
lean_object* l_Lean_Level_updateMax_x21___closed__1;
extern lean_object* l_Lean_numLitKind;
lean_object* l_ReaderT_bind___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_isParam___boxed(lean_object*);
lean_object* l_Lean_Level_PP_toResult___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint32_t lean_level_depth(lean_object*);
lean_object* l_Lean_Level_isIMax___boxed(lean_object*);
lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at_Lean_Level_normalize___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_instHashableLevel;
uint64_t l_Lean_levelZero___closed__1;
lean_object* l_Lean_Level_isExplicit_match__1(lean_object*);
uint64_t l_Lean_Level_data(lean_object*);
lean_object* l_Lean_Level_any___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Level_isNeverZero_match__1(lean_object*);
lean_object* l_Lean_Level_PP_Result_succ_match__1(lean_object*);
uint64_t l_Lean_Level_mkData(size_t, lean_object*, uint8_t, uint8_t);
lean_object* lean_level_update_max(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_any(lean_object*, lean_object*);
lean_object* lean_level_mk_max_simp(lean_object*, lean_object*);
lean_object* l_Lean_Level_normalize___closed__1;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint32_t l_UInt64_toUInt32(uint64_t);
lean_object* l_Lean_Unhygienic_run___rarg(lean_object*);
lean_object* l_Lean_Level_mkNaryMax_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMax(lean_object*, lean_object*);
lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse_match__1(lean_object*);
lean_object* l_Lean_Level_ofNat_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_occurs_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_PP_Result_quote___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_depth___boxed(lean_object*);
lean_object* lean_level_mk_imax_simp(lean_object*, lean_object*);
lean_object* l_Lean_Level_toNat(lean_object*);
lean_object* l_Lean_Level_normLtAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Level_updateSucc_x21___closed__3;
lean_object* l_Lean_Level_PP_Result_quote___lambda__4___closed__1;
lean_object* l_Lean_Level_PP_Result_quote___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_toNat___boxed(lean_object*);
lean_object* l_Lean_Level_addOffset(lean_object*, lean_object*);
size_t l_Lean_Level_Data_hash(uint64_t);
lean_object* l_Lean_Level_addOffsetAux(lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Level_updateMax___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_find_x3f_visit_match__1(lean_object*);
lean_object* l_Lean_Level_occurs___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Level_isMaxIMax_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_isZero___boxed(lean_object*);
lean_object* l_Lean_Level_ctorToNat(lean_object*);
lean_object* l_Lean_Level_updateMax_x21___closed__3;
lean_object* l_Lean_Level_isZero_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedLevel___closed__1;
lean_object* l_Lean_Level_isMax_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_PP_toResult_match__1(lean_object*);
lean_object* l_Lean_Level_PP_Result_format_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat___boxed(lean_object*);
lean_object* l_Lean_instBEqData___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Level_updateSucc___boxed(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Level_isNeverZero_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_PP_Result_quote___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Level_0__Lean_Level_accMax(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_PP_Result_succ(lean_object*);
lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_paren___closed__4;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_PP_toResult_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_Data_hasParam(uint64_t);
uint64_t l_UInt64_land(uint64_t, uint64_t);
lean_object* l_Lean_Level_addOffsetAux_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit___boxed(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
extern uint64_t l_instInhabitedUInt64___closed__1;
uint8_t l_Lean_Level_isIMax(lean_object*);
lean_object* l_Lean_Level_PP_Result_format_match__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_PP_Result_quote___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Level_PP_Result_quote___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(lean_object*, uint8_t);
lean_object* l_Lean_Level_data_match__1(lean_object*);
lean_object* l_Lean_Level_getOffset___boxed(lean_object*);
lean_object* l_Array_qpartition_loop___at_Lean_Level_normalize___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameGenerator_namePrefix___default___closed__2;
lean_object* l_Lean_mkLevelMVar(lean_object*);
lean_object* l_Lean_Level_PP_Result_quote___closed__1;
lean_object* l___private_Lean_Level_0__Lean_Level_isAlreadyNormalizedCheap_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_isIMax_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_PP_Result_max(lean_object*, lean_object*);
lean_object* l_Lean_Level_normalize___boxed(lean_object*);
lean_object* l_Nat_toLevel(lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
uint8_t l_Lean_Level_normLt(lean_object*, lean_object*);
lean_object* l_Lean_Level_PP_Result_format___closed__3;
lean_object* l_Lean_Level_PP_Result_imax_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_PP_Result_imax(lean_object*, lean_object*);
lean_object* l_Std_fmt___at_Lean_Level_PP_Result_format___spec__1(lean_object*);
lean_object* lean_level_mk_param(lean_object*);
lean_object* l_Lean_Level_normalize___closed__2;
lean_object* lean_level_update_imax(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_imax___boxed(lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
uint8_t l_Lean_instBEqData(uint64_t, uint64_t);
lean_object* l_Lean_Level_updateIMax_x21___closed__3;
lean_object* l_Lean_levelOne___closed__1;
lean_object* l_Lean_levelZero___closed__2;
lean_object* l_Lean_Level_isMaxIMax___boxed(lean_object*);
uint8_t l_Lean_Name_lt(lean_object*, lean_object*);
uint32_t l_Lean_Level_Data_depth(uint64_t);
lean_object* l_Lean_mkLevelSucc(lean_object*);
lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_PP_toResult___closed__3;
lean_object* l_Lean_Level_instQuoteLevel(lean_object*);
lean_object* l_Lean_Level_find_x3f(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Level_getOffsetAux_match__1(lean_object*);
lean_object* l_Lean_Level_PP_Result_quote___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_Data_hasMVar(uint64_t);
lean_object* l_Lean_Level_normLt___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Level_mkNaryMax(lean_object*);
lean_object* l_Lean_Level_Data_depth___boxed(lean_object*);
uint32_t l_USize_toUInt32(size_t);
lean_object* l_Lean_Level_PP_Result_quote___lambda__3___closed__1;
lean_object* l_Lean_Level_normalize(lean_object*);
uint64_t l_UInt64_shiftLeft(uint64_t, uint64_t);
lean_object* l_Array_appendCore___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Level_mkNaryMax_match__1(lean_object*);
lean_object* l_Lean_Level_PP_Result_quote___lambda__6___closed__1;
lean_object* l_Lean_Level_PP_Result_quote(lean_object*, lean_object*);
lean_object* l_Lean_Level_PP_Result_quote___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_mkData___boxed__const__1;
lean_object* l_Lean_Level_updateSucc_x21___closed__2;
lean_object* l_Lean_Level_normLtAux_match__1(lean_object*);
lean_object* l_Lean_Level_PP_Result_quote___lambda__3___closed__2;
uint8_t l_Lean_Level_isMVar(lean_object*);
lean_object* l_Lean_Level_isSucc_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint64_t l_UInt32_toUInt64(uint32_t);
lean_object* l_Std_fmt___at_Lean_Level_PP_Result_format___spec__2(lean_object*);
lean_object* l_Lean_Level_PP_Result_format(lean_object*, uint8_t);
lean_object* lean_level_mk_imax(lean_object*, lean_object*);
lean_object* l_Nat_imax(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedName;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Level_PP_Result_quote___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_depthEx___boxed(lean_object*);
lean_object* l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst_match__1(lean_object*);
extern lean_object* l_stx___x2b___closed__3;
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
lean_object* lean_level_update_succ(lean_object*, lean_object*);
lean_object* l_Lean_Level_getLevelOffset(lean_object*);
lean_object* l_Lean_Level_dec___boxed(lean_object*);
lean_object* l_Lean_Level_collectMVars_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_find_x3f_visit(lean_object*, lean_object*);
uint64_t l_Lean_instInhabitedData;
lean_object* l_Lean_Level_ofNat_match__1(lean_object*);
lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux_match__1(lean_object*);
lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit(lean_object*, lean_object*);
lean_object* l_Lean_Level_isEquiv___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at_Lean_Level_normalize___spec__1(lean_object*, uint8_t, lean_object*);
size_t lean_usize_mix_hash(size_t, size_t);
lean_object* lean_level_mk_zero(lean_object*);
uint8_t l_Lean_Level_isZero(lean_object*);
extern lean_object* l_prec_x28___x29___closed__7;
lean_object* l_Lean_Level_hasParam___boxed(lean_object*);
uint8_t l_Lean_Level_occurs(lean_object*, lean_object*);
lean_object* l___private_Lean_Level_0__Lean_Level_mkIMaxAux_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_hashEx___boxed(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13918____closed__7;
lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse_match__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Level_hasMVar___boxed(lean_object*);
extern lean_object* l_prec_x28___x29___closed__3;
lean_object* l_Lean_Level_PP_Result_quote___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_PP_Result_quote___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___boxed(lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Level_PP_Result_quote___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isMaxIMax(lean_object*);
lean_object* l_Lean_Level_hash___boxed(lean_object*);
lean_object* l_Lean_Level_instantiateParams(lean_object*, lean_object*);
uint8_t l_Lean_Level_isSucc(lean_object*);
lean_object* l_Lean_Level_PP_Result_quote___lambda__5___closed__1;
lean_object* l_Lean_Level_PP_Result_max_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_isZero_match__1(lean_object*);
uint8_t l_Lean_Level_isExplicit(lean_object*);
lean_object* l_Lean_Level_instantiateParams_match__2(lean_object*);
lean_object* l_Lean_Level_updateSucc_x21___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
uint64_t l_UInt64_shiftRight(uint64_t, uint64_t);
lean_object* l_Lean_Level_instBEqLevel___closed__1;
lean_object* l_Lean_Level_isMVar_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_Level_PP_Result_succ_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_levelOne;
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* l_Lean_Level_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Level_mkData___closed__5;
lean_object* l_Lean_Level_isMax_match__1(lean_object*);
lean_object* l_Lean_Level_PP_Result_quote___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Level_0__Lean_Level_isAlreadyNormalizedCheap_match__1(lean_object*);
lean_object* l_Lean_Level_addOffsetAux_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_instantiateParams_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_level_mk_mvar(lean_object*);
lean_object* l_Lean_Level_format(lean_object*);
lean_object* l_Lean_Level_quote(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsort_sort___at_Lean_Level_normalize___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_Data_hasParam___boxed(lean_object*);
lean_object* l_Lean_Level_PP_Result_quote___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_isMaxIMax_match__1(lean_object*);
lean_object* l_Lean_Level_updateIMax_x21___closed__2;
lean_object* l_Lean_Level_PP_toResult(lean_object*);
lean_object* l_Lean_Level_PP_Result_quote___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_getOffset(lean_object*);
lean_object* l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(lean_object*);
lean_object* l_Nat_toLevel___boxed(lean_object*);
extern lean_object* l_Std_Format_paren___closed__3;
lean_object* l_Lean_Level_isIMax_match__1(lean_object*);
uint8_t l_Lean_Level_isMax(lean_object*);
uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(lean_object*, lean_object*);
lean_object* l_Lean_Level_occurs_match__1(lean_object*);
lean_object* l_Lean_instInhabitedLevel;
lean_object* l_Lean_Syntax_mkLit(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_PP_Result_format_match__1(lean_object*);
lean_object* l_Nat_imax(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Nat_max(x_1, x_2);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(0u);
return x_6;
}
}
}
lean_object* l_Nat_imax___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_imax(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static uint64_t _init_l_Lean_instInhabitedData() {
_start:
{
uint64_t x_1; 
x_1 = l_instInhabitedUInt64;
return x_1;
}
}
size_t l_Lean_Level_Data_hash(uint64_t x_1) {
_start:
{
uint32_t x_2; size_t x_3; 
x_2 = ((uint32_t)x_1);
x_3 = x_2;
return x_3;
}
}
lean_object* l_Lean_Level_Data_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lean_Level_Data_hash(x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
uint8_t l_Lean_instBEqData(uint64_t x_1, uint64_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 == x_2;
return x_3;
}
}
lean_object* l_Lean_instBEqData___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Lean_instBEqData(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
uint32_t l_Lean_Level_Data_depth(uint64_t x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint32_t x_4; 
x_2 = 40;
x_3 = x_1 >> x_2 % 64;
x_4 = ((uint32_t)x_3);
return x_4;
}
}
lean_object* l_Lean_Level_Data_depth___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lean_Level_Data_depth(x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
uint8_t l_Lean_Level_Data_hasMVar(uint64_t x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; uint8_t x_6; 
x_2 = 32;
x_3 = x_1 >> x_2 % 64;
x_4 = 1;
x_5 = x_3 & x_4;
x_6 = x_5 == x_4;
return x_6;
}
}
lean_object* l_Lean_Level_Data_hasMVar___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lean_Level_Data_hasMVar(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_Level_Data_hasParam(uint64_t x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; uint8_t x_6; 
x_2 = 33;
x_3 = x_1 >> x_2 % 64;
x_4 = 1;
x_5 = x_3 & x_4;
x_6 = x_5 == x_4;
return x_6;
}
}
lean_object* l_Lean_Level_Data_hasParam___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lean_Level_Data_hasParam(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Level_mkData___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(16777216u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_sub(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Level_mkData___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Level");
return x_1;
}
}
static lean_object* _init_l_Lean_Level_mkData___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Level.mkData");
return x_1;
}
}
static lean_object* _init_l_Lean_Level_mkData___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("universe level depth is too big");
return x_1;
}
}
static lean_object* _init_l_Lean_Level_mkData___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Level_mkData___closed__2;
x_2 = l_Lean_Level_mkData___closed__3;
x_3 = lean_unsigned_to_nat(46u);
x_4 = lean_unsigned_to_nat(35u);
x_5 = l_Lean_Level_mkData___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Level_mkData___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_Lean_instInhabitedData;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
uint64_t l_Lean_Level_mkData(size_t x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Level_mkData___closed__1;
x_6 = lean_nat_dec_lt(x_5, x_2);
if (x_6 == 0)
{
uint32_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; 
x_7 = (uint32_t)x_1;
x_8 = ((uint64_t)x_7);
x_9 = (uint64_t)x_3;
x_10 = 32;
x_11 = x_9 << x_10 % 64;
x_12 = x_8 + x_11;
x_13 = (uint64_t)x_4;
x_14 = 33;
x_15 = x_13 << x_14 % 64;
x_16 = x_12 + x_15;
x_17 = lean_uint64_of_nat(x_2);
x_18 = 40;
x_19 = x_17 << x_18 % 64;
x_20 = x_16 + x_19;
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; 
x_21 = l_Lean_Level_mkData___closed__5;
x_22 = l_Lean_Level_mkData___boxed__const__1;
x_23 = lean_panic_fn(x_22, x_21);
x_24 = lean_unbox_uint64(x_23);
lean_dec(x_23);
return x_24;
}
}
}
lean_object* l_Lean_Level_mkData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; uint8_t x_7; uint64_t x_8; lean_object* x_9; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_Level_mkData(x_5, x_2, x_6, x_7);
lean_dec(x_2);
x_9 = lean_box_uint64(x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_instInhabitedLevel___closed__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_instInhabitedUInt64___closed__1;
x_2 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint64(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedLevel() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedLevel___closed__1;
return x_1;
}
}
lean_object* l_Lean_Level_data_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint64_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get_uint64(x_1, 0);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
x_10 = lean_apply_1(x_2, x_9);
return x_10;
}
case 1:
{
lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_13 = lean_box_uint64(x_12);
x_14 = lean_apply_2(x_5, x_11, x_13);
return x_14;
}
case 2:
{
lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_18 = lean_box_uint64(x_17);
x_19 = lean_apply_3(x_6, x_15, x_16, x_18);
return x_19;
}
case 3:
{
lean_object* x_20; lean_object* x_21; uint64_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_23 = lean_box_uint64(x_22);
x_24 = lean_apply_3(x_7, x_20, x_21, x_23);
return x_24;
}
case 4:
{
lean_object* x_25; uint64_t x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_27 = lean_box_uint64(x_26);
x_28 = lean_apply_2(x_4, x_25, x_27);
return x_28;
}
default: 
{
lean_object* x_29; uint64_t x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
x_30 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_31 = lean_box_uint64(x_30);
x_32 = lean_apply_2(x_3, x_29, x_31);
return x_32;
}
}
}
}
lean_object* l_Lean_Level_data_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Level_data_match__1___rarg), 7, 0);
return x_2;
}
}
uint64_t l_Lean_Level_data(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint64_t x_2; 
x_2 = lean_ctor_get_uint64(x_1, 0);
return x_2;
}
case 2:
{
uint64_t x_3; 
x_3 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
return x_3;
}
case 3:
{
uint64_t x_4; 
x_4 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
return x_4;
}
default: 
{
uint64_t x_5; 
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
return x_5;
}
}
}
}
lean_object* l_Lean_Level_data___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Level_data(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
size_t l_Lean_Level_hash(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint64_t x_2; size_t x_3; 
x_2 = lean_ctor_get_uint64(x_1, 0);
x_3 = l_Lean_Level_Data_hash(x_2);
return x_3;
}
case 2:
{
uint64_t x_4; size_t x_5; 
x_4 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_5 = l_Lean_Level_Data_hash(x_4);
return x_5;
}
case 3:
{
uint64_t x_6; size_t x_7; 
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_7 = l_Lean_Level_Data_hash(x_6);
return x_7;
}
default: 
{
uint64_t x_8; size_t x_9; 
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_9 = l_Lean_Level_Data_hash(x_8);
return x_9;
}
}
}
}
lean_object* l_Lean_Level_hash___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_Lean_Level_hash(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Level_instHashableLevel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Level_hash___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_instHashableLevel() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Level_instHashableLevel___closed__1;
return x_1;
}
}
lean_object* l_Lean_Level_depth(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint64_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_ctor_get_uint64(x_1, 0);
x_3 = l_Lean_Level_Data_depth(x_2);
x_4 = lean_uint32_to_nat(x_3);
return x_4;
}
case 2:
{
uint64_t x_5; uint32_t x_6; lean_object* x_7; 
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_6 = l_Lean_Level_Data_depth(x_5);
x_7 = lean_uint32_to_nat(x_6);
return x_7;
}
case 3:
{
uint64_t x_8; uint32_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_9 = l_Lean_Level_Data_depth(x_8);
x_10 = lean_uint32_to_nat(x_9);
return x_10;
}
default: 
{
uint64_t x_11; uint32_t x_12; lean_object* x_13; 
x_11 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_12 = l_Lean_Level_Data_depth(x_11);
x_13 = lean_uint32_to_nat(x_12);
return x_13;
}
}
}
}
lean_object* l_Lean_Level_depth___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_depth(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_Lean_Level_hasMVar(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint64_t x_2; uint8_t x_3; 
x_2 = lean_ctor_get_uint64(x_1, 0);
x_3 = l_Lean_Level_Data_hasMVar(x_2);
return x_3;
}
case 2:
{
uint64_t x_4; uint8_t x_5; 
x_4 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_5 = l_Lean_Level_Data_hasMVar(x_4);
return x_5;
}
case 3:
{
uint64_t x_6; uint8_t x_7; 
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_7 = l_Lean_Level_Data_hasMVar(x_6);
return x_7;
}
default: 
{
uint64_t x_8; uint8_t x_9; 
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_9 = l_Lean_Level_Data_hasMVar(x_8);
return x_9;
}
}
}
}
lean_object* l_Lean_Level_hasMVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Level_hasMVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_Level_hasParam(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint64_t x_2; uint8_t x_3; 
x_2 = lean_ctor_get_uint64(x_1, 0);
x_3 = l_Lean_Level_Data_hasParam(x_2);
return x_3;
}
case 2:
{
uint64_t x_4; uint8_t x_5; 
x_4 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_5 = l_Lean_Level_Data_hasParam(x_4);
return x_5;
}
case 3:
{
uint64_t x_6; uint8_t x_7; 
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_7 = l_Lean_Level_Data_hasParam(x_6);
return x_7;
}
default: 
{
uint64_t x_8; uint8_t x_9; 
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_9 = l_Lean_Level_Data_hasParam(x_8);
return x_9;
}
}
}
}
lean_object* l_Lean_Level_hasParam___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Level_hasParam(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
size_t lean_level_hash(lean_object* x_1) {
_start:
{
size_t x_2; 
x_2 = l_Lean_Level_hash(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Level_hashEx___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = lean_level_hash(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
uint8_t lean_level_has_mvar(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Level_hasMVar(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Level_hasMVarEx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_level_has_mvar(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t lean_level_has_param(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Level_hasParam(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Level_hasParamEx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_level_has_param(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint32_t lean_level_depth(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint64_t x_2; uint32_t x_3; 
x_2 = lean_ctor_get_uint64(x_1, 0);
lean_dec(x_1);
x_3 = l_Lean_Level_Data_depth(x_2);
return x_3;
}
case 2:
{
uint64_t x_4; uint32_t x_5; 
x_4 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_5 = l_Lean_Level_Data_depth(x_4);
return x_5;
}
case 3:
{
uint64_t x_6; uint32_t x_7; 
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_7 = l_Lean_Level_Data_depth(x_6);
return x_7;
}
default: 
{
uint64_t x_8; uint32_t x_9; 
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_9 = l_Lean_Level_Data_depth(x_8);
return x_9;
}
}
}
}
lean_object* l_Lean_Level_depthEx___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_level_depth(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
static uint64_t _init_l_Lean_levelZero___closed__1() {
_start:
{
size_t x_1; lean_object* x_2; uint8_t x_3; uint64_t x_4; 
x_1 = 2221;
x_2 = lean_unsigned_to_nat(0u);
x_3 = 0;
x_4 = l_Lean_Level_mkData(x_1, x_2, x_3, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_levelZero___closed__2() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero___closed__1;
x_2 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint64(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_levelZero() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_levelZero___closed__2;
return x_1;
}
}
lean_object* l_Lean_mkLevelMVar(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; size_t x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint64_t x_8; lean_object* x_9; 
x_2 = 2237;
x_3 = l_Lean_Name_hash(x_1);
x_4 = lean_usize_mix_hash(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = 1;
x_7 = 0;
x_8 = l_Lean_Level_mkData(x_4, x_5, x_6, x_7);
x_9 = lean_alloc_ctor(5, 1, 8);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set_uint64(x_9, sizeof(void*)*1, x_8);
return x_9;
}
}
lean_object* l_Lean_mkLevelParam(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; size_t x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint64_t x_8; lean_object* x_9; 
x_2 = 2239;
x_3 = l_Lean_Name_hash(x_1);
x_4 = lean_usize_mix_hash(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = 0;
x_7 = 1;
x_8 = l_Lean_Level_mkData(x_4, x_5, x_6, x_7);
x_9 = lean_alloc_ctor(4, 1, 8);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set_uint64(x_9, sizeof(void*)*1, x_8);
return x_9;
}
}
lean_object* l_Lean_mkLevelSucc(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; size_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint64_t x_10; lean_object* x_11; 
x_2 = 2243;
x_3 = l_Lean_Level_hash(x_1);
x_4 = lean_usize_mix_hash(x_2, x_3);
x_5 = l_Lean_Level_depth(x_1);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_5, x_6);
lean_dec(x_5);
x_8 = l_Lean_Level_hasMVar(x_1);
x_9 = l_Lean_Level_hasParam(x_1);
x_10 = l_Lean_Level_mkData(x_4, x_7, x_8, x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set_uint64(x_11, sizeof(void*)*1, x_10);
return x_11;
}
}
lean_object* l_Lean_mkLevelMax(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_3 = 2251;
x_4 = l_Lean_Level_hash(x_1);
x_5 = l_Lean_Level_hash(x_2);
x_6 = lean_usize_mix_hash(x_4, x_5);
x_7 = lean_usize_mix_hash(x_3, x_6);
x_8 = l_Lean_Level_depth(x_1);
x_9 = l_Lean_Level_depth(x_2);
x_10 = l_Nat_max(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_10, x_11);
lean_dec(x_10);
x_13 = l_Lean_Level_hasMVar(x_1);
x_14 = l_Lean_Level_hasParam(x_1);
if (x_13 == 0)
{
uint8_t x_15; 
x_15 = l_Lean_Level_hasMVar(x_2);
if (x_14 == 0)
{
uint8_t x_16; uint64_t x_17; lean_object* x_18; 
x_16 = l_Lean_Level_hasParam(x_2);
x_17 = l_Lean_Level_mkData(x_7, x_12, x_15, x_16);
lean_dec(x_12);
x_18 = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_2);
lean_ctor_set_uint64(x_18, sizeof(void*)*2, x_17);
return x_18;
}
else
{
uint8_t x_19; uint64_t x_20; lean_object* x_21; 
x_19 = 1;
x_20 = l_Lean_Level_mkData(x_7, x_12, x_15, x_19);
lean_dec(x_12);
x_21 = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_2);
lean_ctor_set_uint64(x_21, sizeof(void*)*2, x_20);
return x_21;
}
}
else
{
if (x_14 == 0)
{
uint8_t x_22; uint8_t x_23; uint64_t x_24; lean_object* x_25; 
x_22 = l_Lean_Level_hasParam(x_2);
x_23 = 1;
x_24 = l_Lean_Level_mkData(x_7, x_12, x_23, x_22);
lean_dec(x_12);
x_25 = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_2);
lean_ctor_set_uint64(x_25, sizeof(void*)*2, x_24);
return x_25;
}
else
{
uint8_t x_26; uint64_t x_27; lean_object* x_28; 
x_26 = 1;
x_27 = l_Lean_Level_mkData(x_7, x_12, x_26, x_26);
lean_dec(x_12);
x_28 = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set_uint64(x_28, sizeof(void*)*2, x_27);
return x_28;
}
}
}
}
lean_object* l_Lean_mkLevelIMax(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_3 = 2267;
x_4 = l_Lean_Level_hash(x_1);
x_5 = l_Lean_Level_hash(x_2);
x_6 = lean_usize_mix_hash(x_4, x_5);
x_7 = lean_usize_mix_hash(x_3, x_6);
x_8 = l_Lean_Level_depth(x_1);
x_9 = l_Lean_Level_depth(x_2);
x_10 = l_Nat_max(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_10, x_11);
lean_dec(x_10);
x_13 = l_Lean_Level_hasMVar(x_1);
x_14 = l_Lean_Level_hasParam(x_1);
if (x_13 == 0)
{
uint8_t x_15; 
x_15 = l_Lean_Level_hasMVar(x_2);
if (x_14 == 0)
{
uint8_t x_16; uint64_t x_17; lean_object* x_18; 
x_16 = l_Lean_Level_hasParam(x_2);
x_17 = l_Lean_Level_mkData(x_7, x_12, x_15, x_16);
lean_dec(x_12);
x_18 = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_2);
lean_ctor_set_uint64(x_18, sizeof(void*)*2, x_17);
return x_18;
}
else
{
uint8_t x_19; uint64_t x_20; lean_object* x_21; 
x_19 = 1;
x_20 = l_Lean_Level_mkData(x_7, x_12, x_15, x_19);
lean_dec(x_12);
x_21 = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_2);
lean_ctor_set_uint64(x_21, sizeof(void*)*2, x_20);
return x_21;
}
}
else
{
if (x_14 == 0)
{
uint8_t x_22; uint8_t x_23; uint64_t x_24; lean_object* x_25; 
x_22 = l_Lean_Level_hasParam(x_2);
x_23 = 1;
x_24 = l_Lean_Level_mkData(x_7, x_12, x_23, x_22);
lean_dec(x_12);
x_25 = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_2);
lean_ctor_set_uint64(x_25, sizeof(void*)*2, x_24);
return x_25;
}
else
{
uint8_t x_26; uint64_t x_27; lean_object* x_28; 
x_26 = 1;
x_27 = l_Lean_Level_mkData(x_7, x_12, x_26, x_26);
lean_dec(x_12);
x_28 = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set_uint64(x_28, sizeof(void*)*2, x_27);
return x_28;
}
}
}
}
static lean_object* _init_l_Lean_levelOne___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_mkLevelSucc(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_levelOne() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_levelOne___closed__1;
return x_1;
}
}
lean_object* lean_level_mk_zero(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_dec(x_1);
x_2 = l_Lean_levelZero;
return x_2;
}
}
lean_object* lean_level_mk_succ(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkLevelSucc(x_1);
return x_2;
}
}
lean_object* lean_level_mk_mvar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkLevelMVar(x_1);
return x_2;
}
}
lean_object* lean_level_mk_param(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkLevelParam(x_1);
return x_2;
}
}
lean_object* lean_level_mk_max(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkLevelMax(x_1, x_2);
return x_3;
}
}
lean_object* lean_level_mk_imax(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkLevelIMax(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Level_isZero_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint64_t x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get_uint64(x_1, 0);
lean_dec(x_1);
x_5 = lean_box_uint64(x_4);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Level_isZero_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Level_isZero_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Level_isZero(lean_object* x_1) {
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
lean_object* l_Lean_Level_isZero___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Level_isZero(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Level_isSucc_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l_Lean_Level_isSucc_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Level_isSucc_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Level_isSucc(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
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
lean_object* l_Lean_Level_isSucc___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Level_isSucc(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Level_isMax_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_7 = lean_box_uint64(x_6);
x_8 = lean_apply_3(x_2, x_4, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l_Lean_Level_isMax_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Level_isMax_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Level_isMax(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 2)
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
lean_object* l_Lean_Level_isMax___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Level_isMax(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Level_isIMax_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_7 = lean_box_uint64(x_6);
x_8 = lean_apply_3(x_2, x_4, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l_Lean_Level_isIMax_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Level_isIMax_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Level_isIMax(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 3)
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
lean_object* l_Lean_Level_isIMax___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Level_isIMax(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Level_isMaxIMax_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_3(x_2, x_5, x_6, x_8);
return x_9;
}
case 3:
{
lean_object* x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_13 = lean_box_uint64(x_12);
x_14 = lean_apply_3(x_3, x_10, x_11, x_13);
return x_14;
}
default: 
{
lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_apply_1(x_4, x_1);
return x_15;
}
}
}
}
lean_object* l_Lean_Level_isMaxIMax_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Level_isMaxIMax_match__1___rarg), 4, 0);
return x_2;
}
}
uint8_t l_Lean_Level_isMaxIMax(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
case 3:
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
default: 
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
}
}
lean_object* l_Lean_Level_isMaxIMax___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Level_isMaxIMax(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Level_isParam_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l_Lean_Level_isParam_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Level_isParam_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Level_isParam(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
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
lean_object* l_Lean_Level_isParam___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Level_isParam(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Level_isMVar_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l_Lean_Level_isMVar_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Level_isMVar_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Level_isMVar(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
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
lean_object* l_Lean_Level_isMVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Level_isMVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Level_mvarId_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Level.mvarId!");
return x_1;
}
}
static lean_object* _init_l_Lean_Level_mvarId_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("metavariable expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Level_mvarId_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Level_mkData___closed__2;
x_2 = l_Lean_Level_mvarId_x21___closed__1;
x_3 = lean_unsigned_to_nat(157u);
x_4 = lean_unsigned_to_nat(21u);
x_5 = l_Lean_Level_mvarId_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Level_mvarId_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_instInhabitedName;
x_4 = l_Lean_Level_mvarId_x21___closed__3;
x_5 = lean_panic_fn(x_3, x_4);
return x_5;
}
}
}
lean_object* l_Lean_Level_mvarId_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_mvarId_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Level_isNeverZero_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint64_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get_uint64(x_1, 0);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
x_10 = lean_apply_1(x_2, x_9);
return x_10;
}
case 1:
{
lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_13 = lean_box_uint64(x_12);
x_14 = lean_apply_2(x_5, x_11, x_13);
return x_14;
}
case 2:
{
lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_18 = lean_box_uint64(x_17);
x_19 = lean_apply_3(x_6, x_15, x_16, x_18);
return x_19;
}
case 3:
{
lean_object* x_20; lean_object* x_21; uint64_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_23 = lean_box_uint64(x_22);
x_24 = lean_apply_3(x_7, x_20, x_21, x_23);
return x_24;
}
case 4:
{
lean_object* x_25; uint64_t x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_27 = lean_box_uint64(x_26);
x_28 = lean_apply_2(x_3, x_25, x_27);
return x_28;
}
default: 
{
lean_object* x_29; uint64_t x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
x_30 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_31 = lean_box_uint64(x_30);
x_32 = lean_apply_2(x_4, x_29, x_31);
return x_32;
}
}
}
}
lean_object* l_Lean_Level_isNeverZero_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Level_isNeverZero_match__1___rarg), 7, 0);
return x_2;
}
}
uint8_t l_Lean_Level_isNeverZero(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
case 2:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_Level_isNeverZero(x_3);
if (x_5 == 0)
{
x_1 = x_4;
goto _start;
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
case 3:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 1);
x_1 = x_8;
goto _start;
}
default: 
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
}
lean_object* l_Lean_Level_isNeverZero___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Level_isNeverZero(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Level_ofNat_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_2, x_9);
return x_10;
}
}
}
lean_object* l_Lean_Level_ofNat_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Level_ofNat_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Level_ofNat_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Level_ofNat_match__1___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Level_ofNat(lean_object* x_1) {
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
x_6 = l_Lean_Level_ofNat(x_5);
lean_dec(x_5);
x_7 = l_Lean_mkLevelSucc(x_6);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = l_Lean_levelZero;
return x_8;
}
}
}
lean_object* l_Lean_Level_ofNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_ofNat(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Level_addOffsetAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Lean_Level_addOffsetAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Level_addOffsetAux_match__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Level_addOffsetAux_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Level_addOffsetAux_match__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Level_addOffsetAux(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_mkLevelSucc(x_2);
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
lean_object* l_Lean_Level_addOffset(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Level_addOffsetAux(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Level_isExplicit_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get_uint64(x_1, 0);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; uint64_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_10 = lean_box_uint64(x_9);
x_11 = lean_apply_2(x_3, x_8, x_10);
return x_11;
}
default: 
{
lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_apply_1(x_4, x_1);
return x_12;
}
}
}
}
lean_object* l_Lean_Level_isExplicit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Level_isExplicit_match__1___rarg), 4, 0);
return x_2;
}
}
uint8_t l_Lean_Level_isExplicit(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
case 1:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_Level_hasMVar(x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Lean_Level_hasParam(x_3);
if (x_5 == 0)
{
x_1 = x_3;
goto _start;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
default: 
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
}
}
lean_object* l_Lean_Level_isExplicit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Level_isExplicit(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Level_getOffsetAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_7 = lean_box_uint64(x_6);
x_8 = lean_apply_3(x_3, x_5, x_7, x_2);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_apply_2(x_4, x_1, x_2);
return x_9;
}
}
}
lean_object* l_Lean_Level_getOffsetAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Level_getOffsetAux_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Level_getOffsetAux(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_3;
x_2 = x_5;
goto _start;
}
else
{
return x_2;
}
}
}
lean_object* l_Lean_Level_getOffsetAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Level_getOffsetAux(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Level_getOffset(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Level_getOffsetAux(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Level_getOffset___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_getOffset(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Level_getLevelOffset(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
x_1 = x_2;
goto _start;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
lean_object* l_Lean_Level_getLevelOffset___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_getLevelOffset(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Level_toNat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_getLevelOffset(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Level_getOffsetAux(x_1, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_box(0);
return x_6;
}
}
}
lean_object* l_Lean_Level_toNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_toNat(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Level_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_level_eq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Level_instBEqLevel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Level_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_instBEqLevel() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Level_instBEqLevel___closed__1;
return x_1;
}
}
lean_object* l_Lean_Level_occurs_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get_uint64(x_2, sizeof(void*)*1);
x_9 = lean_box_uint64(x_8);
x_10 = lean_apply_4(x_3, x_1, x_2, x_7, x_9);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; uint64_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_14 = lean_box_uint64(x_13);
x_15 = lean_apply_5(x_4, x_1, x_2, x_11, x_12, x_14);
return x_15;
}
case 3:
{
lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
x_18 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_19 = lean_box_uint64(x_18);
x_20 = lean_apply_5(x_5, x_1, x_2, x_16, x_17, x_19);
return x_20;
}
default: 
{
lean_object* x_21; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = lean_apply_2(x_6, x_1, x_2);
return x_21;
}
}
}
}
lean_object* l_Lean_Level_occurs_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Level_occurs_match__1___rarg), 6, 0);
return x_2;
}
}
uint8_t l_Lean_Level_occurs(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_level_eq(x_1, x_2);
if (x_4 == 0)
{
x_2 = x_3;
goto _start;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
case 2:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_level_eq(x_1, x_2);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_Level_occurs(x_1, x_7);
if (x_10 == 0)
{
x_2 = x_8;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
}
case 3:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_level_eq(x_1, x_2);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = l_Lean_Level_occurs(x_1, x_14);
if (x_17 == 0)
{
x_2 = x_15;
goto _start;
}
else
{
uint8_t x_19; 
x_19 = 1;
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = 1;
return x_20;
}
}
default: 
{
uint8_t x_21; 
x_21 = lean_level_eq(x_1, x_2);
return x_21;
}
}
}
}
lean_object* l_Lean_Level_occurs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Level_occurs(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Level_ctorToNat(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(3u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(4u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(5u);
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(1u);
return x_6;
}
default: 
{
lean_object* x_7; 
x_7 = lean_unsigned_to_nat(2u);
return x_7;
}
}
}
}
lean_object* l_Lean_Level_ctorToNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_ctorToNat(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Level_normLtAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_12; uint64_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get_uint64(x_3, sizeof(void*)*1);
lean_dec(x_3);
x_14 = lean_box_uint64(x_13);
x_15 = lean_apply_5(x_6, x_1, x_2, x_12, x_14, x_4);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_6);
x_16 = lean_apply_4(x_11, x_1, x_2, x_3, x_4);
return x_16;
}
}
case 1:
{
lean_object* x_17; uint64_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_19 = lean_box_uint64(x_18);
x_20 = lean_apply_5(x_5, x_17, x_19, x_2, x_3, x_4);
return x_20;
}
case 2:
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_21; uint64_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_11);
lean_dec(x_7);
x_21 = lean_ctor_get(x_3, 0);
lean_inc(x_21);
x_22 = lean_ctor_get_uint64(x_3, sizeof(void*)*1);
lean_dec(x_3);
x_23 = lean_box_uint64(x_22);
x_24 = lean_apply_5(x_6, x_1, x_2, x_21, x_23, x_4);
return x_24;
}
case 2:
{
lean_object* x_25; lean_object* x_26; uint64_t x_27; lean_object* x_28; lean_object* x_29; uint64_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_11);
lean_dec(x_6);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
x_27 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
x_30 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
x_31 = lean_box_uint64(x_27);
x_32 = lean_box_uint64(x_30);
x_33 = lean_apply_10(x_7, x_1, x_25, x_26, x_31, x_2, x_3, x_28, x_29, x_32, x_4);
return x_33;
}
default: 
{
lean_object* x_34; 
lean_dec(x_7);
lean_dec(x_6);
x_34 = lean_apply_4(x_11, x_1, x_2, x_3, x_4);
return x_34;
}
}
}
case 3:
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_35; uint64_t x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_11);
lean_dec(x_8);
x_35 = lean_ctor_get(x_3, 0);
lean_inc(x_35);
x_36 = lean_ctor_get_uint64(x_3, sizeof(void*)*1);
lean_dec(x_3);
x_37 = lean_box_uint64(x_36);
x_38 = lean_apply_5(x_6, x_1, x_2, x_35, x_37, x_4);
return x_38;
}
case 3:
{
lean_object* x_39; lean_object* x_40; uint64_t x_41; lean_object* x_42; lean_object* x_43; uint64_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_11);
lean_dec(x_6);
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
x_41 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_42 = lean_ctor_get(x_3, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_3, 1);
lean_inc(x_43);
x_44 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
x_45 = lean_box_uint64(x_41);
x_46 = lean_box_uint64(x_44);
x_47 = lean_apply_10(x_8, x_1, x_39, x_40, x_45, x_2, x_3, x_42, x_43, x_46, x_4);
return x_47;
}
default: 
{
lean_object* x_48; 
lean_dec(x_8);
lean_dec(x_6);
x_48 = lean_apply_4(x_11, x_1, x_2, x_3, x_4);
return x_48;
}
}
}
case 4:
{
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_49; uint64_t x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_11);
lean_dec(x_9);
x_49 = lean_ctor_get(x_3, 0);
lean_inc(x_49);
x_50 = lean_ctor_get_uint64(x_3, sizeof(void*)*1);
lean_dec(x_3);
x_51 = lean_box_uint64(x_50);
x_52 = lean_apply_5(x_6, x_1, x_2, x_49, x_51, x_4);
return x_52;
}
case 4:
{
lean_object* x_53; uint64_t x_54; lean_object* x_55; uint64_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_11);
lean_dec(x_6);
x_53 = lean_ctor_get(x_1, 0);
lean_inc(x_53);
x_54 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_55 = lean_ctor_get(x_3, 0);
lean_inc(x_55);
x_56 = lean_ctor_get_uint64(x_3, sizeof(void*)*1);
lean_dec(x_3);
x_57 = lean_box_uint64(x_54);
x_58 = lean_box_uint64(x_56);
x_59 = lean_apply_6(x_9, x_53, x_57, x_2, x_55, x_58, x_4);
return x_59;
}
default: 
{
lean_object* x_60; 
lean_dec(x_9);
lean_dec(x_6);
x_60 = lean_apply_4(x_11, x_1, x_2, x_3, x_4);
return x_60;
}
}
}
default: 
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_61; uint64_t x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_11);
lean_dec(x_10);
x_61 = lean_ctor_get(x_3, 0);
lean_inc(x_61);
x_62 = lean_ctor_get_uint64(x_3, sizeof(void*)*1);
lean_dec(x_3);
x_63 = lean_box_uint64(x_62);
x_64 = lean_apply_5(x_6, x_1, x_2, x_61, x_63, x_4);
return x_64;
}
case 5:
{
lean_object* x_65; uint64_t x_66; lean_object* x_67; uint64_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_11);
lean_dec(x_6);
x_65 = lean_ctor_get(x_1, 0);
lean_inc(x_65);
x_66 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_67 = lean_ctor_get(x_3, 0);
lean_inc(x_67);
x_68 = lean_ctor_get_uint64(x_3, sizeof(void*)*1);
lean_dec(x_3);
x_69 = lean_box_uint64(x_66);
x_70 = lean_box_uint64(x_68);
x_71 = lean_apply_6(x_10, x_65, x_69, x_2, x_67, x_70, x_4);
return x_71;
}
default: 
{
lean_object* x_72; 
lean_dec(x_10);
lean_dec(x_6);
x_72 = lean_apply_4(x_11, x_1, x_2, x_3, x_4);
return x_72;
}
}
}
}
}
}
lean_object* l_Lean_Level_normLtAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Level_normLtAux_match__1___rarg), 11, 0);
return x_2;
}
}
uint8_t l_Lean_Level_normLtAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_5;
x_4 = x_7;
goto _start;
}
else
{
uint8_t x_9; 
x_9 = lean_level_eq(x_1, x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_4);
lean_dec(x_2);
x_10 = l_Lean_Level_ctorToNat(x_1);
x_11 = l_Lean_Level_ctorToNat(x_3);
x_12 = lean_nat_dec_lt(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
}
case 1:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_2, x_15);
lean_dec(x_2);
x_1 = x_14;
x_2 = x_16;
goto _start;
}
case 2:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_4, x_19);
lean_dec(x_4);
x_3 = x_18;
x_4 = x_20;
goto _start;
}
case 2:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
x_26 = lean_level_eq(x_1, x_3);
if (x_26 == 0)
{
uint8_t x_27; 
lean_dec(x_4);
lean_dec(x_2);
x_27 = lean_level_eq(x_22, x_24);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_unsigned_to_nat(0u);
x_1 = x_22;
x_2 = x_28;
x_3 = x_24;
x_4 = x_28;
goto _start;
}
else
{
lean_object* x_30; 
x_30 = lean_unsigned_to_nat(0u);
x_1 = x_23;
x_2 = x_30;
x_3 = x_25;
x_4 = x_30;
goto _start;
}
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_32;
}
}
default: 
{
uint8_t x_33; 
x_33 = lean_level_eq(x_1, x_3);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_4);
lean_dec(x_2);
x_34 = l_Lean_Level_ctorToNat(x_1);
x_35 = l_Lean_Level_ctorToNat(x_3);
x_36 = lean_nat_dec_lt(x_34, x_35);
lean_dec(x_35);
lean_dec(x_34);
return x_36;
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_37;
}
}
}
}
case 3:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_3, 0);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_4, x_39);
lean_dec(x_4);
x_3 = x_38;
x_4 = x_40;
goto _start;
}
case 3:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_1, 0);
x_43 = lean_ctor_get(x_1, 1);
x_44 = lean_ctor_get(x_3, 0);
x_45 = lean_ctor_get(x_3, 1);
x_46 = lean_level_eq(x_1, x_3);
if (x_46 == 0)
{
uint8_t x_47; 
lean_dec(x_4);
lean_dec(x_2);
x_47 = lean_level_eq(x_42, x_44);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_unsigned_to_nat(0u);
x_1 = x_42;
x_2 = x_48;
x_3 = x_44;
x_4 = x_48;
goto _start;
}
else
{
lean_object* x_50; 
x_50 = lean_unsigned_to_nat(0u);
x_1 = x_43;
x_2 = x_50;
x_3 = x_45;
x_4 = x_50;
goto _start;
}
}
else
{
uint8_t x_52; 
x_52 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_52;
}
}
default: 
{
uint8_t x_53; 
x_53 = lean_level_eq(x_1, x_3);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_dec(x_4);
lean_dec(x_2);
x_54 = l_Lean_Level_ctorToNat(x_1);
x_55 = l_Lean_Level_ctorToNat(x_3);
x_56 = lean_nat_dec_lt(x_54, x_55);
lean_dec(x_55);
lean_dec(x_54);
return x_56;
}
else
{
uint8_t x_57; 
x_57 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_57;
}
}
}
}
case 4:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_3, 0);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_add(x_4, x_59);
lean_dec(x_4);
x_3 = x_58;
x_4 = x_60;
goto _start;
}
case 4:
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_1, 0);
x_63 = lean_ctor_get(x_3, 0);
x_64 = lean_name_eq(x_62, x_63);
if (x_64 == 0)
{
uint8_t x_65; 
lean_dec(x_4);
lean_dec(x_2);
x_65 = l_Lean_Name_lt(x_62, x_63);
return x_65;
}
else
{
uint8_t x_66; 
x_66 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_66;
}
}
default: 
{
uint8_t x_67; 
x_67 = lean_level_eq(x_1, x_3);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_dec(x_4);
lean_dec(x_2);
x_68 = l_Lean_Level_ctorToNat(x_1);
x_69 = l_Lean_Level_ctorToNat(x_3);
x_70 = lean_nat_dec_lt(x_68, x_69);
lean_dec(x_69);
lean_dec(x_68);
return x_70;
}
else
{
uint8_t x_71; 
x_71 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_71;
}
}
}
}
default: 
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_3, 0);
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_nat_add(x_4, x_73);
lean_dec(x_4);
x_3 = x_72;
x_4 = x_74;
goto _start;
}
case 5:
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_ctor_get(x_1, 0);
x_77 = lean_ctor_get(x_3, 0);
x_78 = lean_name_eq(x_76, x_77);
if (x_78 == 0)
{
uint8_t x_79; 
lean_dec(x_4);
lean_dec(x_2);
x_79 = l_Lean_Name_quickLt(x_76, x_77);
return x_79;
}
else
{
uint8_t x_80; 
x_80 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_80;
}
}
default: 
{
uint8_t x_81; 
x_81 = lean_level_eq(x_1, x_3);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
lean_dec(x_4);
lean_dec(x_2);
x_82 = l_Lean_Level_ctorToNat(x_1);
x_83 = l_Lean_Level_ctorToNat(x_3);
x_84 = lean_nat_dec_lt(x_82, x_83);
lean_dec(x_83);
lean_dec(x_82);
return x_84;
}
else
{
uint8_t x_85; 
x_85 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_85;
}
}
}
}
}
}
}
lean_object* l_Lean_Level_normLtAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_Level_normLtAux(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
uint8_t l_Lean_Level_normLt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Level_normLtAux(x_1, x_3, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Level_normLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Level_normLt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Level_0__Lean_Level_isAlreadyNormalizedCheap_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get_uint64(x_1, 0);
lean_dec(x_1);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_1(x_2, x_8);
return x_9;
}
case 1:
{
lean_object* x_10; uint64_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_12 = lean_box_uint64(x_11);
x_13 = lean_apply_2(x_5, x_10, x_12);
return x_13;
}
case 4:
{
lean_object* x_14; uint64_t x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_16 = lean_box_uint64(x_15);
x_17 = lean_apply_2(x_3, x_14, x_16);
return x_17;
}
case 5:
{
lean_object* x_18; uint64_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_20 = lean_box_uint64(x_19);
x_21 = lean_apply_2(x_4, x_18, x_20);
return x_21;
}
default: 
{
lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_apply_1(x_6, x_1);
return x_22;
}
}
}
}
lean_object* l___private_Lean_Level_0__Lean_Level_isAlreadyNormalizedCheap_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Level_0__Lean_Level_isAlreadyNormalizedCheap_match__1___rarg), 6, 0);
return x_2;
}
}
uint8_t l___private_Lean_Level_0__Lean_Level_isAlreadyNormalizedCheap(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
x_1 = x_2;
goto _start;
}
case 2:
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
case 3:
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
default: 
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
}
}
lean_object* l___private_Lean_Level_0__Lean_Level_isAlreadyNormalizedCheap___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Level_0__Lean_Level_isAlreadyNormalizedCheap(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Level_0__Lean_Level_mkIMaxAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_5);
if (lean_obj_tag(x_2) == 0)
{
uint64_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_6 = lean_ctor_get_uint64(x_2, 0);
x_7 = lean_box_uint64(x_6);
x_8 = lean_apply_3(x_3, x_1, x_2, x_7);
return x_8;
}
else
{
uint64_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_9 = lean_ctor_get_uint64(x_1, 0);
lean_dec(x_1);
x_10 = lean_box_uint64(x_9);
x_11 = lean_apply_2(x_4, x_10, x_2);
return x_11;
}
}
else
{
lean_dec(x_4);
if (lean_obj_tag(x_2) == 0)
{
uint64_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_12 = lean_ctor_get_uint64(x_2, 0);
x_13 = lean_box_uint64(x_12);
x_14 = lean_apply_3(x_3, x_1, x_2, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_3);
x_15 = lean_apply_2(x_5, x_1, x_2);
return x_15;
}
}
}
}
lean_object* l___private_Lean_Level_0__Lean_Level_mkIMaxAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Level_0__Lean_Level_mkIMaxAux_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Level_0__Lean_Level_mkIMaxAux(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = lean_level_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = l_Lean_mkLevelIMax(x_1, x_2);
return x_4;
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
}
}
lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux_match__1___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_10 = lean_box_uint64(x_9);
x_11 = lean_box(x_2);
x_12 = lean_apply_5(x_4, x_7, x_8, x_10, x_11, x_3);
return x_12;
}
else
{
lean_dec(x_4);
if (x_2 == 0)
{
lean_object* x_13; 
lean_dec(x_6);
x_13 = lean_apply_2(x_5, x_1, x_3);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_5);
x_14 = lean_apply_2(x_6, x_1, x_3);
return x_14;
}
}
}
}
lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Level_0__Lean_Level_getMaxArgsAux_match__1___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux_match__1___rarg(x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
lean_inc(x_1);
x_7 = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(x_1, x_5, x_3, x_4);
x_2 = x_6;
x_4 = x_7;
goto _start;
}
else
{
if (x_3 == 0)
{
lean_object* x_9; uint8_t x_10; 
lean_inc(x_1);
x_9 = lean_apply_1(x_1, x_2);
x_10 = 1;
x_2 = x_9;
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; 
lean_dec(x_1);
x_12 = lean_array_push(x_4, x_2);
return x_12;
}
}
}
}
lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(x_1, x_2, x_5, x_4);
return x_6;
}
}
lean_object* l___private_Lean_Level_0__Lean_Level_accMax(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Level_isZero(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Level_addOffsetAux(x_3, x_2);
x_6 = l_Lean_mkLevelMax(x_1, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = l_Lean_Level_addOffsetAux(x_3, x_2);
return x_7;
}
}
}
lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_1);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_9 = lean_nat_add(x_2, x_5);
lean_dec(x_5);
x_10 = l___private_Lean_Level_0__Lean_Level_accMax(x_6, x_4, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_array_fget(x_1, x_3);
x_12 = l_Lean_Level_getLevelOffset(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Level_getOffsetAux(x_11, x_13);
lean_dec(x_11);
x_15 = lean_level_eq(x_12, x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_3, x_16);
lean_dec(x_3);
x_18 = lean_nat_add(x_2, x_5);
lean_dec(x_5);
x_19 = l___private_Lean_Level_0__Lean_Level_accMax(x_6, x_4, x_18);
x_3 = x_17;
x_4 = x_12;
x_5 = x_14;
x_6 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_4);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_3, x_21);
lean_dec(x_3);
x_3 = x_22;
x_4 = x_12;
x_5 = x_14;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Level_0__Lean_Level_mkMaxAux(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_array_fget(x_1, x_2);
x_6 = l_Lean_Level_getLevelOffset(x_5);
lean_dec(x_5);
x_7 = l_Lean_Level_isZero(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Level_0__Lean_Level_skipExplicit(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_array_fget(x_1, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Level_getOffsetAux(x_7, x_8);
lean_dec(x_7);
x_10 = lean_nat_dec_le(x_2, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_3 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_3);
x_14 = 1;
return x_14;
}
}
}
}
lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_2, x_5);
x_7 = l_Lean_instInhabitedLevel;
x_8 = lean_array_get(x_7, x_1, x_6);
lean_dec(x_6);
x_9 = l_Lean_Level_getOffsetAux(x_8, x_3);
lean_dec(x_8);
x_10 = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(x_1, x_9, x_2);
lean_dec(x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_2);
x_11 = 0;
return x_11;
}
}
}
lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at_Lean_Level_normalize___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at_Lean_Level_normalize___spec__1(x_4, x_2, x_3);
x_1 = x_5;
x_3 = x_6;
goto _start;
}
else
{
if (x_2 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Level_normalize(x_1);
lean_dec(x_1);
x_9 = 1;
x_1 = x_8;
x_2 = x_9;
goto _start;
}
else
{
lean_object* x_11; 
x_11 = lean_array_push(x_3, x_1);
return x_11;
}
}
}
}
lean_object* l_Array_qpartition_loop___at_Lean_Level_normalize___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_array_swap(x_4, x_5, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = l_Lean_instInhabitedLevel;
x_11 = lean_array_get(x_10, x_4, x_6);
lean_inc(x_1);
lean_inc(x_3);
x_12 = lean_apply_2(x_1, x_11, x_3);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_6 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_swap(x_4, x_5, x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
x_4 = x_17;
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
}
static lean_object* _init_l_Array_qsort_sort___at_Lean_Level_normalize___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Level_normLt___boxed), 2, 0);
return x_1;
}
}
lean_object* l_Array_qsort_sort___at_Lean_Level_normalize___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_2, x_3);
if (x_13 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_14 = lean_nat_add(x_2, x_3);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_nat_div(x_14, x_15);
lean_dec(x_14);
x_42 = l_Lean_instInhabitedLevel;
x_43 = lean_array_get(x_42, x_1, x_16);
x_44 = lean_array_get(x_42, x_1, x_2);
x_45 = lean_unsigned_to_nat(0u);
x_46 = l_Lean_Level_normLtAux(x_43, x_45, x_44, x_45);
lean_dec(x_44);
lean_dec(x_43);
if (x_46 == 0)
{
x_17 = x_1;
goto block_41;
}
else
{
lean_object* x_47; 
x_47 = lean_array_swap(x_1, x_2, x_16);
x_17 = x_47;
goto block_41;
}
block_41:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = l_Lean_instInhabitedLevel;
x_19 = lean_array_get(x_18, x_17, x_3);
x_20 = lean_array_get(x_18, x_17, x_2);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Level_normLtAux(x_19, x_21, x_20, x_21);
lean_dec(x_20);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_array_get(x_18, x_17, x_16);
x_24 = l_Lean_Level_normLtAux(x_23, x_21, x_19, x_21);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_16);
x_25 = l_Array_qsort_sort___at_Lean_Level_normalize___spec__2___closed__1;
lean_inc_n(x_2, 2);
x_26 = l_Array_qpartition_loop___at_Lean_Level_normalize___spec__3(x_25, x_3, x_19, x_17, x_2, x_2);
x_4 = x_26;
goto block_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_19);
x_27 = lean_array_swap(x_17, x_16, x_3);
lean_dec(x_16);
x_28 = lean_array_get(x_18, x_27, x_3);
x_29 = l_Array_qsort_sort___at_Lean_Level_normalize___spec__2___closed__1;
lean_inc_n(x_2, 2);
x_30 = l_Array_qpartition_loop___at_Lean_Level_normalize___spec__3(x_29, x_3, x_28, x_27, x_2, x_2);
x_4 = x_30;
goto block_12;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_19);
x_31 = lean_array_swap(x_17, x_2, x_3);
x_32 = lean_array_get(x_18, x_31, x_16);
x_33 = lean_array_get(x_18, x_31, x_3);
x_34 = l_Lean_Level_normLtAux(x_32, x_21, x_33, x_21);
lean_dec(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_16);
x_35 = l_Array_qsort_sort___at_Lean_Level_normalize___spec__2___closed__1;
lean_inc_n(x_2, 2);
x_36 = l_Array_qpartition_loop___at_Lean_Level_normalize___spec__3(x_35, x_3, x_33, x_31, x_2, x_2);
x_4 = x_36;
goto block_12;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_33);
x_37 = lean_array_swap(x_31, x_16, x_3);
lean_dec(x_16);
x_38 = lean_array_get(x_18, x_37, x_3);
x_39 = l_Array_qsort_sort___at_Lean_Level_normalize___spec__2___closed__1;
lean_inc_n(x_2, 2);
x_40 = l_Array_qpartition_loop___at_Lean_Level_normalize___spec__3(x_39, x_3, x_38, x_37, x_2, x_2);
x_4 = x_40;
goto block_12;
}
}
}
}
block_12:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_nat_dec_le(x_3, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Array_qsort_sort___at_Lean_Level_normalize___spec__2(x_6, x_2, x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_5, x_9);
lean_dec(x_5);
x_1 = x_8;
x_2 = x_10;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
}
}
static lean_object* _init_l_Lean_Level_normalize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Level.normalize");
return x_1;
}
}
static lean_object* _init_l_Lean_Level_normalize___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Level_mkData___closed__2;
x_2 = l_Lean_Level_normalize___closed__1;
x_3 = lean_unsigned_to_nat(341u);
x_4 = lean_unsigned_to_nat(11u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Level_normalize(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l___private_Lean_Level_0__Lean_Level_isAlreadyNormalizedCheap(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Level_getOffsetAux(x_1, x_3);
x_5 = l_Lean_Level_getLevelOffset(x_1);
switch (lean_obj_tag(x_5)) {
case 2:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = 0;
x_9 = l_Array_empty___closed__1;
x_10 = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at_Lean_Level_normalize___spec__1(x_6, x_8, x_9);
x_11 = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at_Lean_Level_normalize___spec__1(x_7, x_8, x_10);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_12, x_13);
lean_dec(x_12);
x_15 = l_Array_qsort_sort___at_Lean_Level_normalize___spec__2(x_11, x_3, x_14);
lean_dec(x_14);
x_16 = l___private_Lean_Level_0__Lean_Level_skipExplicit(x_15, x_3);
lean_inc(x_16);
x_17 = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_nat_sub(x_16, x_13);
lean_dec(x_16);
x_19 = l_Lean_instInhabitedLevel;
x_20 = lean_array_get(x_19, x_15, x_18);
x_21 = l_Lean_Level_getLevelOffset(x_20);
x_22 = l_Lean_Level_getOffsetAux(x_20, x_3);
lean_dec(x_20);
x_23 = lean_nat_add(x_18, x_13);
lean_dec(x_18);
x_24 = l_Lean_levelZero;
x_25 = l___private_Lean_Level_0__Lean_Level_mkMaxAux(x_15, x_4, x_23, x_21, x_22, x_24);
lean_dec(x_4);
lean_dec(x_15);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = l_Lean_instInhabitedLevel;
x_27 = lean_array_get(x_26, x_15, x_16);
x_28 = l_Lean_Level_getLevelOffset(x_27);
x_29 = l_Lean_Level_getOffsetAux(x_27, x_3);
lean_dec(x_27);
x_30 = lean_nat_add(x_16, x_13);
lean_dec(x_16);
x_31 = l_Lean_levelZero;
x_32 = l___private_Lean_Level_0__Lean_Level_mkMaxAux(x_15, x_4, x_30, x_28, x_29, x_31);
lean_dec(x_4);
lean_dec(x_15);
return x_32;
}
}
case 3:
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_5, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_5, 1);
lean_inc(x_34);
lean_dec(x_5);
x_35 = l_Lean_Level_isNeverZero(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = l_Lean_Level_normalize(x_33);
lean_dec(x_33);
x_37 = l_Lean_Level_normalize(x_34);
lean_dec(x_34);
x_38 = l___private_Lean_Level_0__Lean_Level_mkIMaxAux(x_36, x_37);
x_39 = l_Lean_Level_addOffsetAux(x_4, x_38);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = l_Lean_mkLevelMax(x_33, x_34);
x_41 = l_Lean_Level_normalize(x_40);
lean_dec(x_40);
x_42 = l_Lean_Level_addOffsetAux(x_4, x_41);
return x_42;
}
}
default: 
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_5);
lean_dec(x_4);
x_43 = l_Lean_instInhabitedLevel;
x_44 = l_Lean_Level_normalize___closed__2;
x_45 = lean_panic_fn(x_43, x_44);
return x_45;
}
}
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at_Lean_Level_normalize___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at_Lean_Level_normalize___spec__1(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_Array_qpartition_loop___at_Lean_Level_normalize___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qpartition_loop___at_Lean_Level_normalize___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_qsort_sort___at_Lean_Level_normalize___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at_Lean_Level_normalize___spec__2(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Level_normalize___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_normalize(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_Lean_Level_isEquiv(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_level_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_Level_normalize(x_1);
x_5 = l_Lean_Level_normalize(x_2);
x_6 = lean_level_eq(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
}
lean_object* l_Lean_Level_isEquiv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Level_isEquiv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Level_dec(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
case 2:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Level_dec(x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Level_dec(x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
x_10 = lean_box(0);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = l_Lean_mkLevelMax(x_8, x_12);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = l_Lean_mkLevelMax(x_8, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
case 3:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
x_19 = l_Lean_Level_dec(x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_box(0);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Level_dec(x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_dec(x_21);
x_23 = lean_box(0);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = l_Lean_mkLevelMax(x_21, x_25);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 0);
lean_inc(x_27);
lean_dec(x_22);
x_28 = l_Lean_mkLevelMax(x_21, x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
default: 
{
lean_object* x_30; 
x_30 = lean_box(0);
return x_30;
}
}
}
}
lean_object* l_Lean_Level_dec___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_dec(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Level_PP_Result_succ_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
case 2:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_2, x_7, x_8);
return x_9;
}
default: 
{
lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_apply_1(x_4, x_1);
return x_10;
}
}
}
}
lean_object* l_Lean_Level_PP_Result_succ_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Level_PP_Result_succ_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Level_PP_Result_succ(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_6, x_7);
lean_dec(x_6);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
case 2:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_11, x_12);
lean_dec(x_11);
lean_ctor_set(x_1, 1, x_13);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_15, x_16);
lean_dec(x_15);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
default: 
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Lean_Level_PP_Result_max_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_apply_2(x_3, x_1, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_apply_2(x_4, x_1, x_2);
return x_7;
}
}
}
lean_object* l_Lean_Level_PP_Result_max_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Level_PP_Result_max_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Level_PP_Result_max(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 3)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
lean_object* l_Lean_Level_PP_Result_imax_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_apply_2(x_3, x_1, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_apply_2(x_4, x_1, x_2);
return x_7;
}
}
}
lean_object* l_Lean_Level_PP_Result_imax_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Level_PP_Result_imax_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Level_PP_Result_imax(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 4)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
lean_object* l_Lean_Level_PP_toResult_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint64_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get_uint64(x_1, 0);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
x_10 = lean_apply_1(x_2, x_9);
return x_10;
}
case 1:
{
lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_13 = lean_box_uint64(x_12);
x_14 = lean_apply_2(x_3, x_11, x_13);
return x_14;
}
case 2:
{
lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_18 = lean_box_uint64(x_17);
x_19 = lean_apply_3(x_4, x_15, x_16, x_18);
return x_19;
}
case 3:
{
lean_object* x_20; lean_object* x_21; uint64_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_23 = lean_box_uint64(x_22);
x_24 = lean_apply_3(x_5, x_20, x_21, x_23);
return x_24;
}
case 4:
{
lean_object* x_25; uint64_t x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_27 = lean_box_uint64(x_26);
x_28 = lean_apply_2(x_6, x_25, x_27);
return x_28;
}
default: 
{
lean_object* x_29; uint64_t x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
x_30 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_31 = lean_box_uint64(x_30);
x_32 = lean_apply_2(x_7, x_29, x_31);
return x_32;
}
}
}
}
lean_object* l_Lean_Level_PP_toResult_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Level_PP_toResult_match__1___rarg), 7, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Level_PP_toResult___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Level_PP_toResult___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("?u");
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_toResult___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Level_PP_toResult___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Level_PP_toResult(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
lean_dec(x_1);
x_2 = l_Lean_Level_PP_toResult___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Level_PP_toResult(x_3);
x_5 = l_Lean_Level_PP_Result_succ(x_4);
return x_5;
}
case 2:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_Level_PP_toResult(x_6);
x_9 = l_Lean_Level_PP_toResult(x_7);
x_10 = l_Lean_Level_PP_Result_max(x_8, x_9);
return x_10;
}
case 3:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lean_Level_PP_toResult(x_11);
x_14 = l_Lean_Level_PP_toResult(x_12);
x_15 = l_Lean_Level_PP_Result_imax(x_13, x_14);
return x_15;
}
case 4:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
default: 
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = l_Lean_NameGenerator_namePrefix___default___closed__2;
x_20 = l_Lean_Level_PP_toResult___closed__3;
x_21 = l_Lean_Name_replacePrefix(x_18, x_19, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse_match__1___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (x_2 == 0)
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_apply_1(x_4, x_1);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
}
}
lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse_match__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse_match__1___rarg(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(lean_object* x_1, uint8_t x_2) {
_start:
{
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_3 = l_Std_Format_paren___closed__3;
x_4 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
x_5 = l_Std_Format_paren___closed__4;
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Std_Format_paren___closed__2;
x_8 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = 0;
x_10 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_9);
return x_10;
}
else
{
return x_1;
}
}
}
lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(x_1, x_3);
return x_4;
}
}
lean_object* l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
lean_object* l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Level_PP_Result_format_match__1___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_box(x_2);
x_11 = lean_apply_2(x_3, x_9, x_10);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_box(x_2);
x_14 = lean_apply_2(x_4, x_12, x_13);
return x_14;
}
case 2:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_16, x_19);
lean_dec(x_16);
x_21 = lean_box(x_2);
x_22 = lean_apply_3(x_6, x_15, x_20, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_16);
lean_dec(x_6);
x_23 = lean_box(x_2);
x_24 = lean_apply_2(x_5, x_15, x_23);
return x_24;
}
}
case 3:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_box(x_2);
x_27 = lean_apply_2(x_7, x_25, x_26);
return x_27;
}
default: 
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_box(x_2);
x_30 = lean_apply_2(x_8, x_28, x_29);
return x_30;
}
}
}
}
lean_object* l_Lean_Level_PP_Result_format_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Level_PP_Result_format_match__1___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Level_PP_Result_format_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Level_PP_Result_format_match__1___rarg(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(lean_object* x_1) {
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
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 0;
x_6 = l_Lean_Level_PP_Result_format(x_3, x_5);
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(x_4);
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
lean_object* l_Std_fmt___at_Lean_Level_PP_Result_format___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Name_toString___closed__1;
x_3 = l_Lean_Name_toStringWithSep(x_2, x_1);
x_4 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
lean_object* l_Std_fmt___at_Lean_Level_PP_Result_format___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Nat_repr(x_1);
x_3 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_format___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_stx___x2b___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_format___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_precMax___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_format___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("imax");
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_format___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Level_PP_Result_format___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Level_PP_Result_format(lean_object* x_1, uint8_t x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Std_fmt___at_Lean_Level_PP_Result_format___spec__1(x_3);
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Nat_repr(x_5);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
case 2:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_9, x_12);
lean_dec(x_9);
x_14 = 0;
x_15 = l_Lean_Level_PP_Result_format(x_8, x_14);
x_16 = l_Lean_Level_PP_Result_format___closed__1;
x_17 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_nat_add(x_13, x_12);
lean_dec(x_13);
x_19 = l_Std_fmt___at_Lean_Level_PP_Result_format___spec__2(x_18);
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(x_20, x_2);
return x_21;
}
else
{
lean_dec(x_9);
x_1 = x_8;
goto _start;
}
}
case 3:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_24 = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(x_23);
x_25 = l_Lean_Level_PP_Result_format___closed__2;
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = 0;
x_28 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(x_28, x_2);
return x_29;
}
default: 
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
lean_dec(x_1);
x_31 = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(x_30);
x_32 = l_Lean_Level_PP_Result_format___closed__4;
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = 0;
x_35 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(x_35, x_2);
return x_36;
}
}
}
}
lean_object* l_Lean_Level_PP_Result_format___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Level_PP_Result_format(x_1, x_3);
return x_4;
}
}
lean_object* l_Lean_Level_PP_Result_quote_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_2, x_8);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_1(x_3, x_10);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_13, x_16);
lean_dec(x_13);
x_18 = lean_apply_2(x_5, x_12, x_17);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_13);
lean_dec(x_5);
x_19 = lean_apply_1(x_4, x_12);
return x_19;
}
}
case 3:
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_apply_1(x_6, x_20);
return x_21;
}
default: 
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_apply_1(x_7, x_22);
return x_23;
}
}
}
}
lean_object* l_Lean_Level_PP_Result_quote_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Level_PP_Result_quote_match__1___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Level_PP_Result_quote___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_SourceInfo_fromRef(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Level_PP_Result_quote___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = lean_unsigned_to_nat(1024u);
x_11 = l_Lean_Level_PP_Result_quote(x_9, x_10);
x_12 = 1;
x_13 = x_2 + x_12;
x_14 = x_11;
x_15 = lean_array_uset(x_8, x_2, x_14);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Lean_Level_PP_Result_quote___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_mk_syntax_ident(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
lean_object* l_Lean_Level_PP_Result_quote___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_Nat_repr(x_1);
x_6 = l_Lean_numLitKind;
x_7 = lean_box(2);
x_8 = l_Lean_Syntax_mkLit(x_6, x_5, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("addLit");
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_myMacro____x40_Init_NotationExtra___hyg_1136____closed__30;
x_2 = l_Lean_Level_PP_Result_quote___lambda__3___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Level_PP_Result_quote___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_6 = lean_unsigned_to_nat(65u);
x_7 = l_Lean_Level_PP_Result_quote(x_1, x_6);
x_8 = l_Array_empty___closed__1;
x_9 = lean_array_push(x_8, x_7);
x_10 = l_stx___x2b___closed__3;
x_11 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_array_push(x_9, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_2, x_13);
x_15 = l_Nat_repr(x_14);
x_16 = l_Lean_numLitKind;
x_17 = lean_box(2);
x_18 = l_Lean_Syntax_mkLit(x_16, x_15, x_17);
x_19 = lean_array_push(x_12, x_18);
x_20 = l_Lean_Level_PP_Result_quote___lambda__3___closed__2;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_5);
return x_22;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___lambda__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_myMacro____x40_Init_NotationExtra___hyg_1136____closed__30;
x_2 = l_myMacro____x40_Init_Notation___hyg_13918____closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Level_PP_Result_quote___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = l_prec_x28___x29___closed__3;
lean_inc(x_2);
x_6 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Array_empty___closed__1;
x_8 = lean_array_push(x_7, x_6);
x_9 = lean_array_push(x_8, x_1);
x_10 = l_prec_x28___x29___closed__7;
x_11 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_array_push(x_9, x_11);
x_13 = l_Lean_Level_PP_Result_quote___lambda__4___closed__1;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___lambda__5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_myMacro____x40_Init_NotationExtra___hyg_1136____closed__30;
x_2 = l_precMax___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Level_PP_Result_quote___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_5 = l_precMax___closed__3;
x_6 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Array_empty___closed__1;
x_8 = lean_array_push(x_7, x_6);
x_9 = l_List_redLength___rarg(x_1);
x_10 = lean_mk_empty_array_with_capacity(x_9);
lean_dec(x_9);
x_11 = l_List_toArrayAux___rarg(x_1, x_10);
x_12 = lean_array_get_size(x_11);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = 0;
x_15 = x_11;
x_16 = l_Array_mapMUnsafe_map___at_Lean_Level_PP_Result_quote___spec__2(x_13, x_14, x_15);
x_17 = x_16;
x_18 = l_Array_appendCore___rarg(x_7, x_17);
lean_dec(x_17);
x_19 = l_Lean_nullKind___closed__2;
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_array_push(x_8, x_20);
x_22 = l_Lean_Level_PP_Result_quote___lambda__5___closed__1;
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_4);
return x_24;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___lambda__6___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_myMacro____x40_Init_NotationExtra___hyg_1136____closed__30;
x_2 = l_Lean_Level_PP_Result_format___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Level_PP_Result_quote___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_5 = l_Lean_Level_PP_Result_format___closed__3;
x_6 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Array_empty___closed__1;
x_8 = lean_array_push(x_7, x_6);
x_9 = l_List_redLength___rarg(x_1);
x_10 = lean_mk_empty_array_with_capacity(x_9);
lean_dec(x_9);
x_11 = l_List_toArrayAux___rarg(x_1, x_10);
x_12 = lean_array_get_size(x_11);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = 0;
x_15 = x_11;
x_16 = l_Array_mapMUnsafe_map___at_Lean_Level_PP_Result_quote___spec__2(x_13, x_14, x_15);
x_17 = x_16;
x_18 = l_Array_appendCore___rarg(x_7, x_17);
lean_dec(x_17);
x_19 = l_Lean_nullKind___closed__2;
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_array_push(x_8, x_20);
x_22 = l_Lean_Level_PP_Result_quote___lambda__6___closed__1;
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_4);
return x_24;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Level_PP_Result_quote___spec__1___boxed), 2, 0);
return x_1;
}
}
lean_object* l_Lean_Level_PP_Result_quote(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_Level_PP_Result_quote___lambda__1___boxed), 4, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = l_Lean_Level_PP_Result_quote___closed__1;
x_6 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__2___rarg), 4, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_4);
x_7 = l_Lean_Unhygienic_run___rarg(x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Level_PP_Result_quote___lambda__2___boxed), 4, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = l_Lean_Level_PP_Result_quote___closed__1;
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__2___rarg), 4, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_9);
x_12 = l_Lean_Unhygienic_run___rarg(x_11);
return x_12;
}
case 2:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_14, x_17);
lean_dec(x_14);
x_19 = lean_alloc_closure((void*)(l_Lean_Level_PP_Result_quote___lambda__3___boxed), 5, 2);
lean_closure_set(x_19, 0, x_13);
lean_closure_set(x_19, 1, x_18);
x_20 = l_Lean_Level_PP_Result_quote___closed__1;
x_21 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__2___rarg), 4, 2);
lean_closure_set(x_21, 0, x_20);
lean_closure_set(x_21, 1, x_19);
x_22 = l_Lean_Unhygienic_run___rarg(x_21);
x_23 = lean_nat_dec_lt(x_15, x_2);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_alloc_closure((void*)(l_Lean_Level_PP_Result_quote___lambda__4___boxed), 4, 1);
lean_closure_set(x_24, 0, x_22);
x_25 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__2___rarg), 4, 2);
lean_closure_set(x_25, 0, x_20);
lean_closure_set(x_25, 1, x_24);
x_26 = l_Lean_Unhygienic_run___rarg(x_25);
return x_26;
}
}
else
{
lean_dec(x_14);
x_1 = x_13;
goto _start;
}
}
case 3:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_alloc_closure((void*)(l_Lean_Level_PP_Result_quote___lambda__5___boxed), 4, 1);
lean_closure_set(x_29, 0, x_28);
x_30 = l_Lean_Level_PP_Result_quote___closed__1;
x_31 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__2___rarg), 4, 2);
lean_closure_set(x_31, 0, x_30);
lean_closure_set(x_31, 1, x_29);
x_32 = l_Lean_Unhygienic_run___rarg(x_31);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_nat_dec_lt(x_33, x_2);
if (x_34 == 0)
{
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_alloc_closure((void*)(l_Lean_Level_PP_Result_quote___lambda__4___boxed), 4, 1);
lean_closure_set(x_35, 0, x_32);
x_36 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__2___rarg), 4, 2);
lean_closure_set(x_36, 0, x_30);
lean_closure_set(x_36, 1, x_35);
x_37 = l_Lean_Unhygienic_run___rarg(x_36);
return x_37;
}
}
default: 
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
lean_dec(x_1);
x_39 = lean_alloc_closure((void*)(l_Lean_Level_PP_Result_quote___lambda__6___boxed), 4, 1);
lean_closure_set(x_39, 0, x_38);
x_40 = l_Lean_Level_PP_Result_quote___closed__1;
x_41 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__2___rarg), 4, 2);
lean_closure_set(x_41, 0, x_40);
lean_closure_set(x_41, 1, x_39);
x_42 = l_Lean_Unhygienic_run___rarg(x_41);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_nat_dec_lt(x_43, x_2);
if (x_44 == 0)
{
return x_42;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_alloc_closure((void*)(l_Lean_Level_PP_Result_quote___lambda__4___boxed), 4, 1);
lean_closure_set(x_45, 0, x_42);
x_46 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__2___rarg), 4, 2);
lean_closure_set(x_46, 0, x_40);
lean_closure_set(x_46, 1, x_45);
x_47 = l_Lean_Unhygienic_run___rarg(x_46);
return x_47;
}
}
}
}
}
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Level_PP_Result_quote___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Level_PP_Result_quote___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Level_PP_Result_quote___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Level_PP_Result_quote___spec__2(x_4, x_5, x_3);
return x_6;
}
}
lean_object* l_Lean_Level_PP_Result_quote___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Level_PP_Result_quote___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Level_PP_Result_quote___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Level_PP_Result_quote___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Level_PP_Result_quote___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Level_PP_Result_quote___lambda__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Level_PP_Result_quote___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Level_PP_Result_quote___lambda__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Level_PP_Result_quote___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Level_PP_Result_quote___lambda__5(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Level_PP_Result_quote___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Level_PP_Result_quote___lambda__6(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Level_PP_Result_quote___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Level_PP_Result_quote(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Level_format(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = l_Lean_Level_PP_toResult(x_1);
x_3 = 1;
x_4 = l_Lean_Level_PP_Result_format(x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Level_instToFormatLevel(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_format(x_1);
return x_2;
}
}
lean_object* l_Lean_Level_instToStringLevel(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Level_format(x_1);
x_3 = l_Std_Format_defWidth;
x_4 = lean_format_pretty(x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Level_quote(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Level_PP_toResult(x_1);
x_4 = l_Lean_Level_PP_Result_quote(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Level_quote___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Level_quote(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Level_instQuoteLevel(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Level_quote(x_1, x_2);
return x_3;
}
}
lean_object* lean_level_mk_max_simp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_13; uint8_t x_32; 
x_32 = lean_level_eq(x_1, x_2);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = l_Lean_Level_isZero(x_1);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = l_Lean_Level_isZero(x_2);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = l_Lean_Level_isExplicit(x_2);
if (x_35 == 0)
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
x_38 = lean_level_eq(x_2, x_36);
lean_dec(x_36);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = lean_level_eq(x_2, x_37);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_box(0);
x_13 = x_40;
goto block_31;
}
else
{
lean_dec(x_2);
return x_1;
}
}
else
{
lean_dec(x_37);
lean_dec(x_2);
return x_1;
}
}
else
{
lean_object* x_41; 
x_41 = lean_box(0);
x_13 = x_41;
goto block_31;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_unsigned_to_nat(0u);
x_43 = l_Lean_Level_getOffsetAux(x_2, x_42);
x_44 = l_Lean_Level_getOffsetAux(x_1, x_42);
x_45 = lean_nat_dec_le(x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
if (x_45 == 0)
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_1, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_1, 1);
lean_inc(x_47);
x_48 = lean_level_eq(x_2, x_46);
lean_dec(x_46);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = lean_level_eq(x_2, x_47);
lean_dec(x_47);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_box(0);
x_13 = x_50;
goto block_31;
}
else
{
lean_dec(x_2);
return x_1;
}
}
else
{
lean_dec(x_47);
lean_dec(x_2);
return x_1;
}
}
else
{
lean_object* x_51; 
x_51 = lean_box(0);
x_13 = x_51;
goto block_31;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
else
{
lean_dec(x_1);
return x_2;
}
}
else
{
lean_dec(x_2);
return x_1;
}
block_12:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_dec(x_3);
x_4 = l_Lean_Level_getLevelOffset(x_1);
x_5 = l_Lean_Level_getLevelOffset(x_2);
x_6 = lean_level_eq(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_Lean_mkLevelMax(x_1, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Level_getOffsetAux(x_2, x_8);
x_10 = l_Lean_Level_getOffsetAux(x_1, x_8);
x_11 = lean_nat_dec_le(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
block_31:
{
uint8_t x_14; 
lean_dec(x_13);
x_14 = l_Lean_Level_isExplicit(x_1);
if (x_14 == 0)
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
x_17 = lean_level_eq(x_1, x_15);
lean_dec(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = lean_level_eq(x_1, x_16);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_box(0);
x_3 = x_19;
goto block_12;
}
else
{
lean_dec(x_1);
return x_2;
}
}
else
{
lean_dec(x_16);
lean_dec(x_1);
return x_2;
}
}
else
{
lean_object* x_20; 
x_20 = lean_box(0);
x_3 = x_20;
goto block_12;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Level_getOffsetAux(x_1, x_21);
x_23 = l_Lean_Level_getOffsetAux(x_2, x_21);
x_24 = lean_nat_dec_le(x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
if (x_24 == 0)
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_2, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
x_27 = lean_level_eq(x_1, x_25);
lean_dec(x_25);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = lean_level_eq(x_1, x_26);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_box(0);
x_3 = x_29;
goto block_12;
}
else
{
lean_dec(x_1);
return x_2;
}
}
else
{
lean_dec(x_26);
lean_dec(x_1);
return x_2;
}
}
else
{
lean_object* x_30; 
x_30 = lean_box(0);
x_3 = x_30;
goto block_12;
}
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
}
}
lean_object* lean_level_mk_imax_simp(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Level_isNeverZero(x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = l_Lean_Level_isZero(x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Lean_Level_isZero(x_1);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_level_eq(x_1, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_Lean_mkLevelIMax(x_1, x_2);
return x_7;
}
else
{
lean_dec(x_2);
return x_1;
}
}
else
{
lean_dec(x_1);
return x_2;
}
}
else
{
lean_dec(x_1);
return x_2;
}
}
else
{
lean_object* x_8; 
x_8 = lean_level_mk_max_simp(x_1, x_2);
return x_8;
}
}
}
lean_object* l_Lean_Level_updateSucc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_level_update_succ(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Level_updateSucc_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Level.updateSucc!");
return x_1;
}
}
static lean_object* _init_l_Lean_Level_updateSucc_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("succ level expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Level_updateSucc_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Level_mkData___closed__2;
x_2 = l_Lean_Level_updateSucc_x21___closed__1;
x_3 = lean_unsigned_to_nat(487u);
x_4 = lean_unsigned_to_nat(18u);
x_5 = l_Lean_Level_updateSucc_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Level_updateSucc_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_level_update_succ(x_1, x_2);
return x_4;
}
else
{
lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set_uint64(x_7, sizeof(void*)*1, x_6);
x_8 = lean_level_update_succ(x_7, x_2);
return x_8;
}
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = l_Lean_instInhabitedLevel;
x_10 = l_Lean_Level_updateSucc_x21___closed__3;
x_11 = lean_panic_fn(x_9, x_10);
return x_11;
}
}
}
lean_object* l_Lean_Level_updateMax___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_level_update_max(x_1, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Level_updateMax_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Level.updateMax!");
return x_1;
}
}
static lean_object* _init_l_Lean_Level_updateMax_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("max level expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Level_updateMax_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Level_mkData___closed__2;
x_2 = l_Lean_Level_updateMax_x21___closed__1;
x_3 = lean_unsigned_to_nat(496u);
x_4 = lean_unsigned_to_nat(21u);
x_5 = l_Lean_Level_updateMax_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Level_updateMax_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_level_update_max(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_9 = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set_uint64(x_9, sizeof(void*)*2, x_8);
x_10 = lean_level_update_max(x_9, x_2, x_3);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = l_Lean_instInhabitedLevel;
x_12 = l_Lean_Level_updateMax_x21___closed__3;
x_13 = lean_panic_fn(x_11, x_12);
return x_13;
}
}
}
lean_object* l_Lean_Level_updateIMax___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_level_update_imax(x_1, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Level_updateIMax_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Level.updateIMax!");
return x_1;
}
}
static lean_object* _init_l_Lean_Level_updateIMax_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("imax level expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Level_updateIMax_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Level_mkData___closed__2;
x_2 = l_Lean_Level_updateIMax_x21___closed__1;
x_3 = lean_unsigned_to_nat(505u);
x_4 = lean_unsigned_to_nat(22u);
x_5 = l_Lean_Level_updateIMax_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Level_updateIMax_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_level_update_imax(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_9 = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set_uint64(x_9, sizeof(void*)*2, x_8);
x_10 = lean_level_update_imax(x_9, x_2, x_3);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = l_Lean_instInhabitedLevel;
x_12 = l_Lean_Level_updateIMax_x21___closed__3;
x_13 = lean_panic_fn(x_11, x_12);
return x_13;
}
}
}
lean_object* l_Lean_Level_mkNaryMax_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_2(x_4, x_10, x_7);
return x_11;
}
}
}
}
lean_object* l_Lean_Level_mkNaryMax_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Level_mkNaryMax_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Level_mkNaryMax(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Lean_levelZero;
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
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_Level_mkNaryMax(x_3);
x_7 = lean_level_mk_max_simp(x_5, x_6);
return x_7;
}
}
}
}
lean_object* l_Lean_Level_instantiateParams_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Level_instantiateParams_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Level_instantiateParams_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Level_instantiateParams_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint64_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get_uint64(x_1, 0);
x_9 = lean_box_uint64(x_8);
x_10 = lean_apply_2(x_2, x_1, x_9);
return x_10;
}
case 1:
{
lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_13 = lean_box_uint64(x_12);
x_14 = lean_apply_3(x_3, x_1, x_11, x_13);
return x_14;
}
case 2:
{
lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_18 = lean_box_uint64(x_17);
x_19 = lean_apply_4(x_4, x_1, x_15, x_16, x_18);
return x_19;
}
case 3:
{
lean_object* x_20; lean_object* x_21; uint64_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_23 = lean_box_uint64(x_22);
x_24 = lean_apply_4(x_5, x_1, x_20, x_21, x_23);
return x_24;
}
case 4:
{
lean_object* x_25; uint64_t x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_27 = lean_box_uint64(x_26);
x_28 = lean_apply_3(x_6, x_1, x_25, x_27);
return x_28;
}
default: 
{
lean_object* x_29; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_apply_1(x_7, x_1);
return x_29;
}
}
}
}
lean_object* l_Lean_Level_instantiateParams_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Level_instantiateParams_match__2___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Level_instantiateParams(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_3; uint64_t x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get_uint64(x_2, sizeof(void*)*1);
x_5 = l_Lean_Level_hasParam(x_2);
if (x_5 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_dec(x_7);
lean_inc(x_3);
x_8 = l_Lean_Level_instantiateParams(x_1, x_3);
x_9 = lean_level_update_succ(x_2, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
lean_inc(x_3);
x_10 = l_Lean_Level_instantiateParams(x_1, x_3);
x_11 = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set_uint64(x_11, sizeof(void*)*1, x_4);
x_12 = lean_level_update_succ(x_11, x_10);
return x_12;
}
}
}
case 2:
{
lean_object* x_13; lean_object* x_14; uint64_t x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
x_15 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_16 = l_Lean_Level_hasParam(x_2);
if (x_16 == 0)
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_2, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_2, 0);
lean_dec(x_19);
lean_inc(x_13);
lean_inc(x_1);
x_20 = l_Lean_Level_instantiateParams(x_1, x_13);
lean_inc(x_14);
x_21 = l_Lean_Level_instantiateParams(x_1, x_14);
x_22 = lean_level_update_max(x_2, x_20, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
lean_inc(x_13);
lean_inc(x_1);
x_23 = l_Lean_Level_instantiateParams(x_1, x_13);
lean_inc(x_14);
x_24 = l_Lean_Level_instantiateParams(x_1, x_14);
x_25 = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_14);
lean_ctor_set_uint64(x_25, sizeof(void*)*2, x_15);
x_26 = lean_level_update_max(x_25, x_23, x_24);
return x_26;
}
}
}
case 3:
{
lean_object* x_27; lean_object* x_28; uint64_t x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_2, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_2, 1);
lean_inc(x_28);
x_29 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_30 = l_Lean_Level_hasParam(x_2);
if (x_30 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_2);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_2, 1);
lean_dec(x_32);
x_33 = lean_ctor_get(x_2, 0);
lean_dec(x_33);
lean_inc(x_27);
lean_inc(x_1);
x_34 = l_Lean_Level_instantiateParams(x_1, x_27);
lean_inc(x_28);
x_35 = l_Lean_Level_instantiateParams(x_1, x_28);
x_36 = lean_level_update_imax(x_2, x_34, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_2);
lean_inc(x_27);
lean_inc(x_1);
x_37 = l_Lean_Level_instantiateParams(x_1, x_27);
lean_inc(x_28);
x_38 = l_Lean_Level_instantiateParams(x_1, x_28);
x_39 = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(x_39, 0, x_27);
lean_ctor_set(x_39, 1, x_28);
lean_ctor_set_uint64(x_39, sizeof(void*)*2, x_29);
x_40 = lean_level_update_imax(x_39, x_37, x_38);
return x_40;
}
}
}
case 4:
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_2, 0);
lean_inc(x_41);
x_42 = lean_apply_1(x_1, x_41);
if (lean_obj_tag(x_42) == 0)
{
return x_2;
}
else
{
lean_object* x_43; 
lean_dec(x_2);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec(x_42);
return x_43;
}
}
default: 
{
lean_dec(x_1);
return x_2;
}
}
}
}
lean_object* l_Lean_Level_collectMVars_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
x_10 = lean_apply_2(x_2, x_7, x_9);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; uint64_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_14 = lean_box_uint64(x_13);
x_15 = lean_apply_3(x_3, x_11, x_12, x_14);
return x_15;
}
case 3:
{
lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_19 = lean_box_uint64(x_18);
x_20 = lean_apply_3(x_4, x_16, x_17, x_19);
return x_20;
}
case 5:
{
lean_object* x_21; uint64_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_23 = lean_box_uint64(x_22);
x_24 = lean_apply_2(x_5, x_21, x_23);
return x_24;
}
default: 
{
lean_object* x_25; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_apply_1(x_6, x_1);
return x_25;
}
}
}
}
lean_object* l_Lean_Level_collectMVars_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Level_collectMVars_match__1___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Level_collectMVars(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_1 = x_3;
goto _start;
}
case 2:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_Level_collectMVars(x_6, x_2);
x_1 = x_5;
x_2 = x_7;
goto _start;
}
case 3:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_Level_collectMVars(x_10, x_2);
x_1 = x_9;
x_2 = x_11;
goto _start;
}
case 5:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_2, x_13, x_14);
return x_15;
}
default: 
{
lean_dec(x_1);
return x_2;
}
}
}
}
lean_object* l_Lean_Level_find_x3f_visit_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_2(x_2, x_6, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_13 = lean_box_uint64(x_12);
x_14 = lean_apply_3(x_3, x_10, x_11, x_13);
return x_14;
}
case 3:
{
lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_18 = lean_box_uint64(x_17);
x_19 = lean_apply_3(x_4, x_15, x_16, x_18);
return x_19;
}
default: 
{
lean_object* x_20; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_apply_1(x_5, x_1);
return x_20;
}
}
}
}
lean_object* l_Lean_Level_find_x3f_visit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Level_find_x3f_visit_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Level_find_x3f_visit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
lean_inc(x_1);
lean_inc(x_2);
x_3 = lean_apply_1(x_1, x_2);
x_4 = lean_unbox(x_3);
lean_dec(x_3);
if (x_4 == 0)
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_2 = x_5;
goto _start;
}
case 2:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_1);
x_9 = l_Lean_Level_find_x3f_visit(x_1, x_7);
if (lean_obj_tag(x_9) == 0)
{
x_2 = x_8;
goto _start;
}
else
{
uint8_t x_11; 
lean_dec(x_8);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
return x_9;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
case 3:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
lean_inc(x_1);
x_16 = l_Lean_Level_find_x3f_visit(x_1, x_14);
if (lean_obj_tag(x_16) == 0)
{
x_2 = x_15;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_15);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
default: 
{
lean_object* x_21; 
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_box(0);
return x_21;
}
}
}
else
{
lean_object* x_22; 
lean_dec(x_1);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_2);
return x_22;
}
}
}
lean_object* l_Lean_Level_find_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Level_find_x3f_visit(x_2, x_1);
return x_3;
}
}
uint8_t l_Lean_Level_any(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Level_find_x3f_visit(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 1;
return x_5;
}
}
}
lean_object* l_Lean_Level_any___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Level_any(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Nat_toLevel(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
lean_object* l_Nat_toLevel___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_toLevel(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Std_Data_HashMap(lean_object*);
lean_object* initialize_Std_Data_HashSet(lean_object*);
lean_object* initialize_Std_Data_PersistentHashMap(lean_object*);
lean_object* initialize_Std_Data_PersistentHashSet(lean_object*);
lean_object* initialize_Lean_Hygiene(lean_object*);
lean_object* initialize_Lean_Data_Name(lean_object*);
lean_object* initialize_Lean_Data_Format(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Level(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashSet(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_PersistentHashMap(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_PersistentHashSet(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Hygiene(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Name(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Format(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedData = _init_l_Lean_instInhabitedData();
l_Lean_Level_mkData___closed__1 = _init_l_Lean_Level_mkData___closed__1();
lean_mark_persistent(l_Lean_Level_mkData___closed__1);
l_Lean_Level_mkData___closed__2 = _init_l_Lean_Level_mkData___closed__2();
lean_mark_persistent(l_Lean_Level_mkData___closed__2);
l_Lean_Level_mkData___closed__3 = _init_l_Lean_Level_mkData___closed__3();
lean_mark_persistent(l_Lean_Level_mkData___closed__3);
l_Lean_Level_mkData___closed__4 = _init_l_Lean_Level_mkData___closed__4();
lean_mark_persistent(l_Lean_Level_mkData___closed__4);
l_Lean_Level_mkData___closed__5 = _init_l_Lean_Level_mkData___closed__5();
lean_mark_persistent(l_Lean_Level_mkData___closed__5);
l_Lean_Level_mkData___boxed__const__1 = _init_l_Lean_Level_mkData___boxed__const__1();
lean_mark_persistent(l_Lean_Level_mkData___boxed__const__1);
l_Lean_instInhabitedLevel___closed__1 = _init_l_Lean_instInhabitedLevel___closed__1();
lean_mark_persistent(l_Lean_instInhabitedLevel___closed__1);
l_Lean_instInhabitedLevel = _init_l_Lean_instInhabitedLevel();
lean_mark_persistent(l_Lean_instInhabitedLevel);
l_Lean_Level_instHashableLevel___closed__1 = _init_l_Lean_Level_instHashableLevel___closed__1();
lean_mark_persistent(l_Lean_Level_instHashableLevel___closed__1);
l_Lean_Level_instHashableLevel = _init_l_Lean_Level_instHashableLevel();
lean_mark_persistent(l_Lean_Level_instHashableLevel);
l_Lean_levelZero___closed__1 = _init_l_Lean_levelZero___closed__1();
l_Lean_levelZero___closed__2 = _init_l_Lean_levelZero___closed__2();
lean_mark_persistent(l_Lean_levelZero___closed__2);
l_Lean_levelZero = _init_l_Lean_levelZero();
lean_mark_persistent(l_Lean_levelZero);
l_Lean_levelOne___closed__1 = _init_l_Lean_levelOne___closed__1();
lean_mark_persistent(l_Lean_levelOne___closed__1);
l_Lean_levelOne = _init_l_Lean_levelOne();
lean_mark_persistent(l_Lean_levelOne);
l_Lean_Level_mvarId_x21___closed__1 = _init_l_Lean_Level_mvarId_x21___closed__1();
lean_mark_persistent(l_Lean_Level_mvarId_x21___closed__1);
l_Lean_Level_mvarId_x21___closed__2 = _init_l_Lean_Level_mvarId_x21___closed__2();
lean_mark_persistent(l_Lean_Level_mvarId_x21___closed__2);
l_Lean_Level_mvarId_x21___closed__3 = _init_l_Lean_Level_mvarId_x21___closed__3();
lean_mark_persistent(l_Lean_Level_mvarId_x21___closed__3);
l_Lean_Level_instBEqLevel___closed__1 = _init_l_Lean_Level_instBEqLevel___closed__1();
lean_mark_persistent(l_Lean_Level_instBEqLevel___closed__1);
l_Lean_Level_instBEqLevel = _init_l_Lean_Level_instBEqLevel();
lean_mark_persistent(l_Lean_Level_instBEqLevel);
l_Array_qsort_sort___at_Lean_Level_normalize___spec__2___closed__1 = _init_l_Array_qsort_sort___at_Lean_Level_normalize___spec__2___closed__1();
lean_mark_persistent(l_Array_qsort_sort___at_Lean_Level_normalize___spec__2___closed__1);
l_Lean_Level_normalize___closed__1 = _init_l_Lean_Level_normalize___closed__1();
lean_mark_persistent(l_Lean_Level_normalize___closed__1);
l_Lean_Level_normalize___closed__2 = _init_l_Lean_Level_normalize___closed__2();
lean_mark_persistent(l_Lean_Level_normalize___closed__2);
l_Lean_Level_PP_toResult___closed__1 = _init_l_Lean_Level_PP_toResult___closed__1();
lean_mark_persistent(l_Lean_Level_PP_toResult___closed__1);
l_Lean_Level_PP_toResult___closed__2 = _init_l_Lean_Level_PP_toResult___closed__2();
lean_mark_persistent(l_Lean_Level_PP_toResult___closed__2);
l_Lean_Level_PP_toResult___closed__3 = _init_l_Lean_Level_PP_toResult___closed__3();
lean_mark_persistent(l_Lean_Level_PP_toResult___closed__3);
l_Lean_Level_PP_Result_format___closed__1 = _init_l_Lean_Level_PP_Result_format___closed__1();
lean_mark_persistent(l_Lean_Level_PP_Result_format___closed__1);
l_Lean_Level_PP_Result_format___closed__2 = _init_l_Lean_Level_PP_Result_format___closed__2();
lean_mark_persistent(l_Lean_Level_PP_Result_format___closed__2);
l_Lean_Level_PP_Result_format___closed__3 = _init_l_Lean_Level_PP_Result_format___closed__3();
lean_mark_persistent(l_Lean_Level_PP_Result_format___closed__3);
l_Lean_Level_PP_Result_format___closed__4 = _init_l_Lean_Level_PP_Result_format___closed__4();
lean_mark_persistent(l_Lean_Level_PP_Result_format___closed__4);
l_Lean_Level_PP_Result_quote___lambda__3___closed__1 = _init_l_Lean_Level_PP_Result_quote___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___lambda__3___closed__1);
l_Lean_Level_PP_Result_quote___lambda__3___closed__2 = _init_l_Lean_Level_PP_Result_quote___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___lambda__3___closed__2);
l_Lean_Level_PP_Result_quote___lambda__4___closed__1 = _init_l_Lean_Level_PP_Result_quote___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___lambda__4___closed__1);
l_Lean_Level_PP_Result_quote___lambda__5___closed__1 = _init_l_Lean_Level_PP_Result_quote___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___lambda__5___closed__1);
l_Lean_Level_PP_Result_quote___lambda__6___closed__1 = _init_l_Lean_Level_PP_Result_quote___lambda__6___closed__1();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___lambda__6___closed__1);
l_Lean_Level_PP_Result_quote___closed__1 = _init_l_Lean_Level_PP_Result_quote___closed__1();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___closed__1);
l_Lean_Level_updateSucc_x21___closed__1 = _init_l_Lean_Level_updateSucc_x21___closed__1();
lean_mark_persistent(l_Lean_Level_updateSucc_x21___closed__1);
l_Lean_Level_updateSucc_x21___closed__2 = _init_l_Lean_Level_updateSucc_x21___closed__2();
lean_mark_persistent(l_Lean_Level_updateSucc_x21___closed__2);
l_Lean_Level_updateSucc_x21___closed__3 = _init_l_Lean_Level_updateSucc_x21___closed__3();
lean_mark_persistent(l_Lean_Level_updateSucc_x21___closed__3);
l_Lean_Level_updateMax_x21___closed__1 = _init_l_Lean_Level_updateMax_x21___closed__1();
lean_mark_persistent(l_Lean_Level_updateMax_x21___closed__1);
l_Lean_Level_updateMax_x21___closed__2 = _init_l_Lean_Level_updateMax_x21___closed__2();
lean_mark_persistent(l_Lean_Level_updateMax_x21___closed__2);
l_Lean_Level_updateMax_x21___closed__3 = _init_l_Lean_Level_updateMax_x21___closed__3();
lean_mark_persistent(l_Lean_Level_updateMax_x21___closed__3);
l_Lean_Level_updateIMax_x21___closed__1 = _init_l_Lean_Level_updateIMax_x21___closed__1();
lean_mark_persistent(l_Lean_Level_updateIMax_x21___closed__1);
l_Lean_Level_updateIMax_x21___closed__2 = _init_l_Lean_Level_updateIMax_x21___closed__2();
lean_mark_persistent(l_Lean_Level_updateIMax_x21___closed__2);
l_Lean_Level_updateIMax_x21___closed__3 = _init_l_Lean_Level_updateIMax_x21___closed__3();
lean_mark_persistent(l_Lean_Level_updateIMax_x21___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

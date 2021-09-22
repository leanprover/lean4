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
LEAN_EXPORT lean_object* l_Lean_Level_dec(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Level_PP_Result_quote___lambda__3___closed__9;
static lean_object* l_Array_qsort_sort___at_Lean_Level_normalize___spec__2___closed__1;
size_t l_USize_add(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_Level_isNeverZero(lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Level_normalize___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_isMax___boxed(lean_object*);
static lean_object* l_Lean_Level_PP_Result_quote___lambda__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_Level_collectMVars(lean_object*, lean_object*);
static lean_object* l_Lean_Level_mvarId_x21___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Level_PP_Result_format___closed__4;
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t l_UInt64_decEq(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Level_data___boxed(lean_object*);
static lean_object* l_Lean_Level_mvarId_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Level_mvarId_x21___boxed(lean_object*);
static lean_object* l_Lean_Level_PP_Result_quote___lambda__3___closed__8;
static lean_object* l_Lean_Level_PP_Result_format___closed__1;
LEAN_EXPORT lean_object* l_Lean_Level_quote___boxed(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_isMVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_updateIMax___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qpartition_loop___at_Lean_Level_normalize___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Level_mkData___closed__3;
extern lean_object* l_Std_Format_defWidth;
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint64_t l_UInt64_add(uint64_t, uint64_t);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*);
uint64_t l_Bool_toUInt64(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkIMaxAux(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Level_PP_Result_quote___spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_getOffsetAux___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_updateMax_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_level_mk_max(lean_object*, lean_object*);
static lean_object* l_Lean_Level_PP_toResult___closed__4;
static lean_object* l_Lean_Level_instHashableLevel___closed__1;
LEAN_EXPORT lean_object* l_Lean_Level_instToStringLevel(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_mkData___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Level_mkData___closed__1;
LEAN_EXPORT lean_object* l_Lean_Level_ctorToNat___boxed(lean_object*);
LEAN_EXPORT lean_object* lean_level_mk_succ(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_hasMVarEx___boxed(lean_object*);
static lean_object* l_Lean_Level_mkData___closed__2;
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isEquiv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instBEqLevel;
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Level_PP_Result_quote___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_hashMVarId____x40_Lean_Level___hyg_205____boxed(lean_object*);
LEAN_EXPORT uint8_t lean_level_has_param(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Level_hash(lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__4;
LEAN_EXPORT lean_object* l_Lean_Level_isExplicit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarId(lean_object*);
LEAN_EXPORT uint32_t lean_level_hash(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_hasParamEx___boxed(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMVarIdSetInhabited;
static lean_object* l_Lean_Level_mkData___closed__4;
lean_object* l_Nat_max(lean_object*, lean_object*);
static lean_object* l_Lean_Level_PP_toResult___closed__1;
LEAN_EXPORT lean_object* l_Lean_Level_getOffsetAux(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_hasParam(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Level_collectMVars___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_depth(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_isSucc___boxed(lean_object*);
static lean_object* l_Lean_Level_updateIMax_x21___closed__1;
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_isAlreadyNormalizedCheap(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_mvarId_x21(lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Level_instToFormatLevel(lean_object*);
LEAN_EXPORT lean_object* l_Lean_levelZero;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Level_updateMax_x21___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isAlreadyNormalizedCheap___boxed(lean_object*);
static lean_object* l_Lean_Level_PP_Result_format___closed__6;
static lean_object* l_Lean_instForInMVarIdSetMVarId___closed__2;
static lean_object* l_Lean_Level_mvarId_x21___closed__3;
extern uint64_t l_instInhabitedUInt64;
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Data_hash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_getLevelOffset___boxed(lean_object*);
static lean_object* l_Lean_instBEqMVarId___closed__1;
LEAN_EXPORT lean_object* l_Lean_Level_Data_hasMVar___boxed(lean_object*);
lean_object* l_Std_RBTree_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_updateIMax_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_setBlack___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLevelIMax(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_level_has_mvar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_isNeverZero___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_normLtAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_format___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isParam(lean_object*);
static lean_object* l_Lean_Level_PP_Result_format___closed__2;
LEAN_EXPORT lean_object* l_Lean_Level_updateSucc_x21(lean_object*, lean_object*);
static lean_object* l_Lean_Level_updateMax_x21___closed__1;
extern lean_object* l_Lean_numLitKind;
lean_object* l_ReaderT_bind___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_isParam___boxed(lean_object*);
static lean_object* l_Lean_Level_PP_toResult___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT uint32_t lean_level_depth(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_isIMax___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_insert___at_Lean_Level_collectMVars___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at_Lean_Level_normalize___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instHashableLevel;
static uint64_t l_Lean_levelZero___closed__1;
LEAN_EXPORT uint64_t l_Lean_Level_data(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_any___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Level_PP_Result_quote___lambda__3___closed__7;
LEAN_EXPORT uint64_t l_Lean_Level_mkData(uint64_t, lean_object*, uint8_t, uint8_t);
lean_object* lean_level_update_max(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_any(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_level_mk_max_simp(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
static lean_object* l_Lean_Level_normalize___closed__1;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint32_t l_UInt64_toUInt32(uint64_t);
static lean_object* l_Lean_instHashableMVarId___closed__1;
lean_object* l_Lean_Unhygienic_run___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLevelMax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprMVarId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMVarIdSetEmptyCollection;
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_depth___boxed(lean_object*);
LEAN_EXPORT lean_object* lean_level_mk_imax_simp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_toNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_normLtAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_beqMVarId____x40_Lean_Level___hyg_158_(lean_object*, lean_object*);
uint64_t l_Lean_Name_hash(lean_object*);
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_Lean_Level_updateSucc_x21___closed__3;
static lean_object* l_Lean_Level_PP_Result_quote___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instForInMVarIdSetMVarId___closed__1;
LEAN_EXPORT lean_object* l_Lean_Level_toNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_addOffset(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Level_Data_hash(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Level_addOffsetAux(lean_object*, lean_object*);
static lean_object* l_Lean_Level_PP_Result_quote___lambda__4___closed__2;
lean_object* lean_format_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_updateMax___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_occurs___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_instInhabitedLevel___closed__2;
LEAN_EXPORT lean_object* l_Lean_Level_isZero___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_ctorToNat(lean_object*);
static lean_object* l_Lean_Level_updateMax_x21___closed__3;
static uint64_t l_Lean_instInhabitedLevel___closed__1;
LEAN_EXPORT lean_object* l_Lean_Level_ofNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqData___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_updateSucc___boxed(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
static lean_object* l_Lean_Level_PP_toResult___closed__5;
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_accMax(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_succ(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Level_0__Lean_hashMVarId____x40_Lean_Level___hyg_205_(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_Data_hasParam(uint64_t);
uint64_t l_UInt64_land(uint64_t, uint64_t);
static lean_object* l_Lean_Level_normalize___closed__4;
LEAN_EXPORT lean_object* l_Lean_instHashableMVarId;
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit___boxed(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isIMax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Level_getOffset___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_qpartition_loop___at_Lean_Level_normalize___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLevelMVar(lean_object*);
static lean_object* l_Lean_Level_PP_Result_quote___closed__1;
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_max(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_normalize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_toLevel(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_normLt(lean_object*, lean_object*);
static lean_object* l_Lean_Level_PP_Result_format___closed__3;
static lean_object* l_Lean_Level_PP_Result_quote___lambda__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imax(lean_object*, lean_object*);
static lean_object* l_Lean_Level_PP_Result_format___closed__5;
static lean_object* l_Lean_Level_PP_Result_quote___lambda__3___closed__6;
LEAN_EXPORT lean_object* lean_level_mk_param(lean_object*);
static lean_object* l_Lean_Level_normalize___closed__2;
lean_object* lean_level_update_imax(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_imax___boxed(lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqData(uint64_t, uint64_t);
static lean_object* l_Lean_Level_updateIMax_x21___closed__3;
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarId;
static lean_object* l_Lean_levelOne___closed__1;
LEAN_EXPORT lean_object* l_Lean_instBEqMVarId;
static lean_object* l_Lean_levelZero___closed__2;
LEAN_EXPORT lean_object* l_Lean_Level_isMaxIMax___boxed(lean_object*);
uint8_t l_Lean_Name_lt(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Level_Data_depth(uint64_t);
LEAN_EXPORT lean_object* l_Lean_mkLevelSucc(lean_object*);
static lean_object* l_Lean_Level_PP_Result_quote___lambda__3___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Level_PP_toResult___closed__3;
LEAN_EXPORT lean_object* l_Lean_Level_instQuoteLevel(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_find_x3f(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Std_RBNode_isRed___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_Data_hasMVar(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Level_normLt___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_mkNaryMax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Data_depth___boxed(lean_object*);
static lean_object* l_Lean_Level_PP_Result_quote___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Level_normalize(lean_object*);
uint64_t l_UInt64_shiftLeft(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_instReprMVarId___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Level_PP_Result_quote___lambda__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_mkData___boxed__const__1;
static lean_object* l_Lean_Level_updateSucc_x21___closed__2;
static lean_object* l_Lean_Level_PP_Result_quote___lambda__3___closed__2;
LEAN_EXPORT uint8_t l_Lean_Level_isMVar(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_beqMVarId____x40_Lean_Level___hyg_158____boxed(lean_object*, lean_object*);
uint64_t l_UInt32_toUInt64(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_format(lean_object*, uint8_t);
LEAN_EXPORT lean_object* lean_level_mk_imax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_imax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Level_PP_Result_quote___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_depthEx___boxed(lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__3;
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
lean_object* lean_level_update_succ(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_getLevelOffset(lean_object*);
static lean_object* l_Lean_Level_PP_Result_quote___lambda__5___closed__3;
LEAN_EXPORT lean_object* l_Lean_Level_dec___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_find_x3f_visit(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_instInhabitedData;
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_isEquiv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at_Lean_Level_normalize___spec__1(lean_object*, uint8_t, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* lean_level_mk_zero(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isZero(lean_object*);
static lean_object* l_Lean_Level_PP_Result_quote___lambda__5___closed__2;
LEAN_EXPORT lean_object* l_Lean_Level_hasParam___boxed(lean_object*);
lean_object* lean_string_length(lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2;
LEAN_EXPORT uint8_t l_Lean_Level_occurs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_hashEx___boxed(lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1;
LEAN_EXPORT lean_object* l_Lean_Level_hasMVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___boxed(lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isMaxIMax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_hash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isSucc(lean_object*);
static lean_object* l_Lean_Level_PP_Result_quote___lambda__5___closed__1;
LEAN_EXPORT uint8_t l_Lean_Level_isExplicit(lean_object*);
static lean_object* l_Lean_Level_updateSucc_x21___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
uint64_t l_UInt64_shiftRight(uint64_t, uint64_t);
static lean_object* l_Lean_Level_instBEqLevel___closed__1;
LEAN_EXPORT lean_object* l_Lean_mkLevelParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_levelOne;
uint8_t lean_level_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Level_PP_Result_quote___lambda__5___closed__4;
LEAN_EXPORT lean_object* l_Lean_Level_beq___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Level_mkData___closed__5;
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Level_normalize___closed__3;
LEAN_EXPORT lean_object* lean_level_mk_mvar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_format(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_quote(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Level_normalize___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Data_hasParam___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Level_updateIMax_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Level_PP_toResult(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_getOffset(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(lean_object*);
LEAN_EXPORT lean_object* l_Nat_toLevel___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isMax(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedLevel;
lean_object* l_Lean_Syntax_mkLit(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap(lean_object*);
LEAN_EXPORT lean_object* l_Nat_imax(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Nat_imax___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint64_t l_Lean_Level_Data_hash(uint64_t x_1) {
_start:
{
uint32_t x_2; uint64_t x_3; 
x_2 = ((uint32_t)x_1);
x_3 = ((uint64_t)x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Data_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lean_Level_Data_hash(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqData(uint64_t x_1, uint64_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 == x_2;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqData___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint32_t l_Lean_Level_Data_depth(uint64_t x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint32_t x_4; 
x_2 = 40;
x_3 = x_1 >> x_2 % 64;
x_4 = ((uint32_t)x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Data_depth___boxed(lean_object* x_1) {
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
LEAN_EXPORT uint8_t l_Lean_Level_Data_hasMVar(uint64_t x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Level_Data_hasMVar___boxed(lean_object* x_1) {
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
LEAN_EXPORT uint8_t l_Lean_Level_Data_hasParam(uint64_t x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Level_Data_hasParam___boxed(lean_object* x_1) {
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
LEAN_EXPORT uint64_t l_Lean_Level_mkData(uint64_t x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Level_mkData___closed__1;
x_6 = lean_nat_dec_lt(x_5, x_2);
if (x_6 == 0)
{
uint32_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; 
x_7 = ((uint32_t)x_1);
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
LEAN_EXPORT lean_object* l_Lean_Level_mkData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; uint8_t x_6; uint8_t x_7; uint64_t x_8; lean_object* x_9; 
x_5 = lean_unbox_uint64(x_1);
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
static lean_object* _init_l_Lean_instInhabitedMVarId() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_beqMVarId____x40_Lean_Level___hyg_158_(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_name_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_beqMVarId____x40_Lean_Level___hyg_158____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Level_0__Lean_beqMVarId____x40_Lean_Level___hyg_158_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instBEqMVarId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Level_0__Lean_beqMVarId____x40_Lean_Level___hyg_158____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instBEqMVarId() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instBEqMVarId___closed__1;
return x_1;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Level_0__Lean_hashMVarId____x40_Lean_Level___hyg_205_(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; 
x_2 = 0;
x_3 = l_Lean_Name_hash(x_1);
x_4 = lean_uint64_mix_hash(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_hashMVarId____x40_Lean_Level___hyg_205____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Level_0__Lean_hashMVarId____x40_Lean_Level___hyg_205_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instHashableMVarId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Level_0__Lean_hashMVarId____x40_Lean_Level___hyg_205____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instHashableMVarId() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instHashableMVarId___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprMVarId(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Name_reprPrec(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprMVarId___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instReprMVarId(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instMVarIdSetInhabited() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_instMVarIdSetEmptyCollection() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_instForInMVarIdSetMVarId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instForInMVarIdSetMVarId___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instForInMVarIdSetMVarId___closed__1;
x_2 = lean_alloc_closure((void*)(l_Std_RBTree_forIn___boxed), 4, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
lean_closure_set(x_2, 2, lean_box(0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instForInMVarIdSetMVarId___closed__2;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static uint64_t _init_l_Lean_instInhabitedLevel___closed__1() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedLevel___closed__2() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_Lean_instInhabitedLevel___closed__1;
x_2 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint64(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedLevel() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedLevel___closed__2;
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lean_Level_data(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Level_data___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Level_data(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Lean_Level_hash(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint64_t x_2; uint64_t x_3; 
x_2 = lean_ctor_get_uint64(x_1, 0);
x_3 = l_Lean_Level_Data_hash(x_2);
return x_3;
}
case 2:
{
uint64_t x_4; uint64_t x_5; 
x_4 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_5 = l_Lean_Level_Data_hash(x_4);
return x_5;
}
case 3:
{
uint64_t x_6; uint64_t x_7; 
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_7 = l_Lean_Level_Data_hash(x_6);
return x_7;
}
default: 
{
uint64_t x_8; uint64_t x_9; 
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_9 = l_Lean_Level_Data_hash(x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Level_hash(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Level_depth(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Level_depth___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_depth(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_hasMVar(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Level_hasMVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Level_hasMVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_hasParam(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Level_hasParam___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Level_hasParam(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint32_t lean_level_hash(lean_object* x_1) {
_start:
{
uint64_t x_2; uint32_t x_3; 
x_2 = l_Lean_Level_hash(x_1);
lean_dec(x_1);
x_3 = ((uint32_t)x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hashEx___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_level_hash(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lean_level_has_mvar(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Level_hasMVar(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hasMVarEx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_level_has_mvar(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lean_level_has_param(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Level_hasParam(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_hasParamEx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_level_has_param(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint32_t lean_level_depth(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Level_depthEx___boxed(lean_object* x_1) {
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
uint64_t x_1; lean_object* x_2; uint8_t x_3; uint64_t x_4; 
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
LEAN_EXPORT lean_object* l_Lean_mkLevelMVar(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint64_t x_8; lean_object* x_9; 
x_2 = 2237;
x_3 = l___private_Lean_Level_0__Lean_hashMVarId____x40_Lean_Level___hyg_205_(x_1);
x_4 = lean_uint64_mix_hash(x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lean_mkLevelParam(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint64_t x_8; lean_object* x_9; 
x_2 = 2239;
x_3 = l_Lean_Name_hash(x_1);
x_4 = lean_uint64_mix_hash(x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lean_mkLevelSucc(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint64_t x_10; lean_object* x_11; 
x_2 = 2243;
x_3 = l_Lean_Level_hash(x_1);
x_4 = lean_uint64_mix_hash(x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lean_mkLevelMax(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_3 = 2251;
x_4 = l_Lean_Level_hash(x_1);
x_5 = l_Lean_Level_hash(x_2);
x_6 = lean_uint64_mix_hash(x_4, x_5);
x_7 = lean_uint64_mix_hash(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Lean_mkLevelIMax(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_3 = 2267;
x_4 = l_Lean_Level_hash(x_1);
x_5 = l_Lean_Level_hash(x_2);
x_6 = lean_uint64_mix_hash(x_4, x_5);
x_7 = lean_uint64_mix_hash(x_3, x_6);
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
LEAN_EXPORT lean_object* lean_level_mk_zero(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_dec(x_1);
x_2 = l_Lean_levelZero;
return x_2;
}
}
LEAN_EXPORT lean_object* lean_level_mk_succ(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkLevelSucc(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_level_mk_mvar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkLevelMVar(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_level_mk_param(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkLevelParam(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_level_mk_max(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkLevelMax(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_level_mk_imax(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkLevelIMax(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isZero(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Level_isZero___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Level_isZero(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isSucc(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Level_isSucc___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Level_isSucc(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isMax(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Level_isMax___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Level_isMax(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isIMax(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Level_isIMax___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Level_isIMax(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isMaxIMax(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Level_isMaxIMax___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Level_isMaxIMax(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isParam(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Level_isParam___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Level_isParam(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isMVar(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Level_isMVar___boxed(lean_object* x_1) {
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
x_3 = lean_unsigned_to_nat(176u);
x_4 = lean_unsigned_to_nat(21u);
x_5 = l_Lean_Level_mvarId_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvarId_x21(lean_object* x_1) {
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
x_3 = l_Lean_instInhabitedMVarId;
x_4 = l_Lean_Level_mvarId_x21___closed__3;
x_5 = lean_panic_fn(x_3, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvarId_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_mvarId_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isNeverZero(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Level_isNeverZero___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Level_isNeverZero(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ofNat(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Level_ofNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_ofNat(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_addOffsetAux(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Level_addOffset(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Level_addOffsetAux(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isExplicit(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Level_isExplicit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Level_isExplicit(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffsetAux(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Level_getOffsetAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Level_getOffsetAux(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffset(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Level_getOffsetAux(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getOffset___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_getOffset(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getLevelOffset(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Level_getLevelOffset___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_getLevelOffset(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_toNat(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Level_toNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_toNat(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_beq___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l_Lean_Level_occurs(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Level_occurs___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Level_ctorToNat(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Level_ctorToNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_ctorToNat(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_normLtAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Level_normLtAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT uint8_t l_Lean_Level_normLt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Level_normLtAux(x_1, x_3, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normLt___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_isAlreadyNormalizedCheap(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isAlreadyNormalizedCheap___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Level_0__Lean_Level_isAlreadyNormalizedCheap(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkIMaxAux(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_accMax(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Level_0__Lean_Level_mkMaxAux(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Level_0__Lean_Level_skipExplicit(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at_Lean_Level_normalize___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Array_qpartition_loop___at_Lean_Level_normalize___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Level_normalize___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_1; 
x_1 = lean_mk_string("unreachable code has been reached");
return x_1;
}
}
static lean_object* _init_l_Lean_Level_normalize___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Level_mkData___closed__2;
x_2 = l_Lean_Level_normalize___closed__1;
x_3 = lean_unsigned_to_nat(360u);
x_4 = lean_unsigned_to_nat(11u);
x_5 = l_Lean_Level_normalize___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Level_normalize___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normalize(lean_object* x_1) {
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
x_9 = l_Lean_Level_normalize___closed__4;
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
x_44 = l_Lean_Level_normalize___closed__3;
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
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at_Lean_Level_normalize___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at_Lean_Level_normalize___spec__1(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_qpartition_loop___at_Lean_Level_normalize___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qpartition_loop___at_Lean_Level_normalize___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Level_normalize___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at_Lean_Level_normalize___spec__2(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normalize___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_normalize(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isEquiv(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Level_isEquiv___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Level_dec(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Level_dec___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_dec(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_succ(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_max(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imax(lean_object* x_1, lean_object* x_2) {
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
x_1 = lean_mk_string("_uniq");
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
static lean_object* _init_l_Lean_Level_PP_toResult___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("?u");
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_toResult___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Level_PP_toResult___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_toResult(lean_object* x_1) {
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
x_19 = l_Lean_Level_PP_toResult___closed__3;
x_20 = l_Lean_Level_PP_toResult___closed__5;
x_21 = l_Lean_Name_replacePrefix(x_18, x_19, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(")");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(lean_object* x_1, uint8_t x_2) {
_start:
{
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_3 = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__4;
x_4 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
x_5 = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__6;
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__3;
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
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(lean_object* x_1) {
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
static lean_object* _init_l_Lean_Level_PP_Result_format___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("+");
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_format___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Level_PP_Result_format___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_format___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("max");
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
static lean_object* _init_l_Lean_Level_PP_Result_format___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("imax");
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_format___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Level_PP_Result_format___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_format(lean_object* x_1, uint8_t x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = 1;
x_5 = l_Lean_Name_toString(x_3, x_4);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Nat_repr(x_7);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_11, x_14);
lean_dec(x_11);
x_16 = 0;
x_17 = l_Lean_Level_PP_Result_format(x_10, x_16);
x_18 = l_Lean_Level_PP_Result_format___closed__2;
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_nat_add(x_15, x_14);
lean_dec(x_15);
x_21 = l_Nat_repr(x_20);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(x_23, x_2);
return x_24;
}
else
{
lean_dec(x_11);
x_1 = x_10;
goto _start;
}
}
case 3:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(x_26);
x_28 = l_Lean_Level_PP_Result_format___closed__4;
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = 0;
x_31 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_30);
x_32 = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(x_31, x_2);
return x_32;
}
default: 
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
lean_dec(x_1);
x_34 = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(x_33);
x_35 = l_Lean_Level_PP_Result_format___closed__6;
x_36 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = 0;
x_38 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_37);
x_39 = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(x_38, x_2);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_format___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Level_PP_Result_format(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Level_PP_Result_quote___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_SourceInfo_fromRef(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Level_PP_Result_quote___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_1 = lean_mk_string("Lean");
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Level_PP_Result_quote___lambda__3___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parser");
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Level_PP_Result_quote___lambda__3___closed__2;
x_2 = l_Lean_Level_PP_Result_quote___lambda__3___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___lambda__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Level");
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Level_PP_Result_quote___lambda__3___closed__4;
x_2 = l_Lean_Level_PP_Result_quote___lambda__3___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___lambda__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("addLit");
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Level_PP_Result_quote___lambda__3___closed__6;
x_2 = l_Lean_Level_PP_Result_quote___lambda__3___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___lambda__3___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_6 = lean_unsigned_to_nat(65u);
x_7 = l_Lean_Level_PP_Result_quote(x_1, x_6);
x_8 = l_Lean_Level_PP_Result_format___closed__1;
x_9 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_2, x_10);
x_12 = l_Nat_repr(x_11);
x_13 = l_Lean_numLitKind;
x_14 = lean_box(2);
x_15 = l_Lean_Syntax_mkLit(x_13, x_12, x_14);
x_16 = l_Lean_Level_PP_Result_quote___lambda__3___closed__9;
x_17 = lean_array_push(x_16, x_7);
x_18 = lean_array_push(x_17, x_9);
x_19 = lean_array_push(x_18, x_15);
x_20 = l_Lean_Level_PP_Result_quote___lambda__3___closed__8;
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
lean_object* x_1; 
x_1 = lean_mk_string("paren");
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Level_PP_Result_quote___lambda__3___closed__6;
x_2 = l_Lean_Level_PP_Result_quote___lambda__4___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1;
lean_inc(x_2);
x_6 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__5;
x_8 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_Level_PP_Result_quote___lambda__3___closed__9;
x_10 = lean_array_push(x_9, x_6);
x_11 = lean_array_push(x_10, x_1);
x_12 = lean_array_push(x_11, x_8);
x_13 = l_Lean_Level_PP_Result_quote___lambda__4___closed__2;
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
x_1 = l_Lean_Level_PP_Result_quote___lambda__3___closed__6;
x_2 = l_Lean_Level_PP_Result_format___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___lambda__5___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("null");
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___lambda__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Level_PP_Result_quote___lambda__5___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___lambda__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_5 = l_Lean_Level_PP_Result_format___closed__3;
x_6 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_List_redLength___rarg(x_1);
x_8 = lean_mk_empty_array_with_capacity(x_7);
lean_dec(x_7);
x_9 = l_List_toArrayAux___rarg(x_1, x_8);
x_10 = lean_array_get_size(x_9);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_12 = 0;
x_13 = x_9;
x_14 = l_Array_mapMUnsafe_map___at_Lean_Level_PP_Result_quote___spec__2(x_11, x_12, x_13);
x_15 = x_14;
x_16 = l_Lean_Level_normalize___closed__4;
x_17 = l_Array_append___rarg(x_16, x_15);
x_18 = l_Lean_Level_PP_Result_quote___lambda__5___closed__3;
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_Level_PP_Result_quote___lambda__5___closed__4;
x_21 = lean_array_push(x_20, x_6);
x_22 = lean_array_push(x_21, x_19);
x_23 = l_Lean_Level_PP_Result_quote___lambda__5___closed__1;
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_4);
return x_25;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___lambda__6___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Level_PP_Result_quote___lambda__3___closed__6;
x_2 = l_Lean_Level_PP_Result_format___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_5 = l_Lean_Level_PP_Result_format___closed__5;
x_6 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_List_redLength___rarg(x_1);
x_8 = lean_mk_empty_array_with_capacity(x_7);
lean_dec(x_7);
x_9 = l_List_toArrayAux___rarg(x_1, x_8);
x_10 = lean_array_get_size(x_9);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_12 = 0;
x_13 = x_9;
x_14 = l_Array_mapMUnsafe_map___at_Lean_Level_PP_Result_quote___spec__2(x_11, x_12, x_13);
x_15 = x_14;
x_16 = l_Lean_Level_normalize___closed__4;
x_17 = l_Array_append___rarg(x_16, x_15);
x_18 = l_Lean_Level_PP_Result_quote___lambda__5___closed__3;
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_Level_PP_Result_quote___lambda__5___closed__4;
x_21 = lean_array_push(x_20, x_6);
x_22 = lean_array_push(x_21, x_19);
x_23 = l_Lean_Level_PP_Result_quote___lambda__6___closed__1;
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_4);
return x_25;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Level_PP_Result_quote___spec__1), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Level_PP_Result_quote___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Level_PP_Result_quote___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Level_PP_Result_quote___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Level_PP_Result_quote___lambda__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Level_PP_Result_quote___lambda__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Level_PP_Result_quote___lambda__5(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Level_PP_Result_quote___lambda__6(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Level_PP_Result_quote(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_format(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = l_Lean_Level_PP_toResult(x_1);
x_3 = 1;
x_4 = l_Lean_Level_PP_Result_format(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToFormatLevel(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_format(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToStringLevel(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Level_format(x_1);
x_3 = l_Std_Format_defWidth;
x_4 = lean_format_pretty(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_quote(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Level_PP_toResult(x_1);
x_4 = l_Lean_Level_PP_Result_quote(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_quote___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Level_quote(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instQuoteLevel(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Level_quote(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_level_mk_max_simp(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* lean_level_mk_imax_simp(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Level_updateSucc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_3 = lean_unsigned_to_nat(506u);
x_4 = lean_unsigned_to_nat(18u);
x_5 = l_Lean_Level_updateSucc_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_updateSucc_x21(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Level_updateMax___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_3 = lean_unsigned_to_nat(515u);
x_4 = lean_unsigned_to_nat(21u);
x_5 = l_Lean_Level_updateMax_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_updateMax_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Level_updateIMax___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_3 = lean_unsigned_to_nat(524u);
x_4 = lean_unsigned_to_nat(22u);
x_5 = l_Lean_Level_updateIMax_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_updateIMax_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Level_mkNaryMax(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Level_collectMVars___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = 0;
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = l_Lean_Name_quickCmp(x_2, x_10);
switch (x_13) {
case 0:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Std_RBNode_ins___at_Lean_Level_collectMVars___spec__2(x_9, x_2, x_3);
x_15 = 0;
lean_ctor_set(x_1, 0, x_14);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_15);
return x_1;
}
case 1:
{
uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_16);
return x_1;
}
default: 
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Std_RBNode_ins___at_Lean_Level_collectMVars___spec__2(x_12, x_2, x_3);
x_18 = 0;
lean_ctor_set(x_1, 3, x_17);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_18);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_ctor_get(x_1, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_23 = l_Lean_Name_quickCmp(x_2, x_20);
switch (x_23) {
case 0:
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = l_Std_RBNode_ins___at_Lean_Level_collectMVars___spec__2(x_19, x_2, x_3);
x_25 = 0;
x_26 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set(x_26, 3, x_22);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_25);
return x_26;
}
case 1:
{
uint8_t x_27; lean_object* x_28; 
lean_dec(x_21);
lean_dec(x_20);
x_27 = 0;
x_28 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_28, 2, x_3);
lean_ctor_set(x_28, 3, x_22);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_27);
return x_28;
}
default: 
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = l_Std_RBNode_ins___at_Lean_Level_collectMVars___spec__2(x_22, x_2, x_3);
x_30 = 0;
x_31 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_20);
lean_ctor_set(x_31, 2, x_21);
lean_ctor_set(x_31, 3, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_30);
return x_31;
}
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_1, 0);
x_34 = lean_ctor_get(x_1, 1);
x_35 = lean_ctor_get(x_1, 2);
x_36 = lean_ctor_get(x_1, 3);
x_37 = l_Lean_Name_quickCmp(x_2, x_34);
switch (x_37) {
case 0:
{
uint8_t x_38; 
x_38 = l_Std_RBNode_isRed___rarg(x_33);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Std_RBNode_ins___at_Lean_Level_collectMVars___spec__2(x_33, x_2, x_3);
x_40 = 1;
lean_ctor_set(x_1, 0, x_39);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_40);
return x_1;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Std_RBNode_ins___at_Lean_Level_collectMVars___spec__2(x_33, x_2, x_3);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 3);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_41, 3);
lean_dec(x_45);
x_46 = lean_ctor_get(x_41, 0);
lean_dec(x_46);
x_47 = 0;
lean_ctor_set(x_41, 0, x_43);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_47);
x_48 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_48);
return x_1;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_41, 1);
x_50 = lean_ctor_get(x_41, 2);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_41);
x_51 = 0;
x_52 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_52, 0, x_43);
lean_ctor_set(x_52, 1, x_49);
lean_ctor_set(x_52, 2, x_50);
lean_ctor_set(x_52, 3, x_43);
lean_ctor_set_uint8(x_52, sizeof(void*)*4, x_51);
x_53 = 1;
lean_ctor_set(x_1, 0, x_52);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_53);
return x_1;
}
}
else
{
uint8_t x_54; 
x_54 = lean_ctor_get_uint8(x_43, sizeof(void*)*4);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_41);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_41, 1);
x_57 = lean_ctor_get(x_41, 2);
x_58 = lean_ctor_get(x_41, 3);
lean_dec(x_58);
x_59 = lean_ctor_get(x_41, 0);
lean_dec(x_59);
x_60 = !lean_is_exclusive(x_43);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_43, 0);
x_62 = lean_ctor_get(x_43, 1);
x_63 = lean_ctor_get(x_43, 2);
x_64 = lean_ctor_get(x_43, 3);
x_65 = 1;
lean_ctor_set(x_43, 3, x_61);
lean_ctor_set(x_43, 2, x_57);
lean_ctor_set(x_43, 1, x_56);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_65);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_64);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_65);
x_66 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_63);
lean_ctor_set(x_1, 1, x_62);
lean_ctor_set(x_1, 0, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_66);
return x_1;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; uint8_t x_73; 
x_67 = lean_ctor_get(x_43, 0);
x_68 = lean_ctor_get(x_43, 1);
x_69 = lean_ctor_get(x_43, 2);
x_70 = lean_ctor_get(x_43, 3);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_43);
x_71 = 1;
x_72 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_72, 0, x_42);
lean_ctor_set(x_72, 1, x_56);
lean_ctor_set(x_72, 2, x_57);
lean_ctor_set(x_72, 3, x_67);
lean_ctor_set_uint8(x_72, sizeof(void*)*4, x_71);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_70);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_71);
x_73 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_69);
lean_ctor_set(x_1, 1, x_68);
lean_ctor_set(x_1, 0, x_72);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_73);
return x_1;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_74 = lean_ctor_get(x_41, 1);
x_75 = lean_ctor_get(x_41, 2);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_41);
x_76 = lean_ctor_get(x_43, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_43, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_43, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_43, 3);
lean_inc(x_79);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 x_80 = x_43;
} else {
 lean_dec_ref(x_43);
 x_80 = lean_box(0);
}
x_81 = 1;
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(1, 4, 1);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_42);
lean_ctor_set(x_82, 1, x_74);
lean_ctor_set(x_82, 2, x_75);
lean_ctor_set(x_82, 3, x_76);
lean_ctor_set_uint8(x_82, sizeof(void*)*4, x_81);
x_83 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_34);
lean_ctor_set(x_83, 2, x_35);
lean_ctor_set(x_83, 3, x_36);
lean_ctor_set_uint8(x_83, sizeof(void*)*4, x_81);
x_84 = 0;
lean_ctor_set(x_1, 3, x_83);
lean_ctor_set(x_1, 2, x_78);
lean_ctor_set(x_1, 1, x_77);
lean_ctor_set(x_1, 0, x_82);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_84);
return x_1;
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_41);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_41, 3);
lean_dec(x_86);
x_87 = lean_ctor_get(x_41, 0);
lean_dec(x_87);
x_88 = 0;
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_88);
x_89 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_89);
return x_1;
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; uint8_t x_94; 
x_90 = lean_ctor_get(x_41, 1);
x_91 = lean_ctor_get(x_41, 2);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_41);
x_92 = 0;
x_93 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_93, 0, x_42);
lean_ctor_set(x_93, 1, x_90);
lean_ctor_set(x_93, 2, x_91);
lean_ctor_set(x_93, 3, x_43);
lean_ctor_set_uint8(x_93, sizeof(void*)*4, x_92);
x_94 = 1;
lean_ctor_set(x_1, 0, x_93);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_94);
return x_1;
}
}
}
}
else
{
uint8_t x_95; 
x_95 = lean_ctor_get_uint8(x_42, sizeof(void*)*4);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_41);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_97 = lean_ctor_get(x_41, 1);
x_98 = lean_ctor_get(x_41, 2);
x_99 = lean_ctor_get(x_41, 3);
x_100 = lean_ctor_get(x_41, 0);
lean_dec(x_100);
x_101 = !lean_is_exclusive(x_42);
if (x_101 == 0)
{
uint8_t x_102; uint8_t x_103; 
x_102 = 1;
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_102);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_99);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_102);
x_103 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_98);
lean_ctor_set(x_1, 1, x_97);
lean_ctor_set(x_1, 0, x_42);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_103);
return x_1;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; uint8_t x_110; 
x_104 = lean_ctor_get(x_42, 0);
x_105 = lean_ctor_get(x_42, 1);
x_106 = lean_ctor_get(x_42, 2);
x_107 = lean_ctor_get(x_42, 3);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_42);
x_108 = 1;
x_109 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_109, 0, x_104);
lean_ctor_set(x_109, 1, x_105);
lean_ctor_set(x_109, 2, x_106);
lean_ctor_set(x_109, 3, x_107);
lean_ctor_set_uint8(x_109, sizeof(void*)*4, x_108);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_99);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_108);
x_110 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_98);
lean_ctor_set(x_1, 1, x_97);
lean_ctor_set(x_1, 0, x_109);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_110);
return x_1;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_111 = lean_ctor_get(x_41, 1);
x_112 = lean_ctor_get(x_41, 2);
x_113 = lean_ctor_get(x_41, 3);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_41);
x_114 = lean_ctor_get(x_42, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_42, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_42, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_42, 3);
lean_inc(x_117);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_118 = x_42;
} else {
 lean_dec_ref(x_42);
 x_118 = lean_box(0);
}
x_119 = 1;
if (lean_is_scalar(x_118)) {
 x_120 = lean_alloc_ctor(1, 4, 1);
} else {
 x_120 = x_118;
}
lean_ctor_set(x_120, 0, x_114);
lean_ctor_set(x_120, 1, x_115);
lean_ctor_set(x_120, 2, x_116);
lean_ctor_set(x_120, 3, x_117);
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_119);
x_121 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_121, 0, x_113);
lean_ctor_set(x_121, 1, x_34);
lean_ctor_set(x_121, 2, x_35);
lean_ctor_set(x_121, 3, x_36);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_119);
x_122 = 0;
lean_ctor_set(x_1, 3, x_121);
lean_ctor_set(x_1, 2, x_112);
lean_ctor_set(x_1, 1, x_111);
lean_ctor_set(x_1, 0, x_120);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_122);
return x_1;
}
}
else
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_41, 3);
lean_inc(x_123);
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_41);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_128; 
x_125 = lean_ctor_get(x_41, 3);
lean_dec(x_125);
x_126 = lean_ctor_get(x_41, 0);
lean_dec(x_126);
x_127 = 0;
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_127);
x_128 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_128);
return x_1;
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; uint8_t x_133; 
x_129 = lean_ctor_get(x_41, 1);
x_130 = lean_ctor_get(x_41, 2);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_41);
x_131 = 0;
x_132 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_132, 0, x_42);
lean_ctor_set(x_132, 1, x_129);
lean_ctor_set(x_132, 2, x_130);
lean_ctor_set(x_132, 3, x_123);
lean_ctor_set_uint8(x_132, sizeof(void*)*4, x_131);
x_133 = 1;
lean_ctor_set(x_1, 0, x_132);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_133);
return x_1;
}
}
else
{
uint8_t x_134; 
x_134 = lean_ctor_get_uint8(x_123, sizeof(void*)*4);
if (x_134 == 0)
{
uint8_t x_135; 
lean_free_object(x_1);
x_135 = !lean_is_exclusive(x_41);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_136 = lean_ctor_get(x_41, 1);
x_137 = lean_ctor_get(x_41, 2);
x_138 = lean_ctor_get(x_41, 3);
lean_dec(x_138);
x_139 = lean_ctor_get(x_41, 0);
lean_dec(x_139);
x_140 = !lean_is_exclusive(x_123);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; uint8_t x_146; 
x_141 = lean_ctor_get(x_123, 0);
x_142 = lean_ctor_get(x_123, 1);
x_143 = lean_ctor_get(x_123, 2);
x_144 = lean_ctor_get(x_123, 3);
x_145 = 1;
lean_inc(x_42);
lean_ctor_set(x_123, 3, x_141);
lean_ctor_set(x_123, 2, x_137);
lean_ctor_set(x_123, 1, x_136);
lean_ctor_set(x_123, 0, x_42);
x_146 = !lean_is_exclusive(x_42);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_147 = lean_ctor_get(x_42, 3);
lean_dec(x_147);
x_148 = lean_ctor_get(x_42, 2);
lean_dec(x_148);
x_149 = lean_ctor_get(x_42, 1);
lean_dec(x_149);
x_150 = lean_ctor_get(x_42, 0);
lean_dec(x_150);
lean_ctor_set_uint8(x_123, sizeof(void*)*4, x_145);
lean_ctor_set(x_42, 3, x_36);
lean_ctor_set(x_42, 2, x_35);
lean_ctor_set(x_42, 1, x_34);
lean_ctor_set(x_42, 0, x_144);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_145);
x_151 = 0;
lean_ctor_set(x_41, 3, x_42);
lean_ctor_set(x_41, 2, x_143);
lean_ctor_set(x_41, 1, x_142);
lean_ctor_set(x_41, 0, x_123);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_151);
return x_41;
}
else
{
lean_object* x_152; uint8_t x_153; 
lean_dec(x_42);
lean_ctor_set_uint8(x_123, sizeof(void*)*4, x_145);
x_152 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_152, 0, x_144);
lean_ctor_set(x_152, 1, x_34);
lean_ctor_set(x_152, 2, x_35);
lean_ctor_set(x_152, 3, x_36);
lean_ctor_set_uint8(x_152, sizeof(void*)*4, x_145);
x_153 = 0;
lean_ctor_set(x_41, 3, x_152);
lean_ctor_set(x_41, 2, x_143);
lean_ctor_set(x_41, 1, x_142);
lean_ctor_set(x_41, 0, x_123);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_153);
return x_41;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_154 = lean_ctor_get(x_123, 0);
x_155 = lean_ctor_get(x_123, 1);
x_156 = lean_ctor_get(x_123, 2);
x_157 = lean_ctor_get(x_123, 3);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_123);
x_158 = 1;
lean_inc(x_42);
x_159 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_159, 0, x_42);
lean_ctor_set(x_159, 1, x_136);
lean_ctor_set(x_159, 2, x_137);
lean_ctor_set(x_159, 3, x_154);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_160 = x_42;
} else {
 lean_dec_ref(x_42);
 x_160 = lean_box(0);
}
lean_ctor_set_uint8(x_159, sizeof(void*)*4, x_158);
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 4, 1);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_157);
lean_ctor_set(x_161, 1, x_34);
lean_ctor_set(x_161, 2, x_35);
lean_ctor_set(x_161, 3, x_36);
lean_ctor_set_uint8(x_161, sizeof(void*)*4, x_158);
x_162 = 0;
lean_ctor_set(x_41, 3, x_161);
lean_ctor_set(x_41, 2, x_156);
lean_ctor_set(x_41, 1, x_155);
lean_ctor_set(x_41, 0, x_159);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_162);
return x_41;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; 
x_163 = lean_ctor_get(x_41, 1);
x_164 = lean_ctor_get(x_41, 2);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_41);
x_165 = lean_ctor_get(x_123, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_123, 1);
lean_inc(x_166);
x_167 = lean_ctor_get(x_123, 2);
lean_inc(x_167);
x_168 = lean_ctor_get(x_123, 3);
lean_inc(x_168);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 lean_ctor_release(x_123, 3);
 x_169 = x_123;
} else {
 lean_dec_ref(x_123);
 x_169 = lean_box(0);
}
x_170 = 1;
lean_inc(x_42);
if (lean_is_scalar(x_169)) {
 x_171 = lean_alloc_ctor(1, 4, 1);
} else {
 x_171 = x_169;
}
lean_ctor_set(x_171, 0, x_42);
lean_ctor_set(x_171, 1, x_163);
lean_ctor_set(x_171, 2, x_164);
lean_ctor_set(x_171, 3, x_165);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_172 = x_42;
} else {
 lean_dec_ref(x_42);
 x_172 = lean_box(0);
}
lean_ctor_set_uint8(x_171, sizeof(void*)*4, x_170);
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 4, 1);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_168);
lean_ctor_set(x_173, 1, x_34);
lean_ctor_set(x_173, 2, x_35);
lean_ctor_set(x_173, 3, x_36);
lean_ctor_set_uint8(x_173, sizeof(void*)*4, x_170);
x_174 = 0;
x_175 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_175, 0, x_171);
lean_ctor_set(x_175, 1, x_166);
lean_ctor_set(x_175, 2, x_167);
lean_ctor_set(x_175, 3, x_173);
lean_ctor_set_uint8(x_175, sizeof(void*)*4, x_174);
return x_175;
}
}
else
{
uint8_t x_176; 
x_176 = !lean_is_exclusive(x_41);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_177 = lean_ctor_get(x_41, 3);
lean_dec(x_177);
x_178 = lean_ctor_get(x_41, 0);
lean_dec(x_178);
x_179 = !lean_is_exclusive(x_42);
if (x_179 == 0)
{
uint8_t x_180; uint8_t x_181; 
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_134);
x_180 = 0;
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_180);
x_181 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_181);
return x_1;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; uint8_t x_188; 
x_182 = lean_ctor_get(x_42, 0);
x_183 = lean_ctor_get(x_42, 1);
x_184 = lean_ctor_get(x_42, 2);
x_185 = lean_ctor_get(x_42, 3);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_42);
x_186 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_186, 0, x_182);
lean_ctor_set(x_186, 1, x_183);
lean_ctor_set(x_186, 2, x_184);
lean_ctor_set(x_186, 3, x_185);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_134);
x_187 = 0;
lean_ctor_set(x_41, 0, x_186);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_187);
x_188 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; uint8_t x_199; 
x_189 = lean_ctor_get(x_41, 1);
x_190 = lean_ctor_get(x_41, 2);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_41);
x_191 = lean_ctor_get(x_42, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_42, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_42, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_42, 3);
lean_inc(x_194);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_195 = x_42;
} else {
 lean_dec_ref(x_42);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 4, 1);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_191);
lean_ctor_set(x_196, 1, x_192);
lean_ctor_set(x_196, 2, x_193);
lean_ctor_set(x_196, 3, x_194);
lean_ctor_set_uint8(x_196, sizeof(void*)*4, x_134);
x_197 = 0;
x_198 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_189);
lean_ctor_set(x_198, 2, x_190);
lean_ctor_set(x_198, 3, x_123);
lean_ctor_set_uint8(x_198, sizeof(void*)*4, x_197);
x_199 = 1;
lean_ctor_set(x_1, 0, x_198);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
}
}
}
}
}
case 1:
{
uint8_t x_200; 
lean_dec(x_35);
lean_dec(x_34);
x_200 = 1;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_200);
return x_1;
}
default: 
{
uint8_t x_201; 
x_201 = l_Std_RBNode_isRed___rarg(x_36);
if (x_201 == 0)
{
lean_object* x_202; uint8_t x_203; 
x_202 = l_Std_RBNode_ins___at_Lean_Level_collectMVars___spec__2(x_36, x_2, x_3);
x_203 = 1;
lean_ctor_set(x_1, 3, x_202);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_203);
return x_1;
}
else
{
lean_object* x_204; lean_object* x_205; 
x_204 = l_Std_RBNode_ins___at_Lean_Level_collectMVars___spec__2(x_36, x_2, x_3);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_204, 3);
lean_inc(x_206);
if (lean_obj_tag(x_206) == 0)
{
uint8_t x_207; 
x_207 = !lean_is_exclusive(x_204);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; uint8_t x_211; 
x_208 = lean_ctor_get(x_204, 3);
lean_dec(x_208);
x_209 = lean_ctor_get(x_204, 0);
lean_dec(x_209);
x_210 = 0;
lean_ctor_set(x_204, 0, x_206);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_210);
x_211 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_211);
return x_1;
}
else
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; uint8_t x_216; 
x_212 = lean_ctor_get(x_204, 1);
x_213 = lean_ctor_get(x_204, 2);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_204);
x_214 = 0;
x_215 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_215, 0, x_206);
lean_ctor_set(x_215, 1, x_212);
lean_ctor_set(x_215, 2, x_213);
lean_ctor_set(x_215, 3, x_206);
lean_ctor_set_uint8(x_215, sizeof(void*)*4, x_214);
x_216 = 1;
lean_ctor_set(x_1, 3, x_215);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_216);
return x_1;
}
}
else
{
uint8_t x_217; 
x_217 = lean_ctor_get_uint8(x_206, sizeof(void*)*4);
if (x_217 == 0)
{
uint8_t x_218; 
x_218 = !lean_is_exclusive(x_204);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_219 = lean_ctor_get(x_204, 1);
x_220 = lean_ctor_get(x_204, 2);
x_221 = lean_ctor_get(x_204, 3);
lean_dec(x_221);
x_222 = lean_ctor_get(x_204, 0);
lean_dec(x_222);
x_223 = !lean_is_exclusive(x_206);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; uint8_t x_229; 
x_224 = lean_ctor_get(x_206, 0);
x_225 = lean_ctor_get(x_206, 1);
x_226 = lean_ctor_get(x_206, 2);
x_227 = lean_ctor_get(x_206, 3);
x_228 = 1;
lean_ctor_set(x_206, 3, x_205);
lean_ctor_set(x_206, 2, x_35);
lean_ctor_set(x_206, 1, x_34);
lean_ctor_set(x_206, 0, x_33);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_228);
lean_ctor_set(x_204, 3, x_227);
lean_ctor_set(x_204, 2, x_226);
lean_ctor_set(x_204, 1, x_225);
lean_ctor_set(x_204, 0, x_224);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_228);
x_229 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_220);
lean_ctor_set(x_1, 1, x_219);
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_229);
return x_1;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; uint8_t x_236; 
x_230 = lean_ctor_get(x_206, 0);
x_231 = lean_ctor_get(x_206, 1);
x_232 = lean_ctor_get(x_206, 2);
x_233 = lean_ctor_get(x_206, 3);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_206);
x_234 = 1;
x_235 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_235, 0, x_33);
lean_ctor_set(x_235, 1, x_34);
lean_ctor_set(x_235, 2, x_35);
lean_ctor_set(x_235, 3, x_205);
lean_ctor_set_uint8(x_235, sizeof(void*)*4, x_234);
lean_ctor_set(x_204, 3, x_233);
lean_ctor_set(x_204, 2, x_232);
lean_ctor_set(x_204, 1, x_231);
lean_ctor_set(x_204, 0, x_230);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_234);
x_236 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_220);
lean_ctor_set(x_1, 1, x_219);
lean_ctor_set(x_1, 0, x_235);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_236);
return x_1;
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_237 = lean_ctor_get(x_204, 1);
x_238 = lean_ctor_get(x_204, 2);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_204);
x_239 = lean_ctor_get(x_206, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_206, 1);
lean_inc(x_240);
x_241 = lean_ctor_get(x_206, 2);
lean_inc(x_241);
x_242 = lean_ctor_get(x_206, 3);
lean_inc(x_242);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 lean_ctor_release(x_206, 2);
 lean_ctor_release(x_206, 3);
 x_243 = x_206;
} else {
 lean_dec_ref(x_206);
 x_243 = lean_box(0);
}
x_244 = 1;
if (lean_is_scalar(x_243)) {
 x_245 = lean_alloc_ctor(1, 4, 1);
} else {
 x_245 = x_243;
}
lean_ctor_set(x_245, 0, x_33);
lean_ctor_set(x_245, 1, x_34);
lean_ctor_set(x_245, 2, x_35);
lean_ctor_set(x_245, 3, x_205);
lean_ctor_set_uint8(x_245, sizeof(void*)*4, x_244);
x_246 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_246, 0, x_239);
lean_ctor_set(x_246, 1, x_240);
lean_ctor_set(x_246, 2, x_241);
lean_ctor_set(x_246, 3, x_242);
lean_ctor_set_uint8(x_246, sizeof(void*)*4, x_244);
x_247 = 0;
lean_ctor_set(x_1, 3, x_246);
lean_ctor_set(x_1, 2, x_238);
lean_ctor_set(x_1, 1, x_237);
lean_ctor_set(x_1, 0, x_245);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_247);
return x_1;
}
}
else
{
uint8_t x_248; 
x_248 = !lean_is_exclusive(x_204);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; uint8_t x_251; uint8_t x_252; 
x_249 = lean_ctor_get(x_204, 3);
lean_dec(x_249);
x_250 = lean_ctor_get(x_204, 0);
lean_dec(x_250);
x_251 = 0;
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_251);
x_252 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_252);
return x_1;
}
else
{
lean_object* x_253; lean_object* x_254; uint8_t x_255; lean_object* x_256; uint8_t x_257; 
x_253 = lean_ctor_get(x_204, 1);
x_254 = lean_ctor_get(x_204, 2);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_204);
x_255 = 0;
x_256 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_256, 0, x_205);
lean_ctor_set(x_256, 1, x_253);
lean_ctor_set(x_256, 2, x_254);
lean_ctor_set(x_256, 3, x_206);
lean_ctor_set_uint8(x_256, sizeof(void*)*4, x_255);
x_257 = 1;
lean_ctor_set(x_1, 3, x_256);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_257);
return x_1;
}
}
}
}
else
{
uint8_t x_258; 
x_258 = lean_ctor_get_uint8(x_205, sizeof(void*)*4);
if (x_258 == 0)
{
uint8_t x_259; 
x_259 = !lean_is_exclusive(x_204);
if (x_259 == 0)
{
lean_object* x_260; uint8_t x_261; 
x_260 = lean_ctor_get(x_204, 0);
lean_dec(x_260);
x_261 = !lean_is_exclusive(x_205);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; uint8_t x_267; 
x_262 = lean_ctor_get(x_205, 0);
x_263 = lean_ctor_get(x_205, 1);
x_264 = lean_ctor_get(x_205, 2);
x_265 = lean_ctor_get(x_205, 3);
x_266 = 1;
lean_ctor_set(x_205, 3, x_262);
lean_ctor_set(x_205, 2, x_35);
lean_ctor_set(x_205, 1, x_34);
lean_ctor_set(x_205, 0, x_33);
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_266);
lean_ctor_set(x_204, 0, x_265);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_266);
x_267 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_264);
lean_ctor_set(x_1, 1, x_263);
lean_ctor_set(x_1, 0, x_205);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_267);
return x_1;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; lean_object* x_273; uint8_t x_274; 
x_268 = lean_ctor_get(x_205, 0);
x_269 = lean_ctor_get(x_205, 1);
x_270 = lean_ctor_get(x_205, 2);
x_271 = lean_ctor_get(x_205, 3);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_205);
x_272 = 1;
x_273 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_273, 0, x_33);
lean_ctor_set(x_273, 1, x_34);
lean_ctor_set(x_273, 2, x_35);
lean_ctor_set(x_273, 3, x_268);
lean_ctor_set_uint8(x_273, sizeof(void*)*4, x_272);
lean_ctor_set(x_204, 0, x_271);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_272);
x_274 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_270);
lean_ctor_set(x_1, 1, x_269);
lean_ctor_set(x_1, 0, x_273);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_274);
return x_1;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_275 = lean_ctor_get(x_204, 1);
x_276 = lean_ctor_get(x_204, 2);
x_277 = lean_ctor_get(x_204, 3);
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_275);
lean_dec(x_204);
x_278 = lean_ctor_get(x_205, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_205, 1);
lean_inc(x_279);
x_280 = lean_ctor_get(x_205, 2);
lean_inc(x_280);
x_281 = lean_ctor_get(x_205, 3);
lean_inc(x_281);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_282 = x_205;
} else {
 lean_dec_ref(x_205);
 x_282 = lean_box(0);
}
x_283 = 1;
if (lean_is_scalar(x_282)) {
 x_284 = lean_alloc_ctor(1, 4, 1);
} else {
 x_284 = x_282;
}
lean_ctor_set(x_284, 0, x_33);
lean_ctor_set(x_284, 1, x_34);
lean_ctor_set(x_284, 2, x_35);
lean_ctor_set(x_284, 3, x_278);
lean_ctor_set_uint8(x_284, sizeof(void*)*4, x_283);
x_285 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_285, 0, x_281);
lean_ctor_set(x_285, 1, x_275);
lean_ctor_set(x_285, 2, x_276);
lean_ctor_set(x_285, 3, x_277);
lean_ctor_set_uint8(x_285, sizeof(void*)*4, x_283);
x_286 = 0;
lean_ctor_set(x_1, 3, x_285);
lean_ctor_set(x_1, 2, x_280);
lean_ctor_set(x_1, 1, x_279);
lean_ctor_set(x_1, 0, x_284);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_286);
return x_1;
}
}
else
{
lean_object* x_287; 
x_287 = lean_ctor_get(x_204, 3);
lean_inc(x_287);
if (lean_obj_tag(x_287) == 0)
{
uint8_t x_288; 
x_288 = !lean_is_exclusive(x_204);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; uint8_t x_291; uint8_t x_292; 
x_289 = lean_ctor_get(x_204, 3);
lean_dec(x_289);
x_290 = lean_ctor_get(x_204, 0);
lean_dec(x_290);
x_291 = 0;
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_291);
x_292 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_292);
return x_1;
}
else
{
lean_object* x_293; lean_object* x_294; uint8_t x_295; lean_object* x_296; uint8_t x_297; 
x_293 = lean_ctor_get(x_204, 1);
x_294 = lean_ctor_get(x_204, 2);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_204);
x_295 = 0;
x_296 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_296, 0, x_205);
lean_ctor_set(x_296, 1, x_293);
lean_ctor_set(x_296, 2, x_294);
lean_ctor_set(x_296, 3, x_287);
lean_ctor_set_uint8(x_296, sizeof(void*)*4, x_295);
x_297 = 1;
lean_ctor_set(x_1, 3, x_296);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_297);
return x_1;
}
}
else
{
uint8_t x_298; 
x_298 = lean_ctor_get_uint8(x_287, sizeof(void*)*4);
if (x_298 == 0)
{
uint8_t x_299; 
lean_free_object(x_1);
x_299 = !lean_is_exclusive(x_204);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; uint8_t x_302; 
x_300 = lean_ctor_get(x_204, 3);
lean_dec(x_300);
x_301 = lean_ctor_get(x_204, 0);
lean_dec(x_301);
x_302 = !lean_is_exclusive(x_287);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; uint8_t x_308; 
x_303 = lean_ctor_get(x_287, 0);
x_304 = lean_ctor_get(x_287, 1);
x_305 = lean_ctor_get(x_287, 2);
x_306 = lean_ctor_get(x_287, 3);
x_307 = 1;
lean_inc(x_205);
lean_ctor_set(x_287, 3, x_205);
lean_ctor_set(x_287, 2, x_35);
lean_ctor_set(x_287, 1, x_34);
lean_ctor_set(x_287, 0, x_33);
x_308 = !lean_is_exclusive(x_205);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; 
x_309 = lean_ctor_get(x_205, 3);
lean_dec(x_309);
x_310 = lean_ctor_get(x_205, 2);
lean_dec(x_310);
x_311 = lean_ctor_get(x_205, 1);
lean_dec(x_311);
x_312 = lean_ctor_get(x_205, 0);
lean_dec(x_312);
lean_ctor_set_uint8(x_287, sizeof(void*)*4, x_307);
lean_ctor_set(x_205, 3, x_306);
lean_ctor_set(x_205, 2, x_305);
lean_ctor_set(x_205, 1, x_304);
lean_ctor_set(x_205, 0, x_303);
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_307);
x_313 = 0;
lean_ctor_set(x_204, 3, x_205);
lean_ctor_set(x_204, 0, x_287);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_313);
return x_204;
}
else
{
lean_object* x_314; uint8_t x_315; 
lean_dec(x_205);
lean_ctor_set_uint8(x_287, sizeof(void*)*4, x_307);
x_314 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_314, 0, x_303);
lean_ctor_set(x_314, 1, x_304);
lean_ctor_set(x_314, 2, x_305);
lean_ctor_set(x_314, 3, x_306);
lean_ctor_set_uint8(x_314, sizeof(void*)*4, x_307);
x_315 = 0;
lean_ctor_set(x_204, 3, x_314);
lean_ctor_set(x_204, 0, x_287);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_315);
return x_204;
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
x_316 = lean_ctor_get(x_287, 0);
x_317 = lean_ctor_get(x_287, 1);
x_318 = lean_ctor_get(x_287, 2);
x_319 = lean_ctor_get(x_287, 3);
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_287);
x_320 = 1;
lean_inc(x_205);
x_321 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_321, 0, x_33);
lean_ctor_set(x_321, 1, x_34);
lean_ctor_set(x_321, 2, x_35);
lean_ctor_set(x_321, 3, x_205);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_322 = x_205;
} else {
 lean_dec_ref(x_205);
 x_322 = lean_box(0);
}
lean_ctor_set_uint8(x_321, sizeof(void*)*4, x_320);
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(1, 4, 1);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_316);
lean_ctor_set(x_323, 1, x_317);
lean_ctor_set(x_323, 2, x_318);
lean_ctor_set(x_323, 3, x_319);
lean_ctor_set_uint8(x_323, sizeof(void*)*4, x_320);
x_324 = 0;
lean_ctor_set(x_204, 3, x_323);
lean_ctor_set(x_204, 0, x_321);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_324);
return x_204;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; lean_object* x_337; 
x_325 = lean_ctor_get(x_204, 1);
x_326 = lean_ctor_get(x_204, 2);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_204);
x_327 = lean_ctor_get(x_287, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_287, 1);
lean_inc(x_328);
x_329 = lean_ctor_get(x_287, 2);
lean_inc(x_329);
x_330 = lean_ctor_get(x_287, 3);
lean_inc(x_330);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 lean_ctor_release(x_287, 2);
 lean_ctor_release(x_287, 3);
 x_331 = x_287;
} else {
 lean_dec_ref(x_287);
 x_331 = lean_box(0);
}
x_332 = 1;
lean_inc(x_205);
if (lean_is_scalar(x_331)) {
 x_333 = lean_alloc_ctor(1, 4, 1);
} else {
 x_333 = x_331;
}
lean_ctor_set(x_333, 0, x_33);
lean_ctor_set(x_333, 1, x_34);
lean_ctor_set(x_333, 2, x_35);
lean_ctor_set(x_333, 3, x_205);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_334 = x_205;
} else {
 lean_dec_ref(x_205);
 x_334 = lean_box(0);
}
lean_ctor_set_uint8(x_333, sizeof(void*)*4, x_332);
if (lean_is_scalar(x_334)) {
 x_335 = lean_alloc_ctor(1, 4, 1);
} else {
 x_335 = x_334;
}
lean_ctor_set(x_335, 0, x_327);
lean_ctor_set(x_335, 1, x_328);
lean_ctor_set(x_335, 2, x_329);
lean_ctor_set(x_335, 3, x_330);
lean_ctor_set_uint8(x_335, sizeof(void*)*4, x_332);
x_336 = 0;
x_337 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_337, 0, x_333);
lean_ctor_set(x_337, 1, x_325);
lean_ctor_set(x_337, 2, x_326);
lean_ctor_set(x_337, 3, x_335);
lean_ctor_set_uint8(x_337, sizeof(void*)*4, x_336);
return x_337;
}
}
else
{
uint8_t x_338; 
x_338 = !lean_is_exclusive(x_204);
if (x_338 == 0)
{
lean_object* x_339; lean_object* x_340; uint8_t x_341; 
x_339 = lean_ctor_get(x_204, 3);
lean_dec(x_339);
x_340 = lean_ctor_get(x_204, 0);
lean_dec(x_340);
x_341 = !lean_is_exclusive(x_205);
if (x_341 == 0)
{
uint8_t x_342; uint8_t x_343; 
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_298);
x_342 = 0;
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_342);
x_343 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_343);
return x_1;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; uint8_t x_350; 
x_344 = lean_ctor_get(x_205, 0);
x_345 = lean_ctor_get(x_205, 1);
x_346 = lean_ctor_get(x_205, 2);
x_347 = lean_ctor_get(x_205, 3);
lean_inc(x_347);
lean_inc(x_346);
lean_inc(x_345);
lean_inc(x_344);
lean_dec(x_205);
x_348 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_348, 0, x_344);
lean_ctor_set(x_348, 1, x_345);
lean_ctor_set(x_348, 2, x_346);
lean_ctor_set(x_348, 3, x_347);
lean_ctor_set_uint8(x_348, sizeof(void*)*4, x_298);
x_349 = 0;
lean_ctor_set(x_204, 0, x_348);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_349);
x_350 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_350);
return x_1;
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; uint8_t x_361; 
x_351 = lean_ctor_get(x_204, 1);
x_352 = lean_ctor_get(x_204, 2);
lean_inc(x_352);
lean_inc(x_351);
lean_dec(x_204);
x_353 = lean_ctor_get(x_205, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_205, 1);
lean_inc(x_354);
x_355 = lean_ctor_get(x_205, 2);
lean_inc(x_355);
x_356 = lean_ctor_get(x_205, 3);
lean_inc(x_356);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_357 = x_205;
} else {
 lean_dec_ref(x_205);
 x_357 = lean_box(0);
}
if (lean_is_scalar(x_357)) {
 x_358 = lean_alloc_ctor(1, 4, 1);
} else {
 x_358 = x_357;
}
lean_ctor_set(x_358, 0, x_353);
lean_ctor_set(x_358, 1, x_354);
lean_ctor_set(x_358, 2, x_355);
lean_ctor_set(x_358, 3, x_356);
lean_ctor_set_uint8(x_358, sizeof(void*)*4, x_298);
x_359 = 0;
x_360 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set(x_360, 1, x_351);
lean_ctor_set(x_360, 2, x_352);
lean_ctor_set(x_360, 3, x_287);
lean_ctor_set_uint8(x_360, sizeof(void*)*4, x_359);
x_361 = 1;
lean_ctor_set(x_1, 3, x_360);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_361);
return x_1;
}
}
}
}
}
}
}
}
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; 
x_362 = lean_ctor_get(x_1, 0);
x_363 = lean_ctor_get(x_1, 1);
x_364 = lean_ctor_get(x_1, 2);
x_365 = lean_ctor_get(x_1, 3);
lean_inc(x_365);
lean_inc(x_364);
lean_inc(x_363);
lean_inc(x_362);
lean_dec(x_1);
x_366 = l_Lean_Name_quickCmp(x_2, x_363);
switch (x_366) {
case 0:
{
uint8_t x_367; 
x_367 = l_Std_RBNode_isRed___rarg(x_362);
if (x_367 == 0)
{
lean_object* x_368; uint8_t x_369; lean_object* x_370; 
x_368 = l_Std_RBNode_ins___at_Lean_Level_collectMVars___spec__2(x_362, x_2, x_3);
x_369 = 1;
x_370 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_370, 0, x_368);
lean_ctor_set(x_370, 1, x_363);
lean_ctor_set(x_370, 2, x_364);
lean_ctor_set(x_370, 3, x_365);
lean_ctor_set_uint8(x_370, sizeof(void*)*4, x_369);
return x_370;
}
else
{
lean_object* x_371; lean_object* x_372; 
x_371 = l_Std_RBNode_ins___at_Lean_Level_collectMVars___spec__2(x_362, x_2, x_3);
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; 
x_373 = lean_ctor_get(x_371, 3);
lean_inc(x_373);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; uint8_t x_377; lean_object* x_378; uint8_t x_379; lean_object* x_380; 
x_374 = lean_ctor_get(x_371, 1);
lean_inc(x_374);
x_375 = lean_ctor_get(x_371, 2);
lean_inc(x_375);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_376 = x_371;
} else {
 lean_dec_ref(x_371);
 x_376 = lean_box(0);
}
x_377 = 0;
if (lean_is_scalar(x_376)) {
 x_378 = lean_alloc_ctor(1, 4, 1);
} else {
 x_378 = x_376;
}
lean_ctor_set(x_378, 0, x_373);
lean_ctor_set(x_378, 1, x_374);
lean_ctor_set(x_378, 2, x_375);
lean_ctor_set(x_378, 3, x_373);
lean_ctor_set_uint8(x_378, sizeof(void*)*4, x_377);
x_379 = 1;
x_380 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_363);
lean_ctor_set(x_380, 2, x_364);
lean_ctor_set(x_380, 3, x_365);
lean_ctor_set_uint8(x_380, sizeof(void*)*4, x_379);
return x_380;
}
else
{
uint8_t x_381; 
x_381 = lean_ctor_get_uint8(x_373, sizeof(void*)*4);
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; uint8_t x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; lean_object* x_394; 
x_382 = lean_ctor_get(x_371, 1);
lean_inc(x_382);
x_383 = lean_ctor_get(x_371, 2);
lean_inc(x_383);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_384 = x_371;
} else {
 lean_dec_ref(x_371);
 x_384 = lean_box(0);
}
x_385 = lean_ctor_get(x_373, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_373, 1);
lean_inc(x_386);
x_387 = lean_ctor_get(x_373, 2);
lean_inc(x_387);
x_388 = lean_ctor_get(x_373, 3);
lean_inc(x_388);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 lean_ctor_release(x_373, 2);
 lean_ctor_release(x_373, 3);
 x_389 = x_373;
} else {
 lean_dec_ref(x_373);
 x_389 = lean_box(0);
}
x_390 = 1;
if (lean_is_scalar(x_389)) {
 x_391 = lean_alloc_ctor(1, 4, 1);
} else {
 x_391 = x_389;
}
lean_ctor_set(x_391, 0, x_372);
lean_ctor_set(x_391, 1, x_382);
lean_ctor_set(x_391, 2, x_383);
lean_ctor_set(x_391, 3, x_385);
lean_ctor_set_uint8(x_391, sizeof(void*)*4, x_390);
if (lean_is_scalar(x_384)) {
 x_392 = lean_alloc_ctor(1, 4, 1);
} else {
 x_392 = x_384;
}
lean_ctor_set(x_392, 0, x_388);
lean_ctor_set(x_392, 1, x_363);
lean_ctor_set(x_392, 2, x_364);
lean_ctor_set(x_392, 3, x_365);
lean_ctor_set_uint8(x_392, sizeof(void*)*4, x_390);
x_393 = 0;
x_394 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_394, 0, x_391);
lean_ctor_set(x_394, 1, x_386);
lean_ctor_set(x_394, 2, x_387);
lean_ctor_set(x_394, 3, x_392);
lean_ctor_set_uint8(x_394, sizeof(void*)*4, x_393);
return x_394;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; lean_object* x_399; uint8_t x_400; lean_object* x_401; 
x_395 = lean_ctor_get(x_371, 1);
lean_inc(x_395);
x_396 = lean_ctor_get(x_371, 2);
lean_inc(x_396);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_397 = x_371;
} else {
 lean_dec_ref(x_371);
 x_397 = lean_box(0);
}
x_398 = 0;
if (lean_is_scalar(x_397)) {
 x_399 = lean_alloc_ctor(1, 4, 1);
} else {
 x_399 = x_397;
}
lean_ctor_set(x_399, 0, x_372);
lean_ctor_set(x_399, 1, x_395);
lean_ctor_set(x_399, 2, x_396);
lean_ctor_set(x_399, 3, x_373);
lean_ctor_set_uint8(x_399, sizeof(void*)*4, x_398);
x_400 = 1;
x_401 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_401, 0, x_399);
lean_ctor_set(x_401, 1, x_363);
lean_ctor_set(x_401, 2, x_364);
lean_ctor_set(x_401, 3, x_365);
lean_ctor_set_uint8(x_401, sizeof(void*)*4, x_400);
return x_401;
}
}
}
else
{
uint8_t x_402; 
x_402 = lean_ctor_get_uint8(x_372, sizeof(void*)*4);
if (x_402 == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; lean_object* x_416; 
x_403 = lean_ctor_get(x_371, 1);
lean_inc(x_403);
x_404 = lean_ctor_get(x_371, 2);
lean_inc(x_404);
x_405 = lean_ctor_get(x_371, 3);
lean_inc(x_405);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_406 = x_371;
} else {
 lean_dec_ref(x_371);
 x_406 = lean_box(0);
}
x_407 = lean_ctor_get(x_372, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_372, 1);
lean_inc(x_408);
x_409 = lean_ctor_get(x_372, 2);
lean_inc(x_409);
x_410 = lean_ctor_get(x_372, 3);
lean_inc(x_410);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 lean_ctor_release(x_372, 2);
 lean_ctor_release(x_372, 3);
 x_411 = x_372;
} else {
 lean_dec_ref(x_372);
 x_411 = lean_box(0);
}
x_412 = 1;
if (lean_is_scalar(x_411)) {
 x_413 = lean_alloc_ctor(1, 4, 1);
} else {
 x_413 = x_411;
}
lean_ctor_set(x_413, 0, x_407);
lean_ctor_set(x_413, 1, x_408);
lean_ctor_set(x_413, 2, x_409);
lean_ctor_set(x_413, 3, x_410);
lean_ctor_set_uint8(x_413, sizeof(void*)*4, x_412);
if (lean_is_scalar(x_406)) {
 x_414 = lean_alloc_ctor(1, 4, 1);
} else {
 x_414 = x_406;
}
lean_ctor_set(x_414, 0, x_405);
lean_ctor_set(x_414, 1, x_363);
lean_ctor_set(x_414, 2, x_364);
lean_ctor_set(x_414, 3, x_365);
lean_ctor_set_uint8(x_414, sizeof(void*)*4, x_412);
x_415 = 0;
x_416 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_416, 0, x_413);
lean_ctor_set(x_416, 1, x_403);
lean_ctor_set(x_416, 2, x_404);
lean_ctor_set(x_416, 3, x_414);
lean_ctor_set_uint8(x_416, sizeof(void*)*4, x_415);
return x_416;
}
else
{
lean_object* x_417; 
x_417 = lean_ctor_get(x_371, 3);
lean_inc(x_417);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; lean_object* x_422; uint8_t x_423; lean_object* x_424; 
x_418 = lean_ctor_get(x_371, 1);
lean_inc(x_418);
x_419 = lean_ctor_get(x_371, 2);
lean_inc(x_419);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_420 = x_371;
} else {
 lean_dec_ref(x_371);
 x_420 = lean_box(0);
}
x_421 = 0;
if (lean_is_scalar(x_420)) {
 x_422 = lean_alloc_ctor(1, 4, 1);
} else {
 x_422 = x_420;
}
lean_ctor_set(x_422, 0, x_372);
lean_ctor_set(x_422, 1, x_418);
lean_ctor_set(x_422, 2, x_419);
lean_ctor_set(x_422, 3, x_417);
lean_ctor_set_uint8(x_422, sizeof(void*)*4, x_421);
x_423 = 1;
x_424 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set(x_424, 1, x_363);
lean_ctor_set(x_424, 2, x_364);
lean_ctor_set(x_424, 3, x_365);
lean_ctor_set_uint8(x_424, sizeof(void*)*4, x_423);
return x_424;
}
else
{
uint8_t x_425; 
x_425 = lean_ctor_get_uint8(x_417, sizeof(void*)*4);
if (x_425 == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; lean_object* x_439; 
x_426 = lean_ctor_get(x_371, 1);
lean_inc(x_426);
x_427 = lean_ctor_get(x_371, 2);
lean_inc(x_427);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_428 = x_371;
} else {
 lean_dec_ref(x_371);
 x_428 = lean_box(0);
}
x_429 = lean_ctor_get(x_417, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_417, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_417, 2);
lean_inc(x_431);
x_432 = lean_ctor_get(x_417, 3);
lean_inc(x_432);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 lean_ctor_release(x_417, 2);
 lean_ctor_release(x_417, 3);
 x_433 = x_417;
} else {
 lean_dec_ref(x_417);
 x_433 = lean_box(0);
}
x_434 = 1;
lean_inc(x_372);
if (lean_is_scalar(x_433)) {
 x_435 = lean_alloc_ctor(1, 4, 1);
} else {
 x_435 = x_433;
}
lean_ctor_set(x_435, 0, x_372);
lean_ctor_set(x_435, 1, x_426);
lean_ctor_set(x_435, 2, x_427);
lean_ctor_set(x_435, 3, x_429);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 lean_ctor_release(x_372, 2);
 lean_ctor_release(x_372, 3);
 x_436 = x_372;
} else {
 lean_dec_ref(x_372);
 x_436 = lean_box(0);
}
lean_ctor_set_uint8(x_435, sizeof(void*)*4, x_434);
if (lean_is_scalar(x_436)) {
 x_437 = lean_alloc_ctor(1, 4, 1);
} else {
 x_437 = x_436;
}
lean_ctor_set(x_437, 0, x_432);
lean_ctor_set(x_437, 1, x_363);
lean_ctor_set(x_437, 2, x_364);
lean_ctor_set(x_437, 3, x_365);
lean_ctor_set_uint8(x_437, sizeof(void*)*4, x_434);
x_438 = 0;
if (lean_is_scalar(x_428)) {
 x_439 = lean_alloc_ctor(1, 4, 1);
} else {
 x_439 = x_428;
}
lean_ctor_set(x_439, 0, x_435);
lean_ctor_set(x_439, 1, x_430);
lean_ctor_set(x_439, 2, x_431);
lean_ctor_set(x_439, 3, x_437);
lean_ctor_set_uint8(x_439, sizeof(void*)*4, x_438);
return x_439;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; uint8_t x_449; lean_object* x_450; uint8_t x_451; lean_object* x_452; 
x_440 = lean_ctor_get(x_371, 1);
lean_inc(x_440);
x_441 = lean_ctor_get(x_371, 2);
lean_inc(x_441);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_442 = x_371;
} else {
 lean_dec_ref(x_371);
 x_442 = lean_box(0);
}
x_443 = lean_ctor_get(x_372, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_372, 1);
lean_inc(x_444);
x_445 = lean_ctor_get(x_372, 2);
lean_inc(x_445);
x_446 = lean_ctor_get(x_372, 3);
lean_inc(x_446);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 lean_ctor_release(x_372, 2);
 lean_ctor_release(x_372, 3);
 x_447 = x_372;
} else {
 lean_dec_ref(x_372);
 x_447 = lean_box(0);
}
if (lean_is_scalar(x_447)) {
 x_448 = lean_alloc_ctor(1, 4, 1);
} else {
 x_448 = x_447;
}
lean_ctor_set(x_448, 0, x_443);
lean_ctor_set(x_448, 1, x_444);
lean_ctor_set(x_448, 2, x_445);
lean_ctor_set(x_448, 3, x_446);
lean_ctor_set_uint8(x_448, sizeof(void*)*4, x_425);
x_449 = 0;
if (lean_is_scalar(x_442)) {
 x_450 = lean_alloc_ctor(1, 4, 1);
} else {
 x_450 = x_442;
}
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_440);
lean_ctor_set(x_450, 2, x_441);
lean_ctor_set(x_450, 3, x_417);
lean_ctor_set_uint8(x_450, sizeof(void*)*4, x_449);
x_451 = 1;
x_452 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_452, 0, x_450);
lean_ctor_set(x_452, 1, x_363);
lean_ctor_set(x_452, 2, x_364);
lean_ctor_set(x_452, 3, x_365);
lean_ctor_set_uint8(x_452, sizeof(void*)*4, x_451);
return x_452;
}
}
}
}
}
}
case 1:
{
uint8_t x_453; lean_object* x_454; 
lean_dec(x_364);
lean_dec(x_363);
x_453 = 1;
x_454 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_454, 0, x_362);
lean_ctor_set(x_454, 1, x_2);
lean_ctor_set(x_454, 2, x_3);
lean_ctor_set(x_454, 3, x_365);
lean_ctor_set_uint8(x_454, sizeof(void*)*4, x_453);
return x_454;
}
default: 
{
uint8_t x_455; 
x_455 = l_Std_RBNode_isRed___rarg(x_365);
if (x_455 == 0)
{
lean_object* x_456; uint8_t x_457; lean_object* x_458; 
x_456 = l_Std_RBNode_ins___at_Lean_Level_collectMVars___spec__2(x_365, x_2, x_3);
x_457 = 1;
x_458 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_458, 0, x_362);
lean_ctor_set(x_458, 1, x_363);
lean_ctor_set(x_458, 2, x_364);
lean_ctor_set(x_458, 3, x_456);
lean_ctor_set_uint8(x_458, sizeof(void*)*4, x_457);
return x_458;
}
else
{
lean_object* x_459; lean_object* x_460; 
x_459 = l_Std_RBNode_ins___at_Lean_Level_collectMVars___spec__2(x_365, x_2, x_3);
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; 
x_461 = lean_ctor_get(x_459, 3);
lean_inc(x_461);
if (lean_obj_tag(x_461) == 0)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; uint8_t x_465; lean_object* x_466; uint8_t x_467; lean_object* x_468; 
x_462 = lean_ctor_get(x_459, 1);
lean_inc(x_462);
x_463 = lean_ctor_get(x_459, 2);
lean_inc(x_463);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_464 = x_459;
} else {
 lean_dec_ref(x_459);
 x_464 = lean_box(0);
}
x_465 = 0;
if (lean_is_scalar(x_464)) {
 x_466 = lean_alloc_ctor(1, 4, 1);
} else {
 x_466 = x_464;
}
lean_ctor_set(x_466, 0, x_461);
lean_ctor_set(x_466, 1, x_462);
lean_ctor_set(x_466, 2, x_463);
lean_ctor_set(x_466, 3, x_461);
lean_ctor_set_uint8(x_466, sizeof(void*)*4, x_465);
x_467 = 1;
x_468 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_468, 0, x_362);
lean_ctor_set(x_468, 1, x_363);
lean_ctor_set(x_468, 2, x_364);
lean_ctor_set(x_468, 3, x_466);
lean_ctor_set_uint8(x_468, sizeof(void*)*4, x_467);
return x_468;
}
else
{
uint8_t x_469; 
x_469 = lean_ctor_get_uint8(x_461, sizeof(void*)*4);
if (x_469 == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; uint8_t x_478; lean_object* x_479; lean_object* x_480; uint8_t x_481; lean_object* x_482; 
x_470 = lean_ctor_get(x_459, 1);
lean_inc(x_470);
x_471 = lean_ctor_get(x_459, 2);
lean_inc(x_471);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_472 = x_459;
} else {
 lean_dec_ref(x_459);
 x_472 = lean_box(0);
}
x_473 = lean_ctor_get(x_461, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_461, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_461, 2);
lean_inc(x_475);
x_476 = lean_ctor_get(x_461, 3);
lean_inc(x_476);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 lean_ctor_release(x_461, 1);
 lean_ctor_release(x_461, 2);
 lean_ctor_release(x_461, 3);
 x_477 = x_461;
} else {
 lean_dec_ref(x_461);
 x_477 = lean_box(0);
}
x_478 = 1;
if (lean_is_scalar(x_477)) {
 x_479 = lean_alloc_ctor(1, 4, 1);
} else {
 x_479 = x_477;
}
lean_ctor_set(x_479, 0, x_362);
lean_ctor_set(x_479, 1, x_363);
lean_ctor_set(x_479, 2, x_364);
lean_ctor_set(x_479, 3, x_460);
lean_ctor_set_uint8(x_479, sizeof(void*)*4, x_478);
if (lean_is_scalar(x_472)) {
 x_480 = lean_alloc_ctor(1, 4, 1);
} else {
 x_480 = x_472;
}
lean_ctor_set(x_480, 0, x_473);
lean_ctor_set(x_480, 1, x_474);
lean_ctor_set(x_480, 2, x_475);
lean_ctor_set(x_480, 3, x_476);
lean_ctor_set_uint8(x_480, sizeof(void*)*4, x_478);
x_481 = 0;
x_482 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_482, 0, x_479);
lean_ctor_set(x_482, 1, x_470);
lean_ctor_set(x_482, 2, x_471);
lean_ctor_set(x_482, 3, x_480);
lean_ctor_set_uint8(x_482, sizeof(void*)*4, x_481);
return x_482;
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; uint8_t x_486; lean_object* x_487; uint8_t x_488; lean_object* x_489; 
x_483 = lean_ctor_get(x_459, 1);
lean_inc(x_483);
x_484 = lean_ctor_get(x_459, 2);
lean_inc(x_484);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_485 = x_459;
} else {
 lean_dec_ref(x_459);
 x_485 = lean_box(0);
}
x_486 = 0;
if (lean_is_scalar(x_485)) {
 x_487 = lean_alloc_ctor(1, 4, 1);
} else {
 x_487 = x_485;
}
lean_ctor_set(x_487, 0, x_460);
lean_ctor_set(x_487, 1, x_483);
lean_ctor_set(x_487, 2, x_484);
lean_ctor_set(x_487, 3, x_461);
lean_ctor_set_uint8(x_487, sizeof(void*)*4, x_486);
x_488 = 1;
x_489 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_489, 0, x_362);
lean_ctor_set(x_489, 1, x_363);
lean_ctor_set(x_489, 2, x_364);
lean_ctor_set(x_489, 3, x_487);
lean_ctor_set_uint8(x_489, sizeof(void*)*4, x_488);
return x_489;
}
}
}
else
{
uint8_t x_490; 
x_490 = lean_ctor_get_uint8(x_460, sizeof(void*)*4);
if (x_490 == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; uint8_t x_500; lean_object* x_501; lean_object* x_502; uint8_t x_503; lean_object* x_504; 
x_491 = lean_ctor_get(x_459, 1);
lean_inc(x_491);
x_492 = lean_ctor_get(x_459, 2);
lean_inc(x_492);
x_493 = lean_ctor_get(x_459, 3);
lean_inc(x_493);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_494 = x_459;
} else {
 lean_dec_ref(x_459);
 x_494 = lean_box(0);
}
x_495 = lean_ctor_get(x_460, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_460, 1);
lean_inc(x_496);
x_497 = lean_ctor_get(x_460, 2);
lean_inc(x_497);
x_498 = lean_ctor_get(x_460, 3);
lean_inc(x_498);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 lean_ctor_release(x_460, 2);
 lean_ctor_release(x_460, 3);
 x_499 = x_460;
} else {
 lean_dec_ref(x_460);
 x_499 = lean_box(0);
}
x_500 = 1;
if (lean_is_scalar(x_499)) {
 x_501 = lean_alloc_ctor(1, 4, 1);
} else {
 x_501 = x_499;
}
lean_ctor_set(x_501, 0, x_362);
lean_ctor_set(x_501, 1, x_363);
lean_ctor_set(x_501, 2, x_364);
lean_ctor_set(x_501, 3, x_495);
lean_ctor_set_uint8(x_501, sizeof(void*)*4, x_500);
if (lean_is_scalar(x_494)) {
 x_502 = lean_alloc_ctor(1, 4, 1);
} else {
 x_502 = x_494;
}
lean_ctor_set(x_502, 0, x_498);
lean_ctor_set(x_502, 1, x_491);
lean_ctor_set(x_502, 2, x_492);
lean_ctor_set(x_502, 3, x_493);
lean_ctor_set_uint8(x_502, sizeof(void*)*4, x_500);
x_503 = 0;
x_504 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_504, 0, x_501);
lean_ctor_set(x_504, 1, x_496);
lean_ctor_set(x_504, 2, x_497);
lean_ctor_set(x_504, 3, x_502);
lean_ctor_set_uint8(x_504, sizeof(void*)*4, x_503);
return x_504;
}
else
{
lean_object* x_505; 
x_505 = lean_ctor_get(x_459, 3);
lean_inc(x_505);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; uint8_t x_509; lean_object* x_510; uint8_t x_511; lean_object* x_512; 
x_506 = lean_ctor_get(x_459, 1);
lean_inc(x_506);
x_507 = lean_ctor_get(x_459, 2);
lean_inc(x_507);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_508 = x_459;
} else {
 lean_dec_ref(x_459);
 x_508 = lean_box(0);
}
x_509 = 0;
if (lean_is_scalar(x_508)) {
 x_510 = lean_alloc_ctor(1, 4, 1);
} else {
 x_510 = x_508;
}
lean_ctor_set(x_510, 0, x_460);
lean_ctor_set(x_510, 1, x_506);
lean_ctor_set(x_510, 2, x_507);
lean_ctor_set(x_510, 3, x_505);
lean_ctor_set_uint8(x_510, sizeof(void*)*4, x_509);
x_511 = 1;
x_512 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_512, 0, x_362);
lean_ctor_set(x_512, 1, x_363);
lean_ctor_set(x_512, 2, x_364);
lean_ctor_set(x_512, 3, x_510);
lean_ctor_set_uint8(x_512, sizeof(void*)*4, x_511);
return x_512;
}
else
{
uint8_t x_513; 
x_513 = lean_ctor_get_uint8(x_505, sizeof(void*)*4);
if (x_513 == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; uint8_t x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; lean_object* x_527; 
x_514 = lean_ctor_get(x_459, 1);
lean_inc(x_514);
x_515 = lean_ctor_get(x_459, 2);
lean_inc(x_515);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_516 = x_459;
} else {
 lean_dec_ref(x_459);
 x_516 = lean_box(0);
}
x_517 = lean_ctor_get(x_505, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_505, 1);
lean_inc(x_518);
x_519 = lean_ctor_get(x_505, 2);
lean_inc(x_519);
x_520 = lean_ctor_get(x_505, 3);
lean_inc(x_520);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 lean_ctor_release(x_505, 2);
 lean_ctor_release(x_505, 3);
 x_521 = x_505;
} else {
 lean_dec_ref(x_505);
 x_521 = lean_box(0);
}
x_522 = 1;
lean_inc(x_460);
if (lean_is_scalar(x_521)) {
 x_523 = lean_alloc_ctor(1, 4, 1);
} else {
 x_523 = x_521;
}
lean_ctor_set(x_523, 0, x_362);
lean_ctor_set(x_523, 1, x_363);
lean_ctor_set(x_523, 2, x_364);
lean_ctor_set(x_523, 3, x_460);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 lean_ctor_release(x_460, 2);
 lean_ctor_release(x_460, 3);
 x_524 = x_460;
} else {
 lean_dec_ref(x_460);
 x_524 = lean_box(0);
}
lean_ctor_set_uint8(x_523, sizeof(void*)*4, x_522);
if (lean_is_scalar(x_524)) {
 x_525 = lean_alloc_ctor(1, 4, 1);
} else {
 x_525 = x_524;
}
lean_ctor_set(x_525, 0, x_517);
lean_ctor_set(x_525, 1, x_518);
lean_ctor_set(x_525, 2, x_519);
lean_ctor_set(x_525, 3, x_520);
lean_ctor_set_uint8(x_525, sizeof(void*)*4, x_522);
x_526 = 0;
if (lean_is_scalar(x_516)) {
 x_527 = lean_alloc_ctor(1, 4, 1);
} else {
 x_527 = x_516;
}
lean_ctor_set(x_527, 0, x_523);
lean_ctor_set(x_527, 1, x_514);
lean_ctor_set(x_527, 2, x_515);
lean_ctor_set(x_527, 3, x_525);
lean_ctor_set_uint8(x_527, sizeof(void*)*4, x_526);
return x_527;
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; uint8_t x_537; lean_object* x_538; uint8_t x_539; lean_object* x_540; 
x_528 = lean_ctor_get(x_459, 1);
lean_inc(x_528);
x_529 = lean_ctor_get(x_459, 2);
lean_inc(x_529);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_530 = x_459;
} else {
 lean_dec_ref(x_459);
 x_530 = lean_box(0);
}
x_531 = lean_ctor_get(x_460, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_460, 1);
lean_inc(x_532);
x_533 = lean_ctor_get(x_460, 2);
lean_inc(x_533);
x_534 = lean_ctor_get(x_460, 3);
lean_inc(x_534);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 lean_ctor_release(x_460, 2);
 lean_ctor_release(x_460, 3);
 x_535 = x_460;
} else {
 lean_dec_ref(x_460);
 x_535 = lean_box(0);
}
if (lean_is_scalar(x_535)) {
 x_536 = lean_alloc_ctor(1, 4, 1);
} else {
 x_536 = x_535;
}
lean_ctor_set(x_536, 0, x_531);
lean_ctor_set(x_536, 1, x_532);
lean_ctor_set(x_536, 2, x_533);
lean_ctor_set(x_536, 3, x_534);
lean_ctor_set_uint8(x_536, sizeof(void*)*4, x_513);
x_537 = 0;
if (lean_is_scalar(x_530)) {
 x_538 = lean_alloc_ctor(1, 4, 1);
} else {
 x_538 = x_530;
}
lean_ctor_set(x_538, 0, x_536);
lean_ctor_set(x_538, 1, x_528);
lean_ctor_set(x_538, 2, x_529);
lean_ctor_set(x_538, 3, x_505);
lean_ctor_set_uint8(x_538, sizeof(void*)*4, x_537);
x_539 = 1;
x_540 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_540, 0, x_362);
lean_ctor_set(x_540, 1, x_363);
lean_ctor_set(x_540, 2, x_364);
lean_ctor_set(x_540, 3, x_538);
lean_ctor_set_uint8(x_540, sizeof(void*)*4, x_539);
return x_540;
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_insert___at_Lean_Level_collectMVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Std_RBNode_ins___at_Lean_Level_collectMVars___spec__2(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Std_RBNode_ins___at_Lean_Level_collectMVars___spec__2(x_1, x_2, x_3);
x_7 = l_Std_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_collectMVars(lean_object* x_1, lean_object* x_2) {
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
x_15 = l_Std_RBNode_insert___at_Lean_Level_collectMVars___spec__1(x_2, x_13, x_14);
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
LEAN_EXPORT lean_object* l_Lean_Level_find_x3f_visit(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Level_find_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Level_find_x3f_visit(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_any(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Level_any___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Level_any(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_toLevel(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_toLevel___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* initialize_Lean_Level(lean_object* w) {
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
l_Lean_instInhabitedMVarId = _init_l_Lean_instInhabitedMVarId();
lean_mark_persistent(l_Lean_instInhabitedMVarId);
l_Lean_instBEqMVarId___closed__1 = _init_l_Lean_instBEqMVarId___closed__1();
lean_mark_persistent(l_Lean_instBEqMVarId___closed__1);
l_Lean_instBEqMVarId = _init_l_Lean_instBEqMVarId();
lean_mark_persistent(l_Lean_instBEqMVarId);
l_Lean_instHashableMVarId___closed__1 = _init_l_Lean_instHashableMVarId___closed__1();
lean_mark_persistent(l_Lean_instHashableMVarId___closed__1);
l_Lean_instHashableMVarId = _init_l_Lean_instHashableMVarId();
lean_mark_persistent(l_Lean_instHashableMVarId);
l_Lean_instMVarIdSetInhabited = _init_l_Lean_instMVarIdSetInhabited();
lean_mark_persistent(l_Lean_instMVarIdSetInhabited);
l_Lean_instMVarIdSetEmptyCollection = _init_l_Lean_instMVarIdSetEmptyCollection();
lean_mark_persistent(l_Lean_instMVarIdSetEmptyCollection);
l_Lean_instForInMVarIdSetMVarId___closed__1 = _init_l_Lean_instForInMVarIdSetMVarId___closed__1();
lean_mark_persistent(l_Lean_instForInMVarIdSetMVarId___closed__1);
l_Lean_instForInMVarIdSetMVarId___closed__2 = _init_l_Lean_instForInMVarIdSetMVarId___closed__2();
lean_mark_persistent(l_Lean_instForInMVarIdSetMVarId___closed__2);
l_Lean_instInhabitedLevel___closed__1 = _init_l_Lean_instInhabitedLevel___closed__1();
l_Lean_instInhabitedLevel___closed__2 = _init_l_Lean_instInhabitedLevel___closed__2();
lean_mark_persistent(l_Lean_instInhabitedLevel___closed__2);
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
l_Lean_Level_normalize___closed__3 = _init_l_Lean_Level_normalize___closed__3();
lean_mark_persistent(l_Lean_Level_normalize___closed__3);
l_Lean_Level_normalize___closed__4 = _init_l_Lean_Level_normalize___closed__4();
lean_mark_persistent(l_Lean_Level_normalize___closed__4);
l_Lean_Level_PP_toResult___closed__1 = _init_l_Lean_Level_PP_toResult___closed__1();
lean_mark_persistent(l_Lean_Level_PP_toResult___closed__1);
l_Lean_Level_PP_toResult___closed__2 = _init_l_Lean_Level_PP_toResult___closed__2();
lean_mark_persistent(l_Lean_Level_PP_toResult___closed__2);
l_Lean_Level_PP_toResult___closed__3 = _init_l_Lean_Level_PP_toResult___closed__3();
lean_mark_persistent(l_Lean_Level_PP_toResult___closed__3);
l_Lean_Level_PP_toResult___closed__4 = _init_l_Lean_Level_PP_toResult___closed__4();
lean_mark_persistent(l_Lean_Level_PP_toResult___closed__4);
l_Lean_Level_PP_toResult___closed__5 = _init_l_Lean_Level_PP_toResult___closed__5();
lean_mark_persistent(l_Lean_Level_PP_toResult___closed__5);
l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1 = _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1();
lean_mark_persistent(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1);
l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2 = _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2();
lean_mark_persistent(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2);
l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__3 = _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__3();
lean_mark_persistent(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__3);
l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__4 = _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__4();
lean_mark_persistent(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__4);
l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__5 = _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__5();
lean_mark_persistent(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__5);
l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__6 = _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__6();
lean_mark_persistent(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__6);
l_Lean_Level_PP_Result_format___closed__1 = _init_l_Lean_Level_PP_Result_format___closed__1();
lean_mark_persistent(l_Lean_Level_PP_Result_format___closed__1);
l_Lean_Level_PP_Result_format___closed__2 = _init_l_Lean_Level_PP_Result_format___closed__2();
lean_mark_persistent(l_Lean_Level_PP_Result_format___closed__2);
l_Lean_Level_PP_Result_format___closed__3 = _init_l_Lean_Level_PP_Result_format___closed__3();
lean_mark_persistent(l_Lean_Level_PP_Result_format___closed__3);
l_Lean_Level_PP_Result_format___closed__4 = _init_l_Lean_Level_PP_Result_format___closed__4();
lean_mark_persistent(l_Lean_Level_PP_Result_format___closed__4);
l_Lean_Level_PP_Result_format___closed__5 = _init_l_Lean_Level_PP_Result_format___closed__5();
lean_mark_persistent(l_Lean_Level_PP_Result_format___closed__5);
l_Lean_Level_PP_Result_format___closed__6 = _init_l_Lean_Level_PP_Result_format___closed__6();
lean_mark_persistent(l_Lean_Level_PP_Result_format___closed__6);
l_Lean_Level_PP_Result_quote___lambda__3___closed__1 = _init_l_Lean_Level_PP_Result_quote___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___lambda__3___closed__1);
l_Lean_Level_PP_Result_quote___lambda__3___closed__2 = _init_l_Lean_Level_PP_Result_quote___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___lambda__3___closed__2);
l_Lean_Level_PP_Result_quote___lambda__3___closed__3 = _init_l_Lean_Level_PP_Result_quote___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___lambda__3___closed__3);
l_Lean_Level_PP_Result_quote___lambda__3___closed__4 = _init_l_Lean_Level_PP_Result_quote___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___lambda__3___closed__4);
l_Lean_Level_PP_Result_quote___lambda__3___closed__5 = _init_l_Lean_Level_PP_Result_quote___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___lambda__3___closed__5);
l_Lean_Level_PP_Result_quote___lambda__3___closed__6 = _init_l_Lean_Level_PP_Result_quote___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___lambda__3___closed__6);
l_Lean_Level_PP_Result_quote___lambda__3___closed__7 = _init_l_Lean_Level_PP_Result_quote___lambda__3___closed__7();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___lambda__3___closed__7);
l_Lean_Level_PP_Result_quote___lambda__3___closed__8 = _init_l_Lean_Level_PP_Result_quote___lambda__3___closed__8();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___lambda__3___closed__8);
l_Lean_Level_PP_Result_quote___lambda__3___closed__9 = _init_l_Lean_Level_PP_Result_quote___lambda__3___closed__9();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___lambda__3___closed__9);
l_Lean_Level_PP_Result_quote___lambda__4___closed__1 = _init_l_Lean_Level_PP_Result_quote___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___lambda__4___closed__1);
l_Lean_Level_PP_Result_quote___lambda__4___closed__2 = _init_l_Lean_Level_PP_Result_quote___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___lambda__4___closed__2);
l_Lean_Level_PP_Result_quote___lambda__5___closed__1 = _init_l_Lean_Level_PP_Result_quote___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___lambda__5___closed__1);
l_Lean_Level_PP_Result_quote___lambda__5___closed__2 = _init_l_Lean_Level_PP_Result_quote___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___lambda__5___closed__2);
l_Lean_Level_PP_Result_quote___lambda__5___closed__3 = _init_l_Lean_Level_PP_Result_quote___lambda__5___closed__3();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___lambda__5___closed__3);
l_Lean_Level_PP_Result_quote___lambda__5___closed__4 = _init_l_Lean_Level_PP_Result_quote___lambda__5___closed__4();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___lambda__5___closed__4);
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

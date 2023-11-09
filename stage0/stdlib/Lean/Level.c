// Lean compiler output
// Module: Lean.Level
// Imports: Init Lean.Data.HashMap Lean.Data.HashSet Lean.Data.PersistentHashMap Lean.Data.PersistentHashSet Lean.Hygiene Lean.Data.Name Lean.Data.Format
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
LEAN_EXPORT lean_object* l_Lean_Level_Data_hasParam___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_isSucc___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_find_x3f_visit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_toLevel___boxed(lean_object*);
LEAN_EXPORT lean_object* lean_level_mk_param(lean_object*);
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
static lean_object* l_Lean_Level_PP_Result_format___closed__6;
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__3;
static lean_object* l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__4;
static lean_object* l_Lean_instReprData___lambda__3___closed__1;
static lean_object* l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__7;
static lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__3;
static lean_object* l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__13;
static lean_object* l_Lean_Level_mkData___closed__4;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_mvar___override(lean_object*);
static lean_object* l_Lean_Level_PP_Result_quote___closed__10;
lean_object* lean_uint32_to_nat(uint32_t);
static lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__4;
LEAN_EXPORT lean_object* l_Lean_instReprData___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Level_PP_toResult___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkIMaxAux(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_level_has_mvar(lean_object*);
LEAN_EXPORT lean_object* lean_level_mk_succ(lean_object*);
static lean_object* l_Lean_instForInLMVarIdMapProdLMVarId___closed__1;
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Level_instHashableLevel___closed__1;
LEAN_EXPORT uint8_t l_Lean_instBEqData(uint64_t, uint64_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Level_PP_Result_quote___closed__7;
LEAN_EXPORT lean_object* l_Nat_toLevel(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_geq_go___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__18;
static lean_object* l_Lean_Level_PP_toResult___closed__5;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Level_normalize___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_isMaxIMax___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_hasParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_addOffsetAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Level_mvarId_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqData___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Level_succ___override(lean_object*);
static lean_object* l_Lean_instReprData___lambda__2___closed__2;
LEAN_EXPORT uint64_t l_Lean_Level_Data_hash(uint64_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lean_Level_collectMVars___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_RBNode_isRed___rarg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
lean_object* l_Array_qpartition___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_mkData___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instToFormatLevel(lean_object*);
LEAN_EXPORT uint32_t lean_level_depth(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override(lean_object*);
static lean_object* l_Lean_instHashableLevelMVarId___closed__1;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_instLMVarIdSetInhabited;
LEAN_EXPORT lean_object* l_Lean_Level_addOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_isMVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_zero___override;
static lean_object* l_Lean_Level_PP_Result_quote___closed__16;
LEAN_EXPORT lean_object* l_Lean_Level_Data_hasMVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isExplicit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_max___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_level_mk_zero(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isZero(lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__4;
LEAN_EXPORT uint32_t lean_level_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Data_depth___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_hashEx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Data_hash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprData(uint64_t, lean_object*);
LEAN_EXPORT lean_object* lean_level_mk_imax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_isParam___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isSucc(lean_object*);
static lean_object* l_Lean_Level_PP_Result_quote___closed__11;
LEAN_EXPORT lean_object* l_Lean_Level_substParams(lean_object*, lean_object*);
static lean_object* l_Lean_instReprData___closed__1;
static lean_object* l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__10;
static lean_object* l_Lean_Level_PP_Result_format___closed__5;
static lean_object* l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__8;
LEAN_EXPORT lean_object* l_Lean_instReprData___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_qsort_sort___at_Lean_Level_normalize___spec__3___closed__1;
static lean_object* l_Lean_Level_PP_Result_quote___closed__12;
static lean_object* l_Lean_Level_PP_Result_quote___closed__17;
LEAN_EXPORT lean_object* l_Lean_instReprLMVarId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedLevel;
static lean_object* l_Lean_instReprData___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Level_normLtAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instReprData___lambda__2___closed__1;
static lean_object* l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__3;
static lean_object* l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__23;
static lean_object* l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__2;
LEAN_EXPORT lean_object* l_Lean_Level_ofNat(lean_object*);
uint64_t lean_uint64_land(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_mkLevelMVar(lean_object*);
LEAN_EXPORT lean_object* lean_level_mk_mvar(lean_object*);
static lean_object* l_Lean_instBEqLevelMVarId___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at_Lean_Level_normalize___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isEquiv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_format___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_hasParam___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_beqLevelMVarId____x40_Lean_Level___hyg_516_(lean_object*, lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__16;
LEAN_EXPORT lean_object* l_Lean_Level_data___override___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instToStringLevel(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_depthEx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instLMVarIdSetEmptyCollection;
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instReprData___closed__2;
LEAN_EXPORT uint8_t l_Lean_Level_geq_go(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Level_PP_Result_quote___closed__15;
LEAN_EXPORT lean_object* l_Lean_Level_mkData(uint64_t, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Level_hasParamEx___boxed(lean_object*);
static lean_object* l_Lean_Level_PP_Result_quote___closed__4;
static lean_object* l_Lean_Level_PP_Result_quote___closed__8;
static lean_object* l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__9;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLevelSucc(lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__20;
LEAN_EXPORT lean_object* l_Lean_instReprData___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Level_PP_Result_format___closed__2;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Level_quote(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_RBNode_setBlack___rarg(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Level_normalize___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_any___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_toNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprLevel;
static lean_object* l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__22;
static lean_object* l_Lean_Level_mvarId_x21___closed__2;
LEAN_EXPORT uint8_t l_Lean_Level_occurs(lean_object*, lean_object*);
extern uint64_t l_instInhabitedUInt64;
static lean_object* l_Lean_Level_mkData___closed__2;
static lean_object* l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__9;
LEAN_EXPORT lean_object* l_Nat_imax___boxed(lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
static lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkLevelMax(lean_object*, lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Level_normLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(lean_object*, uint8_t);
static lean_object* l_Lean_Level_PP_Result_quote___closed__14;
LEAN_EXPORT lean_object* l_Lean_Level_substParams_go(lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isAlreadyNormalizedCheap___boxed(lean_object*);
static lean_object* l_Lean_Level_PP_Result_quote___closed__6;
LEAN_EXPORT lean_object* l_Lean_Level_ofNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_toResult(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprLevelMVarId;
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_isAlreadyNormalizedCheap(lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__12;
LEAN_EXPORT lean_object* l_panic___at_Lean_Level_mkData___spec__1___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627_(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(lean_object*, lean_object*);
uint64_t lean_uint64_add(uint64_t, uint64_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Lean_Level_isNeverZero___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_simpLevelIMax_x27___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Level_PP_Result_format___closed__4;
static lean_object* l_Lean_instForInLMVarIdSetLMVarId___closed__2;
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_isEquiv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_hasMVarEx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_isIMax___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_normLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_getParamSubst___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instBEqLevel;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Level_data___override___closed__1;
static lean_object* l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__6;
uint32_t lean_uint64_to_uint32(uint64_t);
static lean_object* l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__7;
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint32_to_uint64(uint32_t);
LEAN_EXPORT lean_object* l_Lean_simpLevelIMax_x27(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instForInLMVarIdSetLMVarId___closed__1;
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_succ(lean_object*);
static lean_object* l_Lean_Level_normalize___closed__3;
static lean_object* l_Lean_Level_PP_Result_quote___closed__9;
LEAN_EXPORT lean_object* l_Lean_Level_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_beqLevelMVarId____x40_Lean_Level___hyg_516____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Level_instBEqLevel___closed__1;
static lean_object* l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__12;
lean_object* lean_mk_syntax_ident(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_hasMVar___boxed(lean_object*);
static lean_object* l_Lean_instReprLevel___closed__1;
LEAN_EXPORT lean_object* l_Lean_Level_geq___boxed(lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
LEAN_EXPORT lean_object* l_Lean_Level_isZero___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_depth___boxed(lean_object*);
lean_object* l_Lean_RBMap_instForInRBMapProd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote(lean_object*, lean_object*);
static lean_object* l_Lean_instReprLevelMVarId___closed__1;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_dec___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_geq(lean_object*, lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__6;
LEAN_EXPORT lean_object* l_Lean_instReprData___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprData___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_collectMVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__5;
LEAN_EXPORT uint64_t l___private_Lean_Level_0__Lean_hashLevelMVarId____x40_Lean_Level___hyg_589_(lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2;
static lean_object* l_Lean_Level_PP_Result_quote___closed__1;
static lean_object* l_Lean_Level_PP_Result_quote___closed__2;
static lean_object* l_Lean_Level_PP_Result_quote___closed__3;
LEAN_EXPORT lean_object* l_Lean_instReprData___lambda__2(lean_object*, uint64_t, lean_object*, lean_object*);
static lean_object* l_Lean_Level_PP_toResult___closed__3;
static lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__1;
static lean_object* l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__11;
static lean_object* l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__11;
LEAN_EXPORT lean_object* l_Lean_Level_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_getOffset(lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Level_isMax___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_instInhabitedData;
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap(lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_Data_hasParam(uint64_t);
static lean_object* l_Lean_Level_normalize___closed__4;
LEAN_EXPORT lean_object* l_Lean_Level_getLevelOffset(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_Level_collectMVars___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBTree_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedLMVarIdMap(lean_object*);
static lean_object* l_Lean_Level_normalize___closed__2;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
static lean_object* l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__15;
LEAN_EXPORT lean_object* l_Lean_Level_instQuoteLevelMkStr1(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_quote___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Level_PP_Result_quote___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLevelIMax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_depth(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_occurs___boxed(lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
static lean_object* l_Lean_Level_mkData___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at_Lean_Level_normalize___spec__2(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_dec(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isIMax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_format(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Level_PP_Result_quote___closed__13;
LEAN_EXPORT lean_object* l_Lean_levelOne;
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_accMax(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__3;
LEAN_EXPORT uint8_t l_Lean_Level_isMax(lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2;
static lean_object* l_Lean_Level_PP_toResult___closed__4;
LEAN_EXPORT lean_object* lean_level_mk_max(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Level_Data_depth(uint64_t);
LEAN_EXPORT lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Level_hash(lean_object*);
static lean_object* l_Lean_Level_PP_toResult___closed__2;
static lean_object* l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__1;
static lean_object* l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__21;
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
static lean_object* l_Lean_Level_PP_Result_quote___closed__5;
LEAN_EXPORT lean_object* l_panic___at_Lean_Level_normalize___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_getOffset___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_getParamSubst(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Level_PP_Result_format___closed__1;
LEAN_EXPORT lean_object* l_Lean_instBEqLevelMVarId;
LEAN_EXPORT lean_object* l_Lean_Level_mkNaryMax(lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_param___override(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint64_t lean_bool_to_uint64(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_hashLevelMVarId____x40_Lean_Level___hyg_589____boxed(lean_object*);
static lean_object* l_Lean_Level_mkData___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222_(lean_object*, lean_object*);
static lean_object* l_Lean_Level_PP_Result_format___closed__3;
LEAN_EXPORT uint8_t l_Lean_Level_any(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isMVar(lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Level_normalize___closed__1;
LEAN_EXPORT lean_object* l_Nat_imax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_getLevelOffset___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedLevelMVarId;
static lean_object* l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__10;
static lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2;
static lean_object* l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__13;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isNeverZero(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_isExplicit___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_data___override(lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__17;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__8;
static lean_object* l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__2;
static lean_object* l_Lean_Level_mvarId_x21___closed__3;
LEAN_EXPORT lean_object* l_Lean_simpLevelMax_x27(lean_object*, lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelIMaxCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_Data_hasMVar(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_format(lean_object*, uint8_t);
static lean_object* l_Lean_levelOne___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprLMVarId___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_simpLevelMax_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_max(lean_object*, lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1;
LEAN_EXPORT uint8_t l_Lean_Level_normLtAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_normalize(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instHashableLevel;
LEAN_EXPORT lean_object* l_Lean_Level_hash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imax(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__1;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit(lean_object*, lean_object*);
static lean_object* l_Lean_Level_mvarId_x21___closed__1;
uint8_t l_Lean_Name_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_ctorToNat___boxed(lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__19;
LEAN_EXPORT lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Level_mkData___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_ctorToNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_getOffsetAux___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_level_has_param(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashableLevelMVarId;
LEAN_EXPORT uint8_t l_Lean_Level_isMaxIMax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_imax___override(lean_object*, lean_object*);
static lean_object* l_Lean_Level_mkData___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Level_PP_Result_quote___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_toNat(lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__5;
LEAN_EXPORT lean_object* l_Lean_instReprData___lambda__3(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_getOffsetAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_imax(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_1, x_2);
if (x_5 == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_inc(x_2);
return x_2;
}
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
x_2 = lean_uint64_to_uint32(x_1);
x_3 = lean_uint32_to_uint64(x_2);
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
x_3 = lean_uint64_dec_eq(x_1, x_2);
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
x_3 = lean_uint64_shift_right(x_1, x_2);
x_4 = lean_uint64_to_uint32(x_3);
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
x_3 = lean_uint64_shift_right(x_1, x_2);
x_4 = 1;
x_5 = lean_uint64_land(x_3, x_4);
x_6 = lean_uint64_dec_eq(x_5, x_4);
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
x_3 = lean_uint64_shift_right(x_1, x_2);
x_4 = 1;
x_5 = lean_uint64_land(x_3, x_4);
x_6 = lean_uint64_dec_eq(x_5, x_4);
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
static lean_object* _init_l_panic___at_Lean_Level_mkData___spec__1___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_Lean_instInhabitedData;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Level_mkData___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_panic___at_Lean_Level_mkData___spec__1___boxed__const__1;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
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
x_1 = lean_mk_string_from_bytes("Lean.Level", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_mkData___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Level.mkData", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_mkData___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("universe level depth is too big", 31);
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
LEAN_EXPORT lean_object* l_Lean_Level_mkData(uint64_t x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Level_mkData___closed__1;
x_6 = lean_nat_dec_lt(x_5, x_2);
if (x_6 == 0)
{
uint32_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; lean_object* x_21; 
x_7 = lean_uint64_to_uint32(x_1);
x_8 = lean_uint32_to_uint64(x_7);
x_9 = lean_bool_to_uint64(x_3);
x_10 = 32;
x_11 = lean_uint64_shift_left(x_9, x_10);
x_12 = lean_uint64_add(x_8, x_11);
x_13 = lean_bool_to_uint64(x_4);
x_14 = 33;
x_15 = lean_uint64_shift_left(x_13, x_14);
x_16 = lean_uint64_add(x_12, x_15);
x_17 = lean_uint64_of_nat(x_2);
x_18 = 40;
x_19 = lean_uint64_shift_left(x_17, x_18);
x_20 = lean_uint64_add(x_16, x_19);
x_21 = lean_box_uint64(x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_Level_mkData___closed__5;
x_23 = l_panic___at_Lean_Level_mkData___spec__1(x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mkData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_Level_mkData(x_5, x_2, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = l_Repr_addAppParen(x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_instReprData___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" (hasParam := ", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_instReprData___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("true", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_instReprData___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(")", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData___lambda__2(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Level_Data_hasParam(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Lean_instReprData___lambda__1(x_1, x_3, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = l_Lean_instReprData___lambda__2___closed__1;
x_9 = lean_string_append(x_3, x_8);
x_10 = l_Lean_instReprData___lambda__2___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Lean_instReprData___lambda__2___closed__3;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_box(0);
x_15 = l_Lean_instReprData___lambda__1(x_1, x_13, x_14);
return x_15;
}
}
}
static lean_object* _init_l_Lean_instReprData___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" (hasMVar := ", 13);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData___lambda__3(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
lean_dec(x_4);
x_5 = l_Lean_Level_Data_hasMVar(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Lean_instReprData___lambda__2(x_1, x_2, x_3, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = l_Lean_instReprData___lambda__3___closed__1;
x_9 = lean_string_append(x_3, x_8);
x_10 = l_Lean_instReprData___lambda__2___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Lean_instReprData___lambda__2___closed__3;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_box(0);
x_15 = l_Lean_instReprData___lambda__2(x_1, x_2, x_13, x_14);
return x_15;
}
}
}
static lean_object* _init_l_Lean_instReprData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Level.mkData ", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_instReprData___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" (depth := ", 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData(uint64_t x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_3 = l_Lean_Level_Data_hash(x_1);
x_4 = lean_uint64_to_nat(x_3);
x_5 = l_Nat_repr(x_4);
x_6 = l_Lean_instReprData___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_Level_Data_depth(x_1);
x_9 = 0;
x_10 = lean_uint32_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = l_Lean_instReprData___closed__2;
x_12 = lean_string_append(x_7, x_11);
x_13 = lean_uint32_to_nat(x_8);
x_14 = l_Nat_repr(x_13);
x_15 = lean_string_append(x_12, x_14);
lean_dec(x_14);
x_16 = l_Lean_instReprData___lambda__2___closed__3;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_box(0);
x_19 = l_Lean_instReprData___lambda__3(x_2, x_1, x_17, x_18);
lean_dec(x_2);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = l_Lean_instReprData___lambda__3(x_2, x_1, x_7, x_20);
lean_dec(x_2);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instReprData___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_6 = l_Lean_instReprData___lambda__2(x_1, x_5, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_6 = l_Lean_instReprData___lambda__3(x_1, x_5, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Lean_instReprData(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_instInhabitedLevelMVarId() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_beqLevelMVarId____x40_Lean_Level___hyg_516_(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_name_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_beqLevelMVarId____x40_Lean_Level___hyg_516____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Level_0__Lean_beqLevelMVarId____x40_Lean_Level___hyg_516_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instBEqLevelMVarId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Level_0__Lean_beqLevelMVarId____x40_Lean_Level___hyg_516____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instBEqLevelMVarId() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instBEqLevelMVarId___closed__1;
return x_1;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Level_0__Lean_hashLevelMVarId____x40_Lean_Level___hyg_589_(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; 
x_2 = 0;
x_3 = l_Lean_Name_hash___override(x_1);
x_4 = lean_uint64_mix_hash(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_hashLevelMVarId____x40_Lean_Level___hyg_589____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Level_0__Lean_hashLevelMVarId____x40_Lean_Level___hyg_589_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instHashableLevelMVarId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Level_0__Lean_hashLevelMVarId____x40_Lean_Level___hyg_589____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instHashableLevelMVarId() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instHashableLevelMVarId___closed__1;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("name", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__2;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" := ", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__3;
x_2 = l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__5;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("{ ", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__8;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__9;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" }", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__12;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Name_reprPrec(x_1, x_3);
x_5 = l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__7;
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = 0;
x_8 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_7);
x_9 = l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__6;
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__11;
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__13;
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__10;
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_7);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instReprLevelMVarId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instReprLevelMVarId() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instReprLevelMVarId___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLMVarId(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Name_reprPrec(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLMVarId___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instReprLMVarId(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instLMVarIdSetInhabited() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_instLMVarIdSetEmptyCollection() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_instForInLMVarIdSetLMVarId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instForInLMVarIdSetLMVarId___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instForInLMVarIdSetLMVarId___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_RBTree_forIn___boxed), 4, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
lean_closure_set(x_2, 2, lean_box(0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instForInLMVarIdSetLMVarId___closed__2;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lean_instForInLMVarIdMapProdLMVarId___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instForInLMVarIdSetLMVarId___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_RBMap_instForInRBMapProd___boxed), 5, 4);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
lean_closure_set(x_2, 3, lean_box(0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarId(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instForInLMVarIdMapProdLMVarId___closed__1;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedLMVarIdMap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_2(x_4, x_10, x_11);
return x_12;
}
case 3:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_apply_2(x_5, x_13, x_14);
return x_15;
}
case 4:
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_apply_1(x_6, x_16);
return x_17;
}
default: 
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_apply_1(x_7, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Level_casesOn___override___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Level_casesOn___override___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Level_zero___override() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_succ___override(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; uint32_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; uint64_t x_14; lean_object* x_15; 
x_2 = 2243;
x_3 = l_Lean_Level_data___override(x_1);
x_4 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_5 = l_Lean_Level_Data_hash(x_4);
x_6 = lean_uint64_mix_hash(x_2, x_5);
x_7 = l_Lean_Level_Data_depth(x_4);
x_8 = lean_uint32_to_nat(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_8, x_9);
lean_dec(x_8);
x_11 = l_Lean_Level_Data_hasMVar(x_4);
x_12 = l_Lean_Level_Data_hasParam(x_4);
x_13 = l_Lean_Level_mkData(x_6, x_10, x_11, x_12);
lean_dec(x_10);
x_14 = lean_unbox_uint64(x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set_uint64(x_15, sizeof(void*)*1, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_max___override(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint32_t x_12; lean_object* x_13; uint32_t x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; 
x_3 = 2251;
x_4 = l_Lean_Level_data___override(x_1);
x_5 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_6 = l_Lean_Level_Data_hash(x_5);
x_7 = l_Lean_Level_data___override(x_2);
x_8 = lean_unbox_uint64(x_7);
lean_dec(x_7);
x_9 = l_Lean_Level_Data_hash(x_8);
x_10 = lean_uint64_mix_hash(x_6, x_9);
x_11 = lean_uint64_mix_hash(x_3, x_10);
x_12 = l_Lean_Level_Data_depth(x_5);
x_13 = lean_uint32_to_nat(x_12);
x_14 = l_Lean_Level_Data_depth(x_8);
x_15 = lean_uint32_to_nat(x_14);
x_16 = lean_nat_dec_le(x_13, x_15);
x_17 = l_Lean_Level_Data_hasMVar(x_5);
x_18 = l_Lean_Level_Data_hasParam(x_5);
if (x_16 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_13, x_19);
lean_dec(x_13);
if (x_17 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Level_Data_hasMVar(x_8);
if (x_18 == 0)
{
uint8_t x_22; lean_object* x_23; uint64_t x_24; lean_object* x_25; 
x_22 = l_Lean_Level_Data_hasParam(x_8);
x_23 = l_Lean_Level_mkData(x_11, x_20, x_21, x_22);
lean_dec(x_20);
x_24 = lean_unbox_uint64(x_23);
lean_dec(x_23);
x_25 = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_2);
lean_ctor_set_uint64(x_25, sizeof(void*)*2, x_24);
return x_25;
}
else
{
uint8_t x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; 
x_26 = 1;
x_27 = l_Lean_Level_mkData(x_11, x_20, x_21, x_26);
lean_dec(x_20);
x_28 = lean_unbox_uint64(x_27);
lean_dec(x_27);
x_29 = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_2);
lean_ctor_set_uint64(x_29, sizeof(void*)*2, x_28);
return x_29;
}
}
else
{
if (x_18 == 0)
{
uint8_t x_30; uint8_t x_31; lean_object* x_32; uint64_t x_33; lean_object* x_34; 
x_30 = l_Lean_Level_Data_hasParam(x_8);
x_31 = 1;
x_32 = l_Lean_Level_mkData(x_11, x_20, x_31, x_30);
lean_dec(x_20);
x_33 = lean_unbox_uint64(x_32);
lean_dec(x_32);
x_34 = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_2);
lean_ctor_set_uint64(x_34, sizeof(void*)*2, x_33);
return x_34;
}
else
{
uint8_t x_35; lean_object* x_36; uint64_t x_37; lean_object* x_38; 
x_35 = 1;
x_36 = l_Lean_Level_mkData(x_11, x_20, x_35, x_35);
lean_dec(x_20);
x_37 = lean_unbox_uint64(x_36);
lean_dec(x_36);
x_38 = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_2);
lean_ctor_set_uint64(x_38, sizeof(void*)*2, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_13);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_15, x_39);
lean_dec(x_15);
if (x_17 == 0)
{
uint8_t x_41; 
x_41 = l_Lean_Level_Data_hasMVar(x_8);
if (x_18 == 0)
{
uint8_t x_42; lean_object* x_43; uint64_t x_44; lean_object* x_45; 
x_42 = l_Lean_Level_Data_hasParam(x_8);
x_43 = l_Lean_Level_mkData(x_11, x_40, x_41, x_42);
lean_dec(x_40);
x_44 = lean_unbox_uint64(x_43);
lean_dec(x_43);
x_45 = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_2);
lean_ctor_set_uint64(x_45, sizeof(void*)*2, x_44);
return x_45;
}
else
{
uint8_t x_46; lean_object* x_47; uint64_t x_48; lean_object* x_49; 
x_46 = 1;
x_47 = l_Lean_Level_mkData(x_11, x_40, x_41, x_46);
lean_dec(x_40);
x_48 = lean_unbox_uint64(x_47);
lean_dec(x_47);
x_49 = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_2);
lean_ctor_set_uint64(x_49, sizeof(void*)*2, x_48);
return x_49;
}
}
else
{
if (x_18 == 0)
{
uint8_t x_50; uint8_t x_51; lean_object* x_52; uint64_t x_53; lean_object* x_54; 
x_50 = l_Lean_Level_Data_hasParam(x_8);
x_51 = 1;
x_52 = l_Lean_Level_mkData(x_11, x_40, x_51, x_50);
lean_dec(x_40);
x_53 = lean_unbox_uint64(x_52);
lean_dec(x_52);
x_54 = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(x_54, 0, x_1);
lean_ctor_set(x_54, 1, x_2);
lean_ctor_set_uint64(x_54, sizeof(void*)*2, x_53);
return x_54;
}
else
{
uint8_t x_55; lean_object* x_56; uint64_t x_57; lean_object* x_58; 
x_55 = 1;
x_56 = l_Lean_Level_mkData(x_11, x_40, x_55, x_55);
lean_dec(x_40);
x_57 = lean_unbox_uint64(x_56);
lean_dec(x_56);
x_58 = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(x_58, 0, x_1);
lean_ctor_set(x_58, 1, x_2);
lean_ctor_set_uint64(x_58, sizeof(void*)*2, x_57);
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_imax___override(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint32_t x_12; lean_object* x_13; uint32_t x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; 
x_3 = 2267;
x_4 = l_Lean_Level_data___override(x_1);
x_5 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_6 = l_Lean_Level_Data_hash(x_5);
x_7 = l_Lean_Level_data___override(x_2);
x_8 = lean_unbox_uint64(x_7);
lean_dec(x_7);
x_9 = l_Lean_Level_Data_hash(x_8);
x_10 = lean_uint64_mix_hash(x_6, x_9);
x_11 = lean_uint64_mix_hash(x_3, x_10);
x_12 = l_Lean_Level_Data_depth(x_5);
x_13 = lean_uint32_to_nat(x_12);
x_14 = l_Lean_Level_Data_depth(x_8);
x_15 = lean_uint32_to_nat(x_14);
x_16 = lean_nat_dec_le(x_13, x_15);
x_17 = l_Lean_Level_Data_hasMVar(x_5);
x_18 = l_Lean_Level_Data_hasParam(x_5);
if (x_16 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_13, x_19);
lean_dec(x_13);
if (x_17 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Level_Data_hasMVar(x_8);
if (x_18 == 0)
{
uint8_t x_22; lean_object* x_23; uint64_t x_24; lean_object* x_25; 
x_22 = l_Lean_Level_Data_hasParam(x_8);
x_23 = l_Lean_Level_mkData(x_11, x_20, x_21, x_22);
lean_dec(x_20);
x_24 = lean_unbox_uint64(x_23);
lean_dec(x_23);
x_25 = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_2);
lean_ctor_set_uint64(x_25, sizeof(void*)*2, x_24);
return x_25;
}
else
{
uint8_t x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; 
x_26 = 1;
x_27 = l_Lean_Level_mkData(x_11, x_20, x_21, x_26);
lean_dec(x_20);
x_28 = lean_unbox_uint64(x_27);
lean_dec(x_27);
x_29 = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_2);
lean_ctor_set_uint64(x_29, sizeof(void*)*2, x_28);
return x_29;
}
}
else
{
if (x_18 == 0)
{
uint8_t x_30; uint8_t x_31; lean_object* x_32; uint64_t x_33; lean_object* x_34; 
x_30 = l_Lean_Level_Data_hasParam(x_8);
x_31 = 1;
x_32 = l_Lean_Level_mkData(x_11, x_20, x_31, x_30);
lean_dec(x_20);
x_33 = lean_unbox_uint64(x_32);
lean_dec(x_32);
x_34 = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_2);
lean_ctor_set_uint64(x_34, sizeof(void*)*2, x_33);
return x_34;
}
else
{
uint8_t x_35; lean_object* x_36; uint64_t x_37; lean_object* x_38; 
x_35 = 1;
x_36 = l_Lean_Level_mkData(x_11, x_20, x_35, x_35);
lean_dec(x_20);
x_37 = lean_unbox_uint64(x_36);
lean_dec(x_36);
x_38 = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_2);
lean_ctor_set_uint64(x_38, sizeof(void*)*2, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_13);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_15, x_39);
lean_dec(x_15);
if (x_17 == 0)
{
uint8_t x_41; 
x_41 = l_Lean_Level_Data_hasMVar(x_8);
if (x_18 == 0)
{
uint8_t x_42; lean_object* x_43; uint64_t x_44; lean_object* x_45; 
x_42 = l_Lean_Level_Data_hasParam(x_8);
x_43 = l_Lean_Level_mkData(x_11, x_40, x_41, x_42);
lean_dec(x_40);
x_44 = lean_unbox_uint64(x_43);
lean_dec(x_43);
x_45 = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_2);
lean_ctor_set_uint64(x_45, sizeof(void*)*2, x_44);
return x_45;
}
else
{
uint8_t x_46; lean_object* x_47; uint64_t x_48; lean_object* x_49; 
x_46 = 1;
x_47 = l_Lean_Level_mkData(x_11, x_40, x_41, x_46);
lean_dec(x_40);
x_48 = lean_unbox_uint64(x_47);
lean_dec(x_47);
x_49 = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_2);
lean_ctor_set_uint64(x_49, sizeof(void*)*2, x_48);
return x_49;
}
}
else
{
if (x_18 == 0)
{
uint8_t x_50; uint8_t x_51; lean_object* x_52; uint64_t x_53; lean_object* x_54; 
x_50 = l_Lean_Level_Data_hasParam(x_8);
x_51 = 1;
x_52 = l_Lean_Level_mkData(x_11, x_40, x_51, x_50);
lean_dec(x_40);
x_53 = lean_unbox_uint64(x_52);
lean_dec(x_52);
x_54 = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(x_54, 0, x_1);
lean_ctor_set(x_54, 1, x_2);
lean_ctor_set_uint64(x_54, sizeof(void*)*2, x_53);
return x_54;
}
else
{
uint8_t x_55; lean_object* x_56; uint64_t x_57; lean_object* x_58; 
x_55 = 1;
x_56 = l_Lean_Level_mkData(x_11, x_40, x_55, x_55);
lean_dec(x_40);
x_57 = lean_unbox_uint64(x_56);
lean_dec(x_56);
x_58 = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(x_58, 0, x_1);
lean_ctor_set(x_58, 1, x_2);
lean_ctor_set_uint64(x_58, sizeof(void*)*2, x_57);
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_param___override(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; 
x_2 = 2239;
x_3 = l_Lean_Name_hash___override(x_1);
x_4 = lean_uint64_mix_hash(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = 0;
x_7 = 1;
x_8 = l_Lean_Level_mkData(x_4, x_5, x_6, x_7);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = lean_alloc_ctor(4, 1, 8);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set_uint64(x_10, sizeof(void*)*1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvar___override(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; 
x_2 = 2237;
x_3 = l___private_Lean_Level_0__Lean_hashLevelMVarId____x40_Lean_Level___hyg_589_(x_1);
x_4 = lean_uint64_mix_hash(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = 1;
x_7 = 0;
x_8 = l_Lean_Level_mkData(x_4, x_5, x_6, x_7);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = lean_alloc_ctor(5, 1, 8);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set_uint64(x_10, sizeof(void*)*1, x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_Level_data___override___closed__1() {
_start:
{
uint64_t x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = 2221;
x_2 = lean_unsigned_to_nat(0u);
x_3 = 0;
x_4 = l_Lean_Level_mkData(x_1, x_2, x_3, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_data___override(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_Level_data___override___closed__1;
return x_2;
}
case 2:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
case 3:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_6 = lean_box_uint64(x_5);
return x_6;
}
default: 
{
uint64_t x_7; lean_object* x_8; 
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_8 = lean_box_uint64(x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_data___override___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_data___override(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedLevel() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Level.zero", 15);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__3;
x_2 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__2;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__4;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__6;
x_2 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__2;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__8() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__7;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Level.succ", 15);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__9;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__10;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Level.max", 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__12;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__13;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Level.imax", 15);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__15;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__16;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Level.param", 16);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__18;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__19;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Level.mvar", 15);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__21;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__22;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222_(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(1024u);
x_4 = lean_nat_dec_le(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__5;
x_6 = l_Repr_addAppParen(x_5, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__8;
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
}
case 1:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(1024u);
x_11 = lean_nat_dec_le(x_10, x_2);
x_12 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222_(x_9, x_10);
x_13 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__11;
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
if (x_11 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_15 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__3;
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = 0;
x_18 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
x_19 = l_Repr_addAppParen(x_18, x_2);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_20 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__6;
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_14);
x_22 = 0;
x_23 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_22);
x_24 = l_Repr_addAppParen(x_23, x_2);
return x_24;
}
}
case 2:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_unsigned_to_nat(1024u);
x_28 = lean_nat_dec_le(x_27, x_2);
x_29 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222_(x_25, x_27);
x_30 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__14;
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_box(1);
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222_(x_26, x_27);
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
if (x_28 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_36 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__3;
x_37 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = 0;
x_39 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_38);
x_40 = l_Repr_addAppParen(x_39, x_2);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_41 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__6;
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_35);
x_43 = 0;
x_44 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_43);
x_45 = l_Repr_addAppParen(x_44, x_2);
return x_45;
}
}
case 3:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_46 = lean_ctor_get(x_1, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_1, 1);
lean_inc(x_47);
lean_dec(x_1);
x_48 = lean_unsigned_to_nat(1024u);
x_49 = lean_nat_dec_le(x_48, x_2);
x_50 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222_(x_46, x_48);
x_51 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__17;
x_52 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = lean_box(1);
x_54 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222_(x_47, x_48);
x_56 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
if (x_49 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
x_57 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__3;
x_58 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = 0;
x_60 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_59);
x_61 = l_Repr_addAppParen(x_60, x_2);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; 
x_62 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__6;
x_63 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_56);
x_64 = 0;
x_65 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_64);
x_66 = l_Repr_addAppParen(x_65, x_2);
return x_66;
}
}
case 4:
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_1, 0);
lean_inc(x_67);
lean_dec(x_1);
x_68 = lean_unsigned_to_nat(1024u);
x_69 = lean_nat_dec_le(x_68, x_2);
x_70 = l_Lean_Name_reprPrec(x_67, x_68);
x_71 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__20;
x_72 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
if (x_69 == 0)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; 
x_73 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__3;
x_74 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = 0;
x_76 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_75);
x_77 = l_Repr_addAppParen(x_76, x_2);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; 
x_78 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__6;
x_79 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_72);
x_80 = 0;
x_81 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set_uint8(x_81, sizeof(void*)*1, x_80);
x_82 = l_Repr_addAppParen(x_81, x_2);
return x_82;
}
}
default: 
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_1, 0);
lean_inc(x_83);
lean_dec(x_1);
x_84 = lean_unsigned_to_nat(1024u);
x_85 = lean_nat_dec_le(x_84, x_2);
x_86 = l_Lean_Name_reprPrec(x_83, x_84);
x_87 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__23;
x_88 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
if (x_85 == 0)
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; 
x_89 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__3;
x_90 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
x_91 = 0;
x_92 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_91);
x_93 = l_Repr_addAppParen(x_92, x_2);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; 
x_94 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__6;
x_95 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_88);
x_96 = 0;
x_97 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set_uint8(x_97, sizeof(void*)*1, x_96);
x_98 = l_Repr_addAppParen(x_97, x_2);
return x_98;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instReprLevel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instReprLevel() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instReprLevel___closed__1;
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lean_Level_hash(lean_object* x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; uint64_t x_4; 
x_2 = l_Lean_Level_data___override(x_1);
x_3 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_4 = l_Lean_Level_Data_hash(x_3);
return x_4;
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
lean_object* x_2; uint64_t x_3; uint32_t x_4; lean_object* x_5; 
x_2 = l_Lean_Level_data___override(x_1);
x_3 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_4 = l_Lean_Level_Data_depth(x_3);
x_5 = lean_uint32_to_nat(x_4);
return x_5;
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
lean_object* x_2; uint64_t x_3; uint8_t x_4; 
x_2 = l_Lean_Level_data___override(x_1);
x_3 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_4 = l_Lean_Level_Data_hasMVar(x_3);
return x_4;
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
lean_object* x_2; uint64_t x_3; uint8_t x_4; 
x_2 = l_Lean_Level_data___override(x_1);
x_3 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_4 = l_Lean_Level_Data_hasParam(x_3);
return x_4;
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
x_3 = lean_uint64_to_uint32(x_2);
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
lean_object* x_2; uint64_t x_3; uint32_t x_4; 
x_2 = l_Lean_Level_data___override(x_1);
lean_dec(x_1);
x_3 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_4 = l_Lean_Level_Data_depth(x_3);
return x_4;
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
static lean_object* _init_l_Lean_levelZero() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelMVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_mvar___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelParam(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_param___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelSucc(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_succ___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelMax(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Level_max___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelIMax(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Level_imax___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_levelOne___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Level_succ___override(x_1);
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
x_2 = l_Lean_Level_succ___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_level_mk_mvar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_mvar___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_level_mk_param(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_param___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_level_mk_max(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Level_max___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_level_mk_imax(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Level_imax___override(x_1, x_2);
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
LEAN_EXPORT lean_object* l_panic___at_Lean_Level_mvarId_x21___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedLevelMVarId;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Level_mvarId_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Level.mvarId!", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_mvarId_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("metavariable expected", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_mvarId_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Level_mkData___closed__2;
x_2 = l_Lean_Level_mvarId_x21___closed__1;
x_3 = lean_unsigned_to_nat(192u);
x_4 = lean_unsigned_to_nat(19u);
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
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
lean_dec(x_1);
x_3 = l_Lean_Level_mvarId_x21___closed__3;
x_4 = l_panic___at_Lean_Level_mvarId_x21___spec__1(x_3);
return x_4;
}
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
x_7 = l_Lean_Level_succ___override(x_6);
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
x_7 = l_Lean_Level_succ___override(x_2);
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
switch (lean_obj_tag(x_3)) {
case 0:
{
uint8_t x_5; 
x_5 = lean_level_eq(x_3, x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
lean_dec(x_4);
lean_dec(x_2);
x_6 = l_Lean_Level_ctorToNat(x_3);
x_7 = lean_nat_dec_lt(x_6, x_6);
lean_dec(x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
case 1:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_3 = x_9;
x_4 = x_11;
goto _start;
}
default: 
{
uint8_t x_13; 
x_13 = lean_level_eq(x_1, x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_4);
lean_dec(x_2);
x_14 = l_Lean_Level_ctorToNat(x_1);
x_15 = l_Lean_Level_ctorToNat(x_3);
x_16 = lean_nat_dec_lt(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_17;
}
}
}
}
case 1:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_1 = x_18;
x_2 = x_20;
goto _start;
}
case 2:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
x_3 = x_22;
x_4 = x_24;
goto _start;
}
case 2:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
x_28 = lean_ctor_get(x_3, 0);
x_29 = lean_ctor_get(x_3, 1);
x_30 = lean_level_eq(x_1, x_3);
if (x_30 == 0)
{
uint8_t x_31; 
lean_dec(x_4);
lean_dec(x_2);
x_31 = lean_level_eq(x_26, x_28);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_unsigned_to_nat(0u);
x_1 = x_26;
x_2 = x_32;
x_3 = x_28;
x_4 = x_32;
goto _start;
}
else
{
lean_object* x_34; 
x_34 = lean_unsigned_to_nat(0u);
x_1 = x_27;
x_2 = x_34;
x_3 = x_29;
x_4 = x_34;
goto _start;
}
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_36;
}
}
default: 
{
uint8_t x_37; 
x_37 = lean_level_eq(x_1, x_3);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_4);
lean_dec(x_2);
x_38 = l_Lean_Level_ctorToNat(x_1);
x_39 = l_Lean_Level_ctorToNat(x_3);
x_40 = lean_nat_dec_lt(x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
return x_40;
}
else
{
uint8_t x_41; 
x_41 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_41;
}
}
}
}
case 3:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_3, 0);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_4, x_43);
lean_dec(x_4);
x_3 = x_42;
x_4 = x_44;
goto _start;
}
case 3:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_46 = lean_ctor_get(x_1, 0);
x_47 = lean_ctor_get(x_1, 1);
x_48 = lean_ctor_get(x_3, 0);
x_49 = lean_ctor_get(x_3, 1);
x_50 = lean_level_eq(x_1, x_3);
if (x_50 == 0)
{
uint8_t x_51; 
lean_dec(x_4);
lean_dec(x_2);
x_51 = lean_level_eq(x_46, x_48);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_unsigned_to_nat(0u);
x_1 = x_46;
x_2 = x_52;
x_3 = x_48;
x_4 = x_52;
goto _start;
}
else
{
lean_object* x_54; 
x_54 = lean_unsigned_to_nat(0u);
x_1 = x_47;
x_2 = x_54;
x_3 = x_49;
x_4 = x_54;
goto _start;
}
}
else
{
uint8_t x_56; 
x_56 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_56;
}
}
default: 
{
uint8_t x_57; 
x_57 = lean_level_eq(x_1, x_3);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_4);
lean_dec(x_2);
x_58 = l_Lean_Level_ctorToNat(x_1);
x_59 = l_Lean_Level_ctorToNat(x_3);
x_60 = lean_nat_dec_lt(x_58, x_59);
lean_dec(x_59);
lean_dec(x_58);
return x_60;
}
else
{
uint8_t x_61; 
x_61 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_61;
}
}
}
}
case 4:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_3, 0);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_add(x_4, x_63);
lean_dec(x_4);
x_3 = x_62;
x_4 = x_64;
goto _start;
}
case 4:
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_1, 0);
x_67 = lean_ctor_get(x_3, 0);
x_68 = lean_name_eq(x_66, x_67);
if (x_68 == 0)
{
uint8_t x_69; 
lean_dec(x_4);
lean_dec(x_2);
x_69 = l_Lean_Name_lt(x_66, x_67);
return x_69;
}
else
{
uint8_t x_70; 
x_70 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_70;
}
}
default: 
{
uint8_t x_71; 
x_71 = lean_level_eq(x_1, x_3);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_4);
lean_dec(x_2);
x_72 = l_Lean_Level_ctorToNat(x_1);
x_73 = l_Lean_Level_ctorToNat(x_3);
x_74 = lean_nat_dec_lt(x_72, x_73);
lean_dec(x_73);
lean_dec(x_72);
return x_74;
}
else
{
uint8_t x_75; 
x_75 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_75;
}
}
}
}
default: 
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_3, 0);
x_77 = lean_unsigned_to_nat(1u);
x_78 = lean_nat_add(x_4, x_77);
lean_dec(x_4);
x_3 = x_76;
x_4 = x_78;
goto _start;
}
case 5:
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_80 = lean_ctor_get(x_1, 0);
x_81 = lean_ctor_get(x_3, 0);
x_82 = lean_name_eq(x_80, x_81);
if (x_82 == 0)
{
uint8_t x_83; 
lean_dec(x_4);
lean_dec(x_2);
x_83 = l_Lean_Name_lt(x_80, x_81);
return x_83;
}
else
{
uint8_t x_84; 
x_84 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_84;
}
}
default: 
{
uint8_t x_85; 
x_85 = lean_level_eq(x_1, x_3);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
lean_dec(x_4);
lean_dec(x_2);
x_86 = l_Lean_Level_ctorToNat(x_1);
x_87 = l_Lean_Level_ctorToNat(x_3);
x_88 = lean_nat_dec_lt(x_86, x_87);
lean_dec(x_87);
lean_dec(x_86);
return x_88;
}
else
{
uint8_t x_89; 
x_89 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_89;
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
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
return x_2;
}
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
x_5 = lean_level_eq(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_Lean_Level_imax___override(x_1, x_2);
return x_6;
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
x_6 = l_Lean_Level_max___override(x_1, x_5);
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
LEAN_EXPORT lean_object* l_panic___at_Lean_Level_normalize___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedLevel;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at_Lean_Level_normalize___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
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
x_6 = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at_Lean_Level_normalize___spec__2(x_4, x_2, x_3);
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
static lean_object* _init_l_Array_qsort_sort___at_Lean_Level_normalize___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Level_normLt___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Level_normalize___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = l_Array_qsort_sort___at_Lean_Level_normalize___spec__3___closed__1;
lean_inc(x_2);
x_6 = l_Array_qpartition___rarg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Array_qsort_sort___at_Lean_Level_normalize___spec__3(x_8, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
static lean_object* _init_l_Lean_Level_normalize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Level.normalize", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_normalize___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_normalize___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Level_mkData___closed__2;
x_2 = l_Lean_Level_normalize___closed__1;
x_3 = lean_unsigned_to_nat(383u);
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
lean_dec(x_1);
switch (lean_obj_tag(x_5)) {
case 2:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = 0;
x_9 = l_Lean_Level_normalize___closed__4;
x_10 = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at_Lean_Level_normalize___spec__2(x_6, x_8, x_9);
x_11 = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at_Lean_Level_normalize___spec__2(x_7, x_8, x_10);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_12, x_13);
lean_dec(x_12);
x_15 = l_Array_qsort_sort___at_Lean_Level_normalize___spec__3(x_11, x_3, x_14);
lean_dec(x_14);
x_16 = l___private_Lean_Level_0__Lean_Level_skipExplicit(x_15, x_3);
lean_inc(x_16);
x_17 = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(x_15, x_16);
x_18 = lean_array_get_size(x_15);
if (x_17 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_nat_sub(x_16, x_13);
lean_dec(x_16);
x_20 = lean_nat_dec_lt(x_19, x_18);
lean_dec(x_18);
x_21 = lean_nat_add(x_19, x_13);
if (x_20 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_19);
x_22 = l_Lean_instInhabitedLevel;
x_23 = l___private_Init_Util_0__outOfBounds___rarg(x_22);
x_24 = l_Lean_Level_getLevelOffset(x_23);
x_25 = l_Lean_Level_getOffsetAux(x_23, x_3);
lean_dec(x_23);
x_26 = l_Lean_levelZero;
x_27 = l___private_Lean_Level_0__Lean_Level_mkMaxAux(x_15, x_4, x_21, x_24, x_25, x_26);
lean_dec(x_4);
lean_dec(x_15);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_array_fget(x_15, x_19);
lean_dec(x_19);
x_29 = l_Lean_Level_getLevelOffset(x_28);
x_30 = l_Lean_Level_getOffsetAux(x_28, x_3);
lean_dec(x_28);
x_31 = l_Lean_levelZero;
x_32 = l___private_Lean_Level_0__Lean_Level_mkMaxAux(x_15, x_4, x_21, x_29, x_30, x_31);
lean_dec(x_4);
lean_dec(x_15);
return x_32;
}
}
else
{
uint8_t x_33; lean_object* x_34; 
x_33 = lean_nat_dec_lt(x_16, x_18);
lean_dec(x_18);
x_34 = lean_nat_add(x_16, x_13);
if (x_33 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_16);
x_35 = l_Lean_instInhabitedLevel;
x_36 = l___private_Init_Util_0__outOfBounds___rarg(x_35);
x_37 = l_Lean_Level_getLevelOffset(x_36);
x_38 = l_Lean_Level_getOffsetAux(x_36, x_3);
lean_dec(x_36);
x_39 = l_Lean_levelZero;
x_40 = l___private_Lean_Level_0__Lean_Level_mkMaxAux(x_15, x_4, x_34, x_37, x_38, x_39);
lean_dec(x_4);
lean_dec(x_15);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_array_fget(x_15, x_16);
lean_dec(x_16);
x_42 = l_Lean_Level_getLevelOffset(x_41);
x_43 = l_Lean_Level_getOffsetAux(x_41, x_3);
lean_dec(x_41);
x_44 = l_Lean_levelZero;
x_45 = l___private_Lean_Level_0__Lean_Level_mkMaxAux(x_15, x_4, x_34, x_42, x_43, x_44);
lean_dec(x_4);
lean_dec(x_15);
return x_45;
}
}
}
case 3:
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_5, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_5, 1);
lean_inc(x_47);
lean_dec(x_5);
x_48 = l_Lean_Level_isNeverZero(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = l_Lean_Level_normalize(x_46);
x_50 = l_Lean_Level_normalize(x_47);
x_51 = l___private_Lean_Level_0__Lean_Level_mkIMaxAux(x_49, x_50);
x_52 = l_Lean_Level_addOffsetAux(x_4, x_51);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = l_Lean_Level_max___override(x_46, x_47);
x_54 = l_Lean_Level_normalize(x_53);
x_55 = l_Lean_Level_addOffsetAux(x_4, x_54);
return x_55;
}
}
default: 
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_5);
lean_dec(x_4);
x_56 = l_Lean_Level_normalize___closed__3;
x_57 = l_panic___at_Lean_Level_normalize___spec__1(x_56);
return x_57;
}
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at_Lean_Level_normalize___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at_Lean_Level_normalize___spec__2(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Level_normalize___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at_Lean_Level_normalize___spec__3(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
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
lean_dec(x_2);
lean_dec(x_1);
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
x_13 = l_Lean_Level_max___override(x_8, x_12);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = l_Lean_Level_max___override(x_8, x_14);
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
x_26 = l_Lean_Level_max___override(x_21, x_25);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 0);
lean_inc(x_27);
lean_dec(x_22);
x_28 = l_Lean_Level_max___override(x_21, x_27);
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
x_1 = lean_mk_string_from_bytes("_uniq", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_toResult___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Level_PP_toResult___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Level_PP_toResult___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\?u", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_toResult___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Level_PP_toResult___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
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
x_1 = lean_mk_string_from_bytes("(", 1);
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
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instReprData___lambda__2___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
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
x_4 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
x_5 = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__5;
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__3;
x_8 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = 0;
x_10 = lean_alloc_ctor(6, 1, 1);
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
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(x_4);
x_10 = lean_alloc_ctor(5, 2, 0);
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
x_1 = lean_mk_string_from_bytes("+", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_format___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Level_PP_Result_format___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_format___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("max", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_format___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Level_PP_Result_format___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_format___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("imax", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_format___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Level_PP_Result_format___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
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
x_6 = lean_alloc_ctor(3, 1, 0);
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
x_9 = lean_alloc_ctor(3, 1, 0);
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
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_nat_add(x_15, x_14);
lean_dec(x_15);
x_21 = l_Nat_repr(x_20);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(5, 2, 0);
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
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = 0;
x_31 = lean_alloc_ctor(6, 1, 1);
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
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = 0;
x_38 = lean_alloc_ctor(6, 1, 1);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Level_PP_Result_quote___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_unsigned_to_nat(1024u);
x_9 = l_Lean_Level_PP_Result_quote(x_5, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = l_Lean_SourceInfo_fromRef(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Level", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("addLit", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Level_PP_Result_quote___closed__2;
x_2 = l_Lean_Level_PP_Result_quote___closed__3;
x_3 = l_Lean_Level_PP_Result_quote___closed__4;
x_4 = l_Lean_Level_PP_Result_quote___closed__5;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Level_PP_Result_quote___closed__1;
x_2 = l_Lean_Level_PP_Result_format___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("paren", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Level_PP_Result_quote___closed__2;
x_2 = l_Lean_Level_PP_Result_quote___closed__3;
x_3 = l_Lean_Level_PP_Result_quote___closed__4;
x_4 = l_Lean_Level_PP_Result_quote___closed__8;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Level_PP_Result_quote___closed__1;
x_2 = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Level_PP_Result_quote___closed__1;
x_2 = l_Lean_instReprData___lambda__2___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Level_PP_Result_quote___closed__2;
x_2 = l_Lean_Level_PP_Result_quote___closed__3;
x_3 = l_Lean_Level_PP_Result_quote___closed__4;
x_4 = l_Lean_Level_PP_Result_format___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Level_PP_Result_quote___closed__1;
x_2 = l_Lean_Level_PP_Result_format___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("null", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Level_PP_Result_quote___closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Level_PP_Result_quote___closed__2;
x_2 = l_Lean_Level_PP_Result_quote___closed__3;
x_3 = l_Lean_Level_PP_Result_quote___closed__4;
x_4 = l_Lean_Level_PP_Result_format___closed__5;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Level_PP_Result_quote___closed__1;
x_2 = l_Lean_Level_PP_Result_format___closed__5;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_mk_syntax_ident(x_3);
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Nat_repr(x_5);
x_7 = lean_box(2);
x_8 = l_Lean_Syntax_mkNumLit(x_6, x_7);
return x_8;
}
case 2:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_10, x_13);
lean_dec(x_10);
x_15 = lean_unsigned_to_nat(65u);
x_16 = l_Lean_Level_PP_Result_quote(x_9, x_15);
x_17 = lean_nat_add(x_14, x_13);
lean_dec(x_14);
x_18 = l_Nat_repr(x_17);
x_19 = lean_box(2);
x_20 = l_Lean_Syntax_mkNumLit(x_18, x_19);
x_21 = l_Lean_Level_PP_Result_quote___closed__1;
x_22 = l_Lean_Level_PP_Result_quote___closed__6;
x_23 = l_Lean_Level_PP_Result_quote___closed__7;
x_24 = l_Lean_Syntax_node3(x_21, x_22, x_16, x_23, x_20);
x_25 = lean_nat_dec_lt(x_11, x_2);
if (x_25 == 0)
{
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = l_Lean_Level_PP_Result_quote___closed__9;
x_27 = l_Lean_Level_PP_Result_quote___closed__10;
x_28 = l_Lean_Level_PP_Result_quote___closed__11;
x_29 = l_Lean_Syntax_node3(x_21, x_26, x_27, x_24, x_28);
return x_29;
}
}
else
{
lean_dec(x_10);
x_1 = x_9;
goto _start;
}
}
case 3:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
lean_dec(x_1);
x_32 = l_List_redLength___rarg(x_31);
x_33 = lean_mk_empty_array_with_capacity(x_32);
lean_dec(x_32);
x_34 = l_List_toArrayAux___rarg(x_31, x_33);
x_35 = lean_array_get_size(x_34);
x_36 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_37 = 0;
x_38 = l_Array_mapMUnsafe_map___at_Lean_Level_PP_Result_quote___spec__1(x_36, x_37, x_34);
x_39 = l_Lean_Level_normalize___closed__4;
x_40 = l_Array_append___rarg(x_39, x_38);
x_41 = l_Lean_Level_PP_Result_quote___closed__1;
x_42 = l_Lean_Level_PP_Result_quote___closed__15;
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_40);
x_44 = l_Lean_Level_PP_Result_quote___closed__12;
x_45 = l_Lean_Level_PP_Result_quote___closed__13;
x_46 = l_Lean_Syntax_node2(x_41, x_44, x_45, x_43);
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_nat_dec_lt(x_47, x_2);
if (x_48 == 0)
{
return x_46;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = l_Lean_Level_PP_Result_quote___closed__9;
x_50 = l_Lean_Level_PP_Result_quote___closed__10;
x_51 = l_Lean_Level_PP_Result_quote___closed__11;
x_52 = l_Lean_Syntax_node3(x_41, x_49, x_50, x_46, x_51);
return x_52;
}
}
default: 
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; size_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_53 = lean_ctor_get(x_1, 0);
lean_inc(x_53);
lean_dec(x_1);
x_54 = l_List_redLength___rarg(x_53);
x_55 = lean_mk_empty_array_with_capacity(x_54);
lean_dec(x_54);
x_56 = l_List_toArrayAux___rarg(x_53, x_55);
x_57 = lean_array_get_size(x_56);
x_58 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_59 = 0;
x_60 = l_Array_mapMUnsafe_map___at_Lean_Level_PP_Result_quote___spec__1(x_58, x_59, x_56);
x_61 = l_Lean_Level_normalize___closed__4;
x_62 = l_Array_append___rarg(x_61, x_60);
x_63 = l_Lean_Level_PP_Result_quote___closed__1;
x_64 = l_Lean_Level_PP_Result_quote___closed__15;
x_65 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_65, 2, x_62);
x_66 = l_Lean_Level_PP_Result_quote___closed__16;
x_67 = l_Lean_Level_PP_Result_quote___closed__17;
x_68 = l_Lean_Syntax_node2(x_63, x_66, x_67, x_65);
x_69 = lean_unsigned_to_nat(0u);
x_70 = lean_nat_dec_lt(x_69, x_2);
if (x_70 == 0)
{
return x_68;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = l_Lean_Level_PP_Result_quote___closed__9;
x_72 = l_Lean_Level_PP_Result_quote___closed__10;
x_73 = l_Lean_Level_PP_Result_quote___closed__11;
x_74 = l_Lean_Syntax_node3(x_63, x_71, x_72, x_68, x_73);
return x_74;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Level_PP_Result_quote___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Level_PP_Result_quote___spec__1(x_4, x_5, x_3);
return x_6;
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
LEAN_EXPORT lean_object* l_Lean_Level_instQuoteLevelMkStr1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Level_quote(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_15; uint8_t x_34; 
x_34 = lean_level_eq(x_1, x_2);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = l_Lean_Level_isZero(x_1);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = l_Lean_Level_isZero(x_2);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = l_Lean_Level_isExplicit(x_2);
if (x_37 == 0)
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_1, 0);
x_39 = lean_ctor_get(x_1, 1);
x_40 = lean_level_eq(x_2, x_38);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = lean_level_eq(x_2, x_39);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_box(0);
x_15 = x_42;
goto block_33;
}
else
{
lean_dec(x_3);
lean_inc(x_1);
return x_1;
}
}
else
{
lean_dec(x_3);
lean_inc(x_1);
return x_1;
}
}
else
{
lean_object* x_43; 
x_43 = lean_box(0);
x_15 = x_43;
goto block_33;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_unsigned_to_nat(0u);
x_45 = l_Lean_Level_getOffsetAux(x_2, x_44);
x_46 = l_Lean_Level_getOffsetAux(x_1, x_44);
x_47 = lean_nat_dec_le(x_45, x_46);
lean_dec(x_46);
lean_dec(x_45);
if (x_47 == 0)
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_1, 0);
x_49 = lean_ctor_get(x_1, 1);
x_50 = lean_level_eq(x_2, x_48);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = lean_level_eq(x_2, x_49);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_box(0);
x_15 = x_52;
goto block_33;
}
else
{
lean_dec(x_3);
lean_inc(x_1);
return x_1;
}
}
else
{
lean_dec(x_3);
lean_inc(x_1);
return x_1;
}
}
else
{
lean_object* x_53; 
x_53 = lean_box(0);
x_15 = x_53;
goto block_33;
}
}
else
{
lean_dec(x_3);
lean_inc(x_1);
return x_1;
}
}
}
else
{
lean_dec(x_3);
lean_inc(x_1);
return x_1;
}
}
else
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
else
{
lean_dec(x_3);
lean_inc(x_1);
return x_1;
}
block_14:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_dec(x_4);
x_5 = l_Lean_Level_getLevelOffset(x_1);
x_6 = l_Lean_Level_getLevelOffset(x_2);
x_7 = lean_level_eq(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_3);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Level_getOffsetAux(x_2, x_10);
x_12 = l_Lean_Level_getOffsetAux(x_1, x_10);
x_13 = lean_nat_dec_le(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
block_33:
{
uint8_t x_16; 
lean_dec(x_15);
x_16 = l_Lean_Level_isExplicit(x_1);
if (x_16 == 0)
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_level_eq(x_1, x_17);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = lean_level_eq(x_1, x_18);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_box(0);
x_4 = x_21;
goto block_14;
}
else
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
else
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
else
{
lean_object* x_22; 
x_22 = lean_box(0);
x_4 = x_22;
goto block_14;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_Level_getOffsetAux(x_1, x_23);
x_25 = l_Lean_Level_getOffsetAux(x_2, x_23);
x_26 = lean_nat_dec_le(x_24, x_25);
lean_dec(x_25);
lean_dec(x_24);
if (x_26 == 0)
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_ctor_get(x_2, 1);
x_29 = lean_level_eq(x_1, x_27);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = lean_level_eq(x_1, x_28);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_box(0);
x_4 = x_31;
goto block_14;
}
else
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
else
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
else
{
lean_object* x_32; 
x_32 = lean_box(0);
x_4 = x_32;
goto block_14;
}
}
else
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Level_0__Lean_mkLevelMaxCore(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelMax_x27(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_Level_max___override(x_1, x_2);
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
LEAN_EXPORT lean_object* l_Lean_simpLevelMax_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_13; uint8_t x_32; 
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
x_37 = lean_ctor_get(x_1, 1);
x_38 = lean_level_eq(x_2, x_36);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = lean_level_eq(x_2, x_37);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_box(0);
x_13 = x_40;
goto block_31;
}
else
{
lean_inc(x_1);
return x_1;
}
}
else
{
lean_inc(x_1);
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
x_47 = lean_ctor_get(x_1, 1);
x_48 = lean_level_eq(x_2, x_46);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = lean_level_eq(x_2, x_47);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_box(0);
x_13 = x_50;
goto block_31;
}
else
{
lean_inc(x_1);
return x_1;
}
}
else
{
lean_inc(x_1);
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
lean_inc(x_1);
return x_1;
}
}
}
else
{
lean_inc(x_1);
return x_1;
}
}
else
{
lean_inc(x_2);
return x_2;
}
}
else
{
lean_inc(x_1);
return x_1;
}
block_12:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_dec(x_4);
x_5 = l_Lean_Level_getLevelOffset(x_1);
x_6 = l_Lean_Level_getLevelOffset(x_2);
x_7 = lean_level_eq(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_inc(x_3);
return x_3;
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
lean_inc(x_2);
return x_2;
}
else
{
lean_inc(x_1);
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
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_level_eq(x_1, x_15);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = lean_level_eq(x_1, x_16);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_box(0);
x_4 = x_19;
goto block_12;
}
else
{
lean_inc(x_2);
return x_2;
}
}
else
{
lean_inc(x_2);
return x_2;
}
}
else
{
lean_object* x_20; 
x_20 = lean_box(0);
x_4 = x_20;
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
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_level_eq(x_1, x_25);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = lean_level_eq(x_1, x_26);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_box(0);
x_4 = x_29;
goto block_12;
}
else
{
lean_inc(x_2);
return x_2;
}
}
else
{
lean_inc(x_2);
return x_2;
}
}
else
{
lean_object* x_30; 
x_30 = lean_box(0);
x_4 = x_30;
goto block_12;
}
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelMax_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_simpLevelMax_x27(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelIMaxCore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Level_isNeverZero(x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Lean_Level_isZero(x_2);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_Lean_Level_isZero(x_1);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = lean_level_eq(x_1, x_2);
lean_dec(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
else
{
lean_dec(x_3);
return x_1;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = l_Lean_mkLevelMax_x27(x_1, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkLevelIMax_x27(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_Level_imax___override(x_1, x_2);
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
x_8 = l_Lean_mkLevelMax_x27(x_1, x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelIMax_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Level_isNeverZero(x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Lean_Level_isZero(x_2);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_Lean_Level_isZero(x_1);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = lean_level_eq(x_1, x_2);
lean_dec(x_2);
if (x_7 == 0)
{
lean_dec(x_1);
lean_inc(x_3);
return x_3;
}
else
{
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
x_8 = l_Lean_mkLevelMax_x27(x_1, x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelIMax_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_simpLevelIMax_x27(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Level.0.Lean.Level.updateSucc!Impl", 48);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("succ level expected", 19);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Level_mkData___closed__2;
x_2 = l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__1;
x_3 = lean_unsigned_to_nat(534u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_3; size_t x_4; size_t x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ptr_addr(x_3);
x_5 = lean_ptr_addr(x_2);
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_Lean_Level_succ___override(x_2);
return x_7;
}
else
{
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_8 = l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__3;
x_9 = l_panic___at_Lean_Level_normalize___spec__1(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Level.0.Lean.Level.updateMax!Impl", 47);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("max level expected", 18);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Level_mkData___closed__2;
x_2 = l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__1;
x_3 = lean_unsigned_to_nat(545u);
x_4 = lean_unsigned_to_nat(19u);
x_5 = l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ptr_addr(x_4);
x_7 = lean_ptr_addr(x_2);
x_8 = lean_usize_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Lean_mkLevelMax_x27(x_2, x_3);
return x_9;
}
else
{
size_t x_10; size_t x_11; uint8_t x_12; 
x_10 = lean_ptr_addr(x_5);
x_11 = lean_ptr_addr(x_3);
x_12 = lean_usize_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_Lean_mkLevelMax_x27(x_2, x_3);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l_Lean_simpLevelMax_x27(x_2, x_3, x_1);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__3;
x_16 = l_panic___at_Lean_Level_normalize___spec__1(x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Level.0.Lean.Level.updateIMax!Impl", 48);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("imax level expected", 19);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Level_mkData___closed__2;
x_2 = l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__1;
x_3 = lean_unsigned_to_nat(556u);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ptr_addr(x_4);
x_7 = lean_ptr_addr(x_2);
x_8 = lean_usize_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Lean_mkLevelIMax_x27(x_2, x_3);
return x_9;
}
else
{
size_t x_10; size_t x_11; uint8_t x_12; 
x_10 = lean_ptr_addr(x_5);
x_11 = lean_ptr_addr(x_3);
x_12 = lean_usize_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_Lean_mkLevelIMax_x27(x_2, x_3);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l_Lean_simpLevelIMax_x27(x_2, x_3, x_1);
return x_14;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__3;
x_16 = l_panic___at_Lean_Level_normalize___spec__1(x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
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
x_7 = l_Lean_mkLevelMax_x27(x_5, x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_substParams_go(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Lean_Level_hasParam(x_2);
if (x_4 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_5; size_t x_6; size_t x_7; uint8_t x_8; 
lean_inc(x_3);
x_5 = l_Lean_Level_substParams_go(x_1, x_3);
x_6 = lean_ptr_addr(x_3);
lean_dec(x_3);
x_7 = lean_ptr_addr(x_5);
x_8 = lean_usize_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = l_Lean_Level_succ___override(x_5);
return x_9;
}
else
{
lean_dec(x_5);
return x_2;
}
}
}
case 2:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = l_Lean_Level_hasParam(x_2);
if (x_12 == 0)
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; uint8_t x_17; 
lean_inc(x_10);
lean_inc(x_1);
x_13 = l_Lean_Level_substParams_go(x_1, x_10);
lean_inc(x_11);
x_14 = l_Lean_Level_substParams_go(x_1, x_11);
x_15 = lean_ptr_addr(x_10);
lean_dec(x_10);
x_16 = lean_ptr_addr(x_13);
x_17 = lean_usize_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_2);
x_18 = l_Lean_mkLevelMax_x27(x_13, x_14);
return x_18;
}
else
{
size_t x_19; size_t x_20; uint8_t x_21; 
x_19 = lean_ptr_addr(x_11);
lean_dec(x_11);
x_20 = lean_ptr_addr(x_14);
x_21 = lean_usize_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_2);
x_22 = l_Lean_mkLevelMax_x27(x_13, x_14);
return x_22;
}
else
{
lean_object* x_23; 
x_23 = l_Lean_simpLevelMax_x27(x_13, x_14, x_2);
lean_dec(x_2);
lean_dec(x_14);
lean_dec(x_13);
return x_23;
}
}
}
}
case 3:
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
x_26 = l_Lean_Level_hasParam(x_2);
if (x_26 == 0)
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; uint8_t x_31; 
lean_inc(x_24);
lean_inc(x_1);
x_27 = l_Lean_Level_substParams_go(x_1, x_24);
lean_inc(x_25);
x_28 = l_Lean_Level_substParams_go(x_1, x_25);
x_29 = lean_ptr_addr(x_24);
lean_dec(x_24);
x_30 = lean_ptr_addr(x_27);
x_31 = lean_usize_dec_eq(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_25);
lean_dec(x_2);
x_32 = l_Lean_mkLevelIMax_x27(x_27, x_28);
return x_32;
}
else
{
size_t x_33; size_t x_34; uint8_t x_35; 
x_33 = lean_ptr_addr(x_25);
lean_dec(x_25);
x_34 = lean_ptr_addr(x_28);
x_35 = lean_usize_dec_eq(x_33, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_2);
x_36 = l_Lean_mkLevelIMax_x27(x_27, x_28);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = l_Lean_simpLevelIMax_x27(x_27, x_28, x_2);
lean_dec(x_2);
return x_37;
}
}
}
}
case 4:
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_2, 0);
lean_inc(x_38);
x_39 = lean_apply_1(x_1, x_38);
if (lean_obj_tag(x_39) == 0)
{
return x_2;
}
else
{
lean_object* x_40; 
lean_dec(x_2);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
return x_40;
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
LEAN_EXPORT lean_object* l_Lean_Level_substParams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Level_substParams_go(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getParamSubst(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_name_eq(x_6, x_3);
if (x_10 == 0)
{
x_1 = x_7;
x_2 = x_9;
goto _start;
}
else
{
lean_object* x_12; 
lean_inc(x_8);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_8);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getParamSubst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Level_getParamSubst(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Level_getParamSubst___boxed), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = l_Lean_Level_substParams_go(x_4, x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_geq_go(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_level_eq(x_1, x_2);
if (x_3 == 0)
{
switch (lean_obj_tag(x_1)) {
case 1:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_2, 0);
x_1 = x_5;
x_2 = x_6;
goto _start;
}
case 4:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Level_getLevelOffset(x_2);
x_9 = l_Lean_Level_getLevelOffset(x_1);
x_10 = lean_level_eq(x_9, x_8);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_Level_isZero(x_8);
lean_dec(x_8);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Level_getOffsetAux(x_2, x_13);
x_15 = l_Lean_Level_getOffsetAux(x_1, x_13);
x_16 = lean_nat_dec_le(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_8);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Level_getOffsetAux(x_2, x_17);
x_19 = l_Lean_Level_getOffsetAux(x_1, x_17);
x_20 = lean_nat_dec_le(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
return x_20;
}
}
case 5:
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = l_Lean_Level_getLevelOffset(x_2);
x_22 = l_Lean_Level_getLevelOffset(x_1);
x_23 = lean_level_eq(x_22, x_21);
lean_dec(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Level_isZero(x_21);
lean_dec(x_21);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = 0;
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Lean_Level_getOffsetAux(x_2, x_26);
x_28 = l_Lean_Level_getOffsetAux(x_1, x_26);
x_29 = lean_nat_dec_le(x_27, x_28);
lean_dec(x_28);
lean_dec(x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_21);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Lean_Level_getOffsetAux(x_2, x_30);
x_32 = l_Lean_Level_getOffsetAux(x_1, x_30);
x_33 = lean_nat_dec_le(x_31, x_32);
lean_dec(x_32);
lean_dec(x_31);
return x_33;
}
}
default: 
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_2, 0);
x_35 = lean_ctor_get(x_2, 1);
x_36 = l_Lean_Level_geq_go(x_1, x_34);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = 0;
return x_37;
}
else
{
x_2 = x_35;
goto _start;
}
}
}
}
case 2:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_39; 
x_39 = 1;
return x_39;
}
case 2:
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_2, 0);
x_41 = lean_ctor_get(x_2, 1);
x_42 = l_Lean_Level_geq_go(x_1, x_40);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = 0;
return x_43;
}
else
{
x_2 = x_41;
goto _start;
}
}
default: 
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_1, 0);
x_46 = lean_ctor_get(x_1, 1);
x_47 = l_Lean_Level_geq_go(x_45, x_2);
if (x_47 == 0)
{
x_1 = x_46;
goto _start;
}
else
{
uint8_t x_49; 
x_49 = 1;
return x_49;
}
}
}
}
case 3:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_50; 
x_50 = 1;
return x_50;
}
case 2:
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_ctor_get(x_2, 0);
x_52 = lean_ctor_get(x_2, 1);
x_53 = l_Lean_Level_geq_go(x_1, x_51);
if (x_53 == 0)
{
uint8_t x_54; 
x_54 = 0;
return x_54;
}
else
{
x_2 = x_52;
goto _start;
}
}
case 3:
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_2, 0);
x_57 = lean_ctor_get(x_2, 1);
x_58 = l_Lean_Level_geq_go(x_1, x_56);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = 0;
return x_59;
}
else
{
x_2 = x_57;
goto _start;
}
}
default: 
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_1, 1);
x_1 = x_61;
goto _start;
}
}
}
default: 
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_63; 
x_63 = 1;
return x_63;
}
case 2:
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_ctor_get(x_2, 0);
x_65 = lean_ctor_get(x_2, 1);
x_66 = l_Lean_Level_geq_go(x_1, x_64);
if (x_66 == 0)
{
uint8_t x_67; 
x_67 = 0;
return x_67;
}
else
{
x_2 = x_65;
goto _start;
}
}
case 3:
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_2, 0);
x_70 = lean_ctor_get(x_2, 1);
x_71 = l_Lean_Level_geq_go(x_1, x_69);
if (x_71 == 0)
{
uint8_t x_72; 
x_72 = 0;
return x_72;
}
else
{
x_2 = x_70;
goto _start;
}
}
default: 
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = l_Lean_Level_getLevelOffset(x_2);
x_75 = l_Lean_Level_getLevelOffset(x_1);
x_76 = lean_level_eq(x_75, x_74);
lean_dec(x_75);
if (x_76 == 0)
{
uint8_t x_77; 
x_77 = l_Lean_Level_isZero(x_74);
lean_dec(x_74);
if (x_77 == 0)
{
uint8_t x_78; 
x_78 = 0;
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_79 = lean_unsigned_to_nat(0u);
x_80 = l_Lean_Level_getOffsetAux(x_2, x_79);
x_81 = l_Lean_Level_getOffsetAux(x_1, x_79);
x_82 = lean_nat_dec_le(x_80, x_81);
lean_dec(x_81);
lean_dec(x_80);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_dec(x_74);
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Lean_Level_getOffsetAux(x_2, x_83);
x_85 = l_Lean_Level_getOffsetAux(x_1, x_83);
x_86 = lean_nat_dec_le(x_84, x_85);
lean_dec(x_85);
lean_dec(x_84);
return x_86;
}
}
}
}
}
}
else
{
uint8_t x_87; 
x_87 = 1;
return x_87;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_geq_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Level_geq_go(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_geq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Level_normalize(x_1);
x_4 = l_Lean_Level_normalize(x_2);
x_5 = l_Lean_Level_geq_go(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_geq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Level_geq(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_Level_collectMVars___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_14 = l_Lean_RBNode_ins___at_Lean_Level_collectMVars___spec__2(x_9, x_2, x_3);
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
x_17 = l_Lean_RBNode_ins___at_Lean_Level_collectMVars___spec__2(x_12, x_2, x_3);
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
x_24 = l_Lean_RBNode_ins___at_Lean_Level_collectMVars___spec__2(x_19, x_2, x_3);
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
x_29 = l_Lean_RBNode_ins___at_Lean_Level_collectMVars___spec__2(x_22, x_2, x_3);
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
lean_object* x_38; uint8_t x_39; 
x_38 = l_Lean_RBNode_ins___at_Lean_Level_collectMVars___spec__2(x_33, x_2, x_3);
x_39 = lean_ctor_get_uint8(x_38, sizeof(void*)*4);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_38, 3);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_38, 3);
lean_dec(x_43);
x_44 = lean_ctor_get(x_38, 0);
lean_dec(x_44);
lean_ctor_set(x_38, 0, x_41);
x_45 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_45);
return x_1;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_38, 1);
x_47 = lean_ctor_get(x_38, 2);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_38);
x_48 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_48, 2, x_47);
lean_ctor_set(x_48, 3, x_41);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_39);
x_49 = 1;
lean_ctor_set(x_1, 0, x_48);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
uint8_t x_50; 
x_50 = lean_ctor_get_uint8(x_41, sizeof(void*)*4);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_38);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_38, 1);
x_53 = lean_ctor_get(x_38, 2);
x_54 = lean_ctor_get(x_38, 3);
lean_dec(x_54);
x_55 = lean_ctor_get(x_38, 0);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_41);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_62; 
x_57 = lean_ctor_get(x_41, 0);
x_58 = lean_ctor_get(x_41, 1);
x_59 = lean_ctor_get(x_41, 2);
x_60 = lean_ctor_get(x_41, 3);
x_61 = 1;
lean_ctor_set(x_41, 3, x_57);
lean_ctor_set(x_41, 2, x_53);
lean_ctor_set(x_41, 1, x_52);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_61);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_60);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_61);
x_62 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_59);
lean_ctor_set(x_1, 1, x_58);
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_62);
return x_1;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; uint8_t x_69; 
x_63 = lean_ctor_get(x_41, 0);
x_64 = lean_ctor_get(x_41, 1);
x_65 = lean_ctor_get(x_41, 2);
x_66 = lean_ctor_get(x_41, 3);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_41);
x_67 = 1;
x_68 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_68, 0, x_40);
lean_ctor_set(x_68, 1, x_52);
lean_ctor_set(x_68, 2, x_53);
lean_ctor_set(x_68, 3, x_63);
lean_ctor_set_uint8(x_68, sizeof(void*)*4, x_67);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_66);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_67);
x_69 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_65);
lean_ctor_set(x_1, 1, x_64);
lean_ctor_set(x_1, 0, x_68);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
return x_1;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_70 = lean_ctor_get(x_38, 1);
x_71 = lean_ctor_get(x_38, 2);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_38);
x_72 = lean_ctor_get(x_41, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_41, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_41, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_41, 3);
lean_inc(x_75);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 x_76 = x_41;
} else {
 lean_dec_ref(x_41);
 x_76 = lean_box(0);
}
x_77 = 1;
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(1, 4, 1);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_40);
lean_ctor_set(x_78, 1, x_70);
lean_ctor_set(x_78, 2, x_71);
lean_ctor_set(x_78, 3, x_72);
lean_ctor_set_uint8(x_78, sizeof(void*)*4, x_77);
x_79 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_34);
lean_ctor_set(x_79, 2, x_35);
lean_ctor_set(x_79, 3, x_36);
lean_ctor_set_uint8(x_79, sizeof(void*)*4, x_77);
x_80 = 0;
lean_ctor_set(x_1, 3, x_79);
lean_ctor_set(x_1, 2, x_74);
lean_ctor_set(x_1, 1, x_73);
lean_ctor_set(x_1, 0, x_78);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_80);
return x_1;
}
}
else
{
uint8_t x_81; 
lean_free_object(x_1);
x_81 = !lean_is_exclusive(x_41);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_82 = lean_ctor_get(x_41, 3);
lean_dec(x_82);
x_83 = lean_ctor_get(x_41, 2);
lean_dec(x_83);
x_84 = lean_ctor_get(x_41, 1);
lean_dec(x_84);
x_85 = lean_ctor_get(x_41, 0);
lean_dec(x_85);
x_86 = 1;
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_86);
return x_41;
}
else
{
uint8_t x_87; lean_object* x_88; 
lean_dec(x_41);
x_87 = 1;
x_88 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_88, 0, x_38);
lean_ctor_set(x_88, 1, x_34);
lean_ctor_set(x_88, 2, x_35);
lean_ctor_set(x_88, 3, x_36);
lean_ctor_set_uint8(x_88, sizeof(void*)*4, x_87);
return x_88;
}
}
}
}
else
{
uint8_t x_89; 
x_89 = lean_ctor_get_uint8(x_40, sizeof(void*)*4);
if (x_89 == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_38);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_91 = lean_ctor_get(x_38, 1);
x_92 = lean_ctor_get(x_38, 2);
x_93 = lean_ctor_get(x_38, 3);
x_94 = lean_ctor_get(x_38, 0);
lean_dec(x_94);
x_95 = !lean_is_exclusive(x_40);
if (x_95 == 0)
{
uint8_t x_96; uint8_t x_97; 
x_96 = 1;
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_96);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_93);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_96);
x_97 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_92);
lean_ctor_set(x_1, 1, x_91);
lean_ctor_set(x_1, 0, x_40);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_97);
return x_1;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; uint8_t x_104; 
x_98 = lean_ctor_get(x_40, 0);
x_99 = lean_ctor_get(x_40, 1);
x_100 = lean_ctor_get(x_40, 2);
x_101 = lean_ctor_get(x_40, 3);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_40);
x_102 = 1;
x_103 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set(x_103, 1, x_99);
lean_ctor_set(x_103, 2, x_100);
lean_ctor_set(x_103, 3, x_101);
lean_ctor_set_uint8(x_103, sizeof(void*)*4, x_102);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_93);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_102);
x_104 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_92);
lean_ctor_set(x_1, 1, x_91);
lean_ctor_set(x_1, 0, x_103);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_104);
return x_1;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_105 = lean_ctor_get(x_38, 1);
x_106 = lean_ctor_get(x_38, 2);
x_107 = lean_ctor_get(x_38, 3);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_38);
x_108 = lean_ctor_get(x_40, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_40, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_40, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_40, 3);
lean_inc(x_111);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_112 = x_40;
} else {
 lean_dec_ref(x_40);
 x_112 = lean_box(0);
}
x_113 = 1;
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(1, 4, 1);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_108);
lean_ctor_set(x_114, 1, x_109);
lean_ctor_set(x_114, 2, x_110);
lean_ctor_set(x_114, 3, x_111);
lean_ctor_set_uint8(x_114, sizeof(void*)*4, x_113);
x_115 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_115, 0, x_107);
lean_ctor_set(x_115, 1, x_34);
lean_ctor_set(x_115, 2, x_35);
lean_ctor_set(x_115, 3, x_36);
lean_ctor_set_uint8(x_115, sizeof(void*)*4, x_113);
x_116 = 0;
lean_ctor_set(x_1, 3, x_115);
lean_ctor_set(x_1, 2, x_106);
lean_ctor_set(x_1, 1, x_105);
lean_ctor_set(x_1, 0, x_114);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_116);
return x_1;
}
}
else
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_38, 3);
lean_inc(x_117);
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_118; 
lean_free_object(x_1);
x_118 = !lean_is_exclusive(x_40);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_119 = lean_ctor_get(x_40, 3);
lean_dec(x_119);
x_120 = lean_ctor_get(x_40, 2);
lean_dec(x_120);
x_121 = lean_ctor_get(x_40, 1);
lean_dec(x_121);
x_122 = lean_ctor_get(x_40, 0);
lean_dec(x_122);
x_123 = 1;
lean_ctor_set(x_40, 3, x_36);
lean_ctor_set(x_40, 2, x_35);
lean_ctor_set(x_40, 1, x_34);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_123);
return x_40;
}
else
{
uint8_t x_124; lean_object* x_125; 
lean_dec(x_40);
x_124 = 1;
x_125 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_125, 0, x_38);
lean_ctor_set(x_125, 1, x_34);
lean_ctor_set(x_125, 2, x_35);
lean_ctor_set(x_125, 3, x_36);
lean_ctor_set_uint8(x_125, sizeof(void*)*4, x_124);
return x_125;
}
}
else
{
uint8_t x_126; 
x_126 = lean_ctor_get_uint8(x_117, sizeof(void*)*4);
if (x_126 == 0)
{
uint8_t x_127; 
lean_free_object(x_1);
x_127 = !lean_is_exclusive(x_38);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_128 = lean_ctor_get(x_38, 1);
x_129 = lean_ctor_get(x_38, 2);
x_130 = lean_ctor_get(x_38, 3);
lean_dec(x_130);
x_131 = lean_ctor_get(x_38, 0);
lean_dec(x_131);
x_132 = !lean_is_exclusive(x_117);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; uint8_t x_138; 
x_133 = lean_ctor_get(x_117, 0);
x_134 = lean_ctor_get(x_117, 1);
x_135 = lean_ctor_get(x_117, 2);
x_136 = lean_ctor_get(x_117, 3);
x_137 = 1;
lean_inc(x_40);
lean_ctor_set(x_117, 3, x_133);
lean_ctor_set(x_117, 2, x_129);
lean_ctor_set(x_117, 1, x_128);
lean_ctor_set(x_117, 0, x_40);
x_138 = !lean_is_exclusive(x_40);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_139 = lean_ctor_get(x_40, 3);
lean_dec(x_139);
x_140 = lean_ctor_get(x_40, 2);
lean_dec(x_140);
x_141 = lean_ctor_get(x_40, 1);
lean_dec(x_141);
x_142 = lean_ctor_get(x_40, 0);
lean_dec(x_142);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_137);
lean_ctor_set(x_40, 3, x_36);
lean_ctor_set(x_40, 2, x_35);
lean_ctor_set(x_40, 1, x_34);
lean_ctor_set(x_40, 0, x_136);
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_137);
x_143 = 0;
lean_ctor_set(x_38, 3, x_40);
lean_ctor_set(x_38, 2, x_135);
lean_ctor_set(x_38, 1, x_134);
lean_ctor_set(x_38, 0, x_117);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_143);
return x_38;
}
else
{
lean_object* x_144; uint8_t x_145; 
lean_dec(x_40);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_137);
x_144 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_144, 0, x_136);
lean_ctor_set(x_144, 1, x_34);
lean_ctor_set(x_144, 2, x_35);
lean_ctor_set(x_144, 3, x_36);
lean_ctor_set_uint8(x_144, sizeof(void*)*4, x_137);
x_145 = 0;
lean_ctor_set(x_38, 3, x_144);
lean_ctor_set(x_38, 2, x_135);
lean_ctor_set(x_38, 1, x_134);
lean_ctor_set(x_38, 0, x_117);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_145);
return x_38;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_146 = lean_ctor_get(x_117, 0);
x_147 = lean_ctor_get(x_117, 1);
x_148 = lean_ctor_get(x_117, 2);
x_149 = lean_ctor_get(x_117, 3);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_117);
x_150 = 1;
lean_inc(x_40);
x_151 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_151, 0, x_40);
lean_ctor_set(x_151, 1, x_128);
lean_ctor_set(x_151, 2, x_129);
lean_ctor_set(x_151, 3, x_146);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_152 = x_40;
} else {
 lean_dec_ref(x_40);
 x_152 = lean_box(0);
}
lean_ctor_set_uint8(x_151, sizeof(void*)*4, x_150);
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 4, 1);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_149);
lean_ctor_set(x_153, 1, x_34);
lean_ctor_set(x_153, 2, x_35);
lean_ctor_set(x_153, 3, x_36);
lean_ctor_set_uint8(x_153, sizeof(void*)*4, x_150);
x_154 = 0;
lean_ctor_set(x_38, 3, x_153);
lean_ctor_set(x_38, 2, x_148);
lean_ctor_set(x_38, 1, x_147);
lean_ctor_set(x_38, 0, x_151);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_154);
return x_38;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; 
x_155 = lean_ctor_get(x_38, 1);
x_156 = lean_ctor_get(x_38, 2);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_38);
x_157 = lean_ctor_get(x_117, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_117, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_117, 2);
lean_inc(x_159);
x_160 = lean_ctor_get(x_117, 3);
lean_inc(x_160);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 lean_ctor_release(x_117, 2);
 lean_ctor_release(x_117, 3);
 x_161 = x_117;
} else {
 lean_dec_ref(x_117);
 x_161 = lean_box(0);
}
x_162 = 1;
lean_inc(x_40);
if (lean_is_scalar(x_161)) {
 x_163 = lean_alloc_ctor(1, 4, 1);
} else {
 x_163 = x_161;
}
lean_ctor_set(x_163, 0, x_40);
lean_ctor_set(x_163, 1, x_155);
lean_ctor_set(x_163, 2, x_156);
lean_ctor_set(x_163, 3, x_157);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_164 = x_40;
} else {
 lean_dec_ref(x_40);
 x_164 = lean_box(0);
}
lean_ctor_set_uint8(x_163, sizeof(void*)*4, x_162);
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 4, 1);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_160);
lean_ctor_set(x_165, 1, x_34);
lean_ctor_set(x_165, 2, x_35);
lean_ctor_set(x_165, 3, x_36);
lean_ctor_set_uint8(x_165, sizeof(void*)*4, x_162);
x_166 = 0;
x_167 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_167, 0, x_163);
lean_ctor_set(x_167, 1, x_158);
lean_ctor_set(x_167, 2, x_159);
lean_ctor_set(x_167, 3, x_165);
lean_ctor_set_uint8(x_167, sizeof(void*)*4, x_166);
return x_167;
}
}
else
{
uint8_t x_168; 
x_168 = !lean_is_exclusive(x_38);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_169 = lean_ctor_get(x_38, 3);
lean_dec(x_169);
x_170 = lean_ctor_get(x_38, 0);
lean_dec(x_170);
x_171 = !lean_is_exclusive(x_40);
if (x_171 == 0)
{
uint8_t x_172; 
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_126);
x_172 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_172);
return x_1;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_173 = lean_ctor_get(x_40, 0);
x_174 = lean_ctor_get(x_40, 1);
x_175 = lean_ctor_get(x_40, 2);
x_176 = lean_ctor_get(x_40, 3);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_40);
x_177 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_177, 0, x_173);
lean_ctor_set(x_177, 1, x_174);
lean_ctor_set(x_177, 2, x_175);
lean_ctor_set(x_177, 3, x_176);
lean_ctor_set_uint8(x_177, sizeof(void*)*4, x_126);
lean_ctor_set(x_38, 0, x_177);
x_178 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_178);
return x_1;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_179 = lean_ctor_get(x_38, 1);
x_180 = lean_ctor_get(x_38, 2);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_38);
x_181 = lean_ctor_get(x_40, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_40, 1);
lean_inc(x_182);
x_183 = lean_ctor_get(x_40, 2);
lean_inc(x_183);
x_184 = lean_ctor_get(x_40, 3);
lean_inc(x_184);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_185 = x_40;
} else {
 lean_dec_ref(x_40);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 4, 1);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_181);
lean_ctor_set(x_186, 1, x_182);
lean_ctor_set(x_186, 2, x_183);
lean_ctor_set(x_186, 3, x_184);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_126);
x_187 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_179);
lean_ctor_set(x_187, 2, x_180);
lean_ctor_set(x_187, 3, x_117);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_39);
x_188 = 1;
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
}
}
}
}
else
{
uint8_t x_189; 
x_189 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
case 1:
{
uint8_t x_190; 
lean_dec(x_35);
lean_dec(x_34);
x_190 = 1;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_190);
return x_1;
}
default: 
{
lean_object* x_191; uint8_t x_192; 
x_191 = l_Lean_RBNode_ins___at_Lean_Level_collectMVars___spec__2(x_36, x_2, x_3);
x_192 = lean_ctor_get_uint8(x_191, sizeof(void*)*4);
if (x_192 == 0)
{
lean_object* x_193; 
x_193 = lean_ctor_get(x_191, 0);
lean_inc(x_193);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_191, 3);
lean_inc(x_194);
if (lean_obj_tag(x_194) == 0)
{
uint8_t x_195; 
x_195 = !lean_is_exclusive(x_191);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_196 = lean_ctor_get(x_191, 3);
lean_dec(x_196);
x_197 = lean_ctor_get(x_191, 0);
lean_dec(x_197);
lean_ctor_set(x_191, 0, x_194);
x_198 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_198);
return x_1;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_199 = lean_ctor_get(x_191, 1);
x_200 = lean_ctor_get(x_191, 2);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_191);
x_201 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_201, 0, x_194);
lean_ctor_set(x_201, 1, x_199);
lean_ctor_set(x_201, 2, x_200);
lean_ctor_set(x_201, 3, x_194);
lean_ctor_set_uint8(x_201, sizeof(void*)*4, x_192);
x_202 = 1;
lean_ctor_set(x_1, 3, x_201);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_202);
return x_1;
}
}
else
{
uint8_t x_203; 
x_203 = lean_ctor_get_uint8(x_194, sizeof(void*)*4);
if (x_203 == 0)
{
uint8_t x_204; 
x_204 = !lean_is_exclusive(x_191);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_205 = lean_ctor_get(x_191, 1);
x_206 = lean_ctor_get(x_191, 2);
x_207 = lean_ctor_get(x_191, 3);
lean_dec(x_207);
x_208 = lean_ctor_get(x_191, 0);
lean_dec(x_208);
x_209 = !lean_is_exclusive(x_194);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; uint8_t x_215; 
x_210 = lean_ctor_get(x_194, 0);
x_211 = lean_ctor_get(x_194, 1);
x_212 = lean_ctor_get(x_194, 2);
x_213 = lean_ctor_get(x_194, 3);
x_214 = 1;
lean_ctor_set(x_194, 3, x_193);
lean_ctor_set(x_194, 2, x_35);
lean_ctor_set(x_194, 1, x_34);
lean_ctor_set(x_194, 0, x_33);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_214);
lean_ctor_set(x_191, 3, x_213);
lean_ctor_set(x_191, 2, x_212);
lean_ctor_set(x_191, 1, x_211);
lean_ctor_set(x_191, 0, x_210);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_214);
x_215 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_206);
lean_ctor_set(x_1, 1, x_205);
lean_ctor_set(x_1, 0, x_194);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_215);
return x_1;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; lean_object* x_221; uint8_t x_222; 
x_216 = lean_ctor_get(x_194, 0);
x_217 = lean_ctor_get(x_194, 1);
x_218 = lean_ctor_get(x_194, 2);
x_219 = lean_ctor_get(x_194, 3);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_194);
x_220 = 1;
x_221 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_221, 0, x_33);
lean_ctor_set(x_221, 1, x_34);
lean_ctor_set(x_221, 2, x_35);
lean_ctor_set(x_221, 3, x_193);
lean_ctor_set_uint8(x_221, sizeof(void*)*4, x_220);
lean_ctor_set(x_191, 3, x_219);
lean_ctor_set(x_191, 2, x_218);
lean_ctor_set(x_191, 1, x_217);
lean_ctor_set(x_191, 0, x_216);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_220);
x_222 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_206);
lean_ctor_set(x_1, 1, x_205);
lean_ctor_set(x_1, 0, x_221);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_222);
return x_1;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_223 = lean_ctor_get(x_191, 1);
x_224 = lean_ctor_get(x_191, 2);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_191);
x_225 = lean_ctor_get(x_194, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_194, 1);
lean_inc(x_226);
x_227 = lean_ctor_get(x_194, 2);
lean_inc(x_227);
x_228 = lean_ctor_get(x_194, 3);
lean_inc(x_228);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 x_229 = x_194;
} else {
 lean_dec_ref(x_194);
 x_229 = lean_box(0);
}
x_230 = 1;
if (lean_is_scalar(x_229)) {
 x_231 = lean_alloc_ctor(1, 4, 1);
} else {
 x_231 = x_229;
}
lean_ctor_set(x_231, 0, x_33);
lean_ctor_set(x_231, 1, x_34);
lean_ctor_set(x_231, 2, x_35);
lean_ctor_set(x_231, 3, x_193);
lean_ctor_set_uint8(x_231, sizeof(void*)*4, x_230);
x_232 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_232, 0, x_225);
lean_ctor_set(x_232, 1, x_226);
lean_ctor_set(x_232, 2, x_227);
lean_ctor_set(x_232, 3, x_228);
lean_ctor_set_uint8(x_232, sizeof(void*)*4, x_230);
x_233 = 0;
lean_ctor_set(x_1, 3, x_232);
lean_ctor_set(x_1, 2, x_224);
lean_ctor_set(x_1, 1, x_223);
lean_ctor_set(x_1, 0, x_231);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_233);
return x_1;
}
}
else
{
uint8_t x_234; 
lean_free_object(x_1);
x_234 = !lean_is_exclusive(x_194);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_235 = lean_ctor_get(x_194, 3);
lean_dec(x_235);
x_236 = lean_ctor_get(x_194, 2);
lean_dec(x_236);
x_237 = lean_ctor_get(x_194, 1);
lean_dec(x_237);
x_238 = lean_ctor_get(x_194, 0);
lean_dec(x_238);
x_239 = 1;
lean_ctor_set(x_194, 3, x_191);
lean_ctor_set(x_194, 2, x_35);
lean_ctor_set(x_194, 1, x_34);
lean_ctor_set(x_194, 0, x_33);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_239);
return x_194;
}
else
{
uint8_t x_240; lean_object* x_241; 
lean_dec(x_194);
x_240 = 1;
x_241 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_241, 0, x_33);
lean_ctor_set(x_241, 1, x_34);
lean_ctor_set(x_241, 2, x_35);
lean_ctor_set(x_241, 3, x_191);
lean_ctor_set_uint8(x_241, sizeof(void*)*4, x_240);
return x_241;
}
}
}
}
else
{
uint8_t x_242; 
x_242 = lean_ctor_get_uint8(x_193, sizeof(void*)*4);
if (x_242 == 0)
{
uint8_t x_243; 
x_243 = !lean_is_exclusive(x_191);
if (x_243 == 0)
{
lean_object* x_244; uint8_t x_245; 
x_244 = lean_ctor_get(x_191, 0);
lean_dec(x_244);
x_245 = !lean_is_exclusive(x_193);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; uint8_t x_251; 
x_246 = lean_ctor_get(x_193, 0);
x_247 = lean_ctor_get(x_193, 1);
x_248 = lean_ctor_get(x_193, 2);
x_249 = lean_ctor_get(x_193, 3);
x_250 = 1;
lean_ctor_set(x_193, 3, x_246);
lean_ctor_set(x_193, 2, x_35);
lean_ctor_set(x_193, 1, x_34);
lean_ctor_set(x_193, 0, x_33);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_250);
lean_ctor_set(x_191, 0, x_249);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_250);
x_251 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_248);
lean_ctor_set(x_1, 1, x_247);
lean_ctor_set(x_1, 0, x_193);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_251);
return x_1;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; lean_object* x_257; uint8_t x_258; 
x_252 = lean_ctor_get(x_193, 0);
x_253 = lean_ctor_get(x_193, 1);
x_254 = lean_ctor_get(x_193, 2);
x_255 = lean_ctor_get(x_193, 3);
lean_inc(x_255);
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_193);
x_256 = 1;
x_257 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_257, 0, x_33);
lean_ctor_set(x_257, 1, x_34);
lean_ctor_set(x_257, 2, x_35);
lean_ctor_set(x_257, 3, x_252);
lean_ctor_set_uint8(x_257, sizeof(void*)*4, x_256);
lean_ctor_set(x_191, 0, x_255);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_256);
x_258 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_254);
lean_ctor_set(x_1, 1, x_253);
lean_ctor_set(x_1, 0, x_257);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_258);
return x_1;
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_259 = lean_ctor_get(x_191, 1);
x_260 = lean_ctor_get(x_191, 2);
x_261 = lean_ctor_get(x_191, 3);
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_191);
x_262 = lean_ctor_get(x_193, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_193, 1);
lean_inc(x_263);
x_264 = lean_ctor_get(x_193, 2);
lean_inc(x_264);
x_265 = lean_ctor_get(x_193, 3);
lean_inc(x_265);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_266 = x_193;
} else {
 lean_dec_ref(x_193);
 x_266 = lean_box(0);
}
x_267 = 1;
if (lean_is_scalar(x_266)) {
 x_268 = lean_alloc_ctor(1, 4, 1);
} else {
 x_268 = x_266;
}
lean_ctor_set(x_268, 0, x_33);
lean_ctor_set(x_268, 1, x_34);
lean_ctor_set(x_268, 2, x_35);
lean_ctor_set(x_268, 3, x_262);
lean_ctor_set_uint8(x_268, sizeof(void*)*4, x_267);
x_269 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_269, 0, x_265);
lean_ctor_set(x_269, 1, x_259);
lean_ctor_set(x_269, 2, x_260);
lean_ctor_set(x_269, 3, x_261);
lean_ctor_set_uint8(x_269, sizeof(void*)*4, x_267);
x_270 = 0;
lean_ctor_set(x_1, 3, x_269);
lean_ctor_set(x_1, 2, x_264);
lean_ctor_set(x_1, 1, x_263);
lean_ctor_set(x_1, 0, x_268);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_270);
return x_1;
}
}
else
{
lean_object* x_271; 
x_271 = lean_ctor_get(x_191, 3);
lean_inc(x_271);
if (lean_obj_tag(x_271) == 0)
{
uint8_t x_272; 
lean_free_object(x_1);
x_272 = !lean_is_exclusive(x_193);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; 
x_273 = lean_ctor_get(x_193, 3);
lean_dec(x_273);
x_274 = lean_ctor_get(x_193, 2);
lean_dec(x_274);
x_275 = lean_ctor_get(x_193, 1);
lean_dec(x_275);
x_276 = lean_ctor_get(x_193, 0);
lean_dec(x_276);
x_277 = 1;
lean_ctor_set(x_193, 3, x_191);
lean_ctor_set(x_193, 2, x_35);
lean_ctor_set(x_193, 1, x_34);
lean_ctor_set(x_193, 0, x_33);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_277);
return x_193;
}
else
{
uint8_t x_278; lean_object* x_279; 
lean_dec(x_193);
x_278 = 1;
x_279 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_279, 0, x_33);
lean_ctor_set(x_279, 1, x_34);
lean_ctor_set(x_279, 2, x_35);
lean_ctor_set(x_279, 3, x_191);
lean_ctor_set_uint8(x_279, sizeof(void*)*4, x_278);
return x_279;
}
}
else
{
uint8_t x_280; 
x_280 = lean_ctor_get_uint8(x_271, sizeof(void*)*4);
if (x_280 == 0)
{
uint8_t x_281; 
lean_free_object(x_1);
x_281 = !lean_is_exclusive(x_191);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; uint8_t x_284; 
x_282 = lean_ctor_get(x_191, 3);
lean_dec(x_282);
x_283 = lean_ctor_get(x_191, 0);
lean_dec(x_283);
x_284 = !lean_is_exclusive(x_271);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; uint8_t x_290; 
x_285 = lean_ctor_get(x_271, 0);
x_286 = lean_ctor_get(x_271, 1);
x_287 = lean_ctor_get(x_271, 2);
x_288 = lean_ctor_get(x_271, 3);
x_289 = 1;
lean_inc(x_193);
lean_ctor_set(x_271, 3, x_193);
lean_ctor_set(x_271, 2, x_35);
lean_ctor_set(x_271, 1, x_34);
lean_ctor_set(x_271, 0, x_33);
x_290 = !lean_is_exclusive(x_193);
if (x_290 == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_291 = lean_ctor_get(x_193, 3);
lean_dec(x_291);
x_292 = lean_ctor_get(x_193, 2);
lean_dec(x_292);
x_293 = lean_ctor_get(x_193, 1);
lean_dec(x_293);
x_294 = lean_ctor_get(x_193, 0);
lean_dec(x_294);
lean_ctor_set_uint8(x_271, sizeof(void*)*4, x_289);
lean_ctor_set(x_193, 3, x_288);
lean_ctor_set(x_193, 2, x_287);
lean_ctor_set(x_193, 1, x_286);
lean_ctor_set(x_193, 0, x_285);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_289);
x_295 = 0;
lean_ctor_set(x_191, 3, x_193);
lean_ctor_set(x_191, 0, x_271);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_295);
return x_191;
}
else
{
lean_object* x_296; uint8_t x_297; 
lean_dec(x_193);
lean_ctor_set_uint8(x_271, sizeof(void*)*4, x_289);
x_296 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_296, 0, x_285);
lean_ctor_set(x_296, 1, x_286);
lean_ctor_set(x_296, 2, x_287);
lean_ctor_set(x_296, 3, x_288);
lean_ctor_set_uint8(x_296, sizeof(void*)*4, x_289);
x_297 = 0;
lean_ctor_set(x_191, 3, x_296);
lean_ctor_set(x_191, 0, x_271);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_297);
return x_191;
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_298 = lean_ctor_get(x_271, 0);
x_299 = lean_ctor_get(x_271, 1);
x_300 = lean_ctor_get(x_271, 2);
x_301 = lean_ctor_get(x_271, 3);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_298);
lean_dec(x_271);
x_302 = 1;
lean_inc(x_193);
x_303 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_303, 0, x_33);
lean_ctor_set(x_303, 1, x_34);
lean_ctor_set(x_303, 2, x_35);
lean_ctor_set(x_303, 3, x_193);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_304 = x_193;
} else {
 lean_dec_ref(x_193);
 x_304 = lean_box(0);
}
lean_ctor_set_uint8(x_303, sizeof(void*)*4, x_302);
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(1, 4, 1);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_298);
lean_ctor_set(x_305, 1, x_299);
lean_ctor_set(x_305, 2, x_300);
lean_ctor_set(x_305, 3, x_301);
lean_ctor_set_uint8(x_305, sizeof(void*)*4, x_302);
x_306 = 0;
lean_ctor_set(x_191, 3, x_305);
lean_ctor_set(x_191, 0, x_303);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_306);
return x_191;
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; lean_object* x_319; 
x_307 = lean_ctor_get(x_191, 1);
x_308 = lean_ctor_get(x_191, 2);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_191);
x_309 = lean_ctor_get(x_271, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_271, 1);
lean_inc(x_310);
x_311 = lean_ctor_get(x_271, 2);
lean_inc(x_311);
x_312 = lean_ctor_get(x_271, 3);
lean_inc(x_312);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 lean_ctor_release(x_271, 2);
 lean_ctor_release(x_271, 3);
 x_313 = x_271;
} else {
 lean_dec_ref(x_271);
 x_313 = lean_box(0);
}
x_314 = 1;
lean_inc(x_193);
if (lean_is_scalar(x_313)) {
 x_315 = lean_alloc_ctor(1, 4, 1);
} else {
 x_315 = x_313;
}
lean_ctor_set(x_315, 0, x_33);
lean_ctor_set(x_315, 1, x_34);
lean_ctor_set(x_315, 2, x_35);
lean_ctor_set(x_315, 3, x_193);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_316 = x_193;
} else {
 lean_dec_ref(x_193);
 x_316 = lean_box(0);
}
lean_ctor_set_uint8(x_315, sizeof(void*)*4, x_314);
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(1, 4, 1);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_309);
lean_ctor_set(x_317, 1, x_310);
lean_ctor_set(x_317, 2, x_311);
lean_ctor_set(x_317, 3, x_312);
lean_ctor_set_uint8(x_317, sizeof(void*)*4, x_314);
x_318 = 0;
x_319 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_319, 0, x_315);
lean_ctor_set(x_319, 1, x_307);
lean_ctor_set(x_319, 2, x_308);
lean_ctor_set(x_319, 3, x_317);
lean_ctor_set_uint8(x_319, sizeof(void*)*4, x_318);
return x_319;
}
}
else
{
uint8_t x_320; 
x_320 = !lean_is_exclusive(x_191);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; uint8_t x_323; 
x_321 = lean_ctor_get(x_191, 3);
lean_dec(x_321);
x_322 = lean_ctor_get(x_191, 0);
lean_dec(x_322);
x_323 = !lean_is_exclusive(x_193);
if (x_323 == 0)
{
uint8_t x_324; 
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_280);
x_324 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_324);
return x_1;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; 
x_325 = lean_ctor_get(x_193, 0);
x_326 = lean_ctor_get(x_193, 1);
x_327 = lean_ctor_get(x_193, 2);
x_328 = lean_ctor_get(x_193, 3);
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_193);
x_329 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_329, 0, x_325);
lean_ctor_set(x_329, 1, x_326);
lean_ctor_set(x_329, 2, x_327);
lean_ctor_set(x_329, 3, x_328);
lean_ctor_set_uint8(x_329, sizeof(void*)*4, x_280);
lean_ctor_set(x_191, 0, x_329);
x_330 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_330);
return x_1;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; uint8_t x_340; 
x_331 = lean_ctor_get(x_191, 1);
x_332 = lean_ctor_get(x_191, 2);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_191);
x_333 = lean_ctor_get(x_193, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_193, 1);
lean_inc(x_334);
x_335 = lean_ctor_get(x_193, 2);
lean_inc(x_335);
x_336 = lean_ctor_get(x_193, 3);
lean_inc(x_336);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_337 = x_193;
} else {
 lean_dec_ref(x_193);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 4, 1);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_333);
lean_ctor_set(x_338, 1, x_334);
lean_ctor_set(x_338, 2, x_335);
lean_ctor_set(x_338, 3, x_336);
lean_ctor_set_uint8(x_338, sizeof(void*)*4, x_280);
x_339 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_331);
lean_ctor_set(x_339, 2, x_332);
lean_ctor_set(x_339, 3, x_271);
lean_ctor_set_uint8(x_339, sizeof(void*)*4, x_192);
x_340 = 1;
lean_ctor_set(x_1, 3, x_339);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_340);
return x_1;
}
}
}
}
}
}
else
{
uint8_t x_341; 
x_341 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_341);
return x_1;
}
}
}
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; 
x_342 = lean_ctor_get(x_1, 0);
x_343 = lean_ctor_get(x_1, 1);
x_344 = lean_ctor_get(x_1, 2);
x_345 = lean_ctor_get(x_1, 3);
lean_inc(x_345);
lean_inc(x_344);
lean_inc(x_343);
lean_inc(x_342);
lean_dec(x_1);
x_346 = l_Lean_Name_quickCmp(x_2, x_343);
switch (x_346) {
case 0:
{
lean_object* x_347; uint8_t x_348; 
x_347 = l_Lean_RBNode_ins___at_Lean_Level_collectMVars___spec__2(x_342, x_2, x_3);
x_348 = lean_ctor_get_uint8(x_347, sizeof(void*)*4);
if (x_348 == 0)
{
lean_object* x_349; 
x_349 = lean_ctor_get(x_347, 0);
lean_inc(x_349);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; 
x_350 = lean_ctor_get(x_347, 3);
lean_inc(x_350);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; lean_object* x_356; 
x_351 = lean_ctor_get(x_347, 1);
lean_inc(x_351);
x_352 = lean_ctor_get(x_347, 2);
lean_inc(x_352);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_353 = x_347;
} else {
 lean_dec_ref(x_347);
 x_353 = lean_box(0);
}
if (lean_is_scalar(x_353)) {
 x_354 = lean_alloc_ctor(1, 4, 1);
} else {
 x_354 = x_353;
}
lean_ctor_set(x_354, 0, x_350);
lean_ctor_set(x_354, 1, x_351);
lean_ctor_set(x_354, 2, x_352);
lean_ctor_set(x_354, 3, x_350);
lean_ctor_set_uint8(x_354, sizeof(void*)*4, x_348);
x_355 = 1;
x_356 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_356, 0, x_354);
lean_ctor_set(x_356, 1, x_343);
lean_ctor_set(x_356, 2, x_344);
lean_ctor_set(x_356, 3, x_345);
lean_ctor_set_uint8(x_356, sizeof(void*)*4, x_355);
return x_356;
}
else
{
uint8_t x_357; 
x_357 = lean_ctor_get_uint8(x_350, sizeof(void*)*4);
if (x_357 == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; lean_object* x_370; 
x_358 = lean_ctor_get(x_347, 1);
lean_inc(x_358);
x_359 = lean_ctor_get(x_347, 2);
lean_inc(x_359);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_360 = x_347;
} else {
 lean_dec_ref(x_347);
 x_360 = lean_box(0);
}
x_361 = lean_ctor_get(x_350, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_350, 1);
lean_inc(x_362);
x_363 = lean_ctor_get(x_350, 2);
lean_inc(x_363);
x_364 = lean_ctor_get(x_350, 3);
lean_inc(x_364);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_365 = x_350;
} else {
 lean_dec_ref(x_350);
 x_365 = lean_box(0);
}
x_366 = 1;
if (lean_is_scalar(x_365)) {
 x_367 = lean_alloc_ctor(1, 4, 1);
} else {
 x_367 = x_365;
}
lean_ctor_set(x_367, 0, x_349);
lean_ctor_set(x_367, 1, x_358);
lean_ctor_set(x_367, 2, x_359);
lean_ctor_set(x_367, 3, x_361);
lean_ctor_set_uint8(x_367, sizeof(void*)*4, x_366);
if (lean_is_scalar(x_360)) {
 x_368 = lean_alloc_ctor(1, 4, 1);
} else {
 x_368 = x_360;
}
lean_ctor_set(x_368, 0, x_364);
lean_ctor_set(x_368, 1, x_343);
lean_ctor_set(x_368, 2, x_344);
lean_ctor_set(x_368, 3, x_345);
lean_ctor_set_uint8(x_368, sizeof(void*)*4, x_366);
x_369 = 0;
x_370 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_370, 0, x_367);
lean_ctor_set(x_370, 1, x_362);
lean_ctor_set(x_370, 2, x_363);
lean_ctor_set(x_370, 3, x_368);
lean_ctor_set_uint8(x_370, sizeof(void*)*4, x_369);
return x_370;
}
else
{
lean_object* x_371; uint8_t x_372; lean_object* x_373; 
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_371 = x_350;
} else {
 lean_dec_ref(x_350);
 x_371 = lean_box(0);
}
x_372 = 1;
if (lean_is_scalar(x_371)) {
 x_373 = lean_alloc_ctor(1, 4, 1);
} else {
 x_373 = x_371;
}
lean_ctor_set(x_373, 0, x_347);
lean_ctor_set(x_373, 1, x_343);
lean_ctor_set(x_373, 2, x_344);
lean_ctor_set(x_373, 3, x_345);
lean_ctor_set_uint8(x_373, sizeof(void*)*4, x_372);
return x_373;
}
}
}
else
{
uint8_t x_374; 
x_374 = lean_ctor_get_uint8(x_349, sizeof(void*)*4);
if (x_374 == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; lean_object* x_388; 
x_375 = lean_ctor_get(x_347, 1);
lean_inc(x_375);
x_376 = lean_ctor_get(x_347, 2);
lean_inc(x_376);
x_377 = lean_ctor_get(x_347, 3);
lean_inc(x_377);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_378 = x_347;
} else {
 lean_dec_ref(x_347);
 x_378 = lean_box(0);
}
x_379 = lean_ctor_get(x_349, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_349, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_349, 2);
lean_inc(x_381);
x_382 = lean_ctor_get(x_349, 3);
lean_inc(x_382);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_383 = x_349;
} else {
 lean_dec_ref(x_349);
 x_383 = lean_box(0);
}
x_384 = 1;
if (lean_is_scalar(x_383)) {
 x_385 = lean_alloc_ctor(1, 4, 1);
} else {
 x_385 = x_383;
}
lean_ctor_set(x_385, 0, x_379);
lean_ctor_set(x_385, 1, x_380);
lean_ctor_set(x_385, 2, x_381);
lean_ctor_set(x_385, 3, x_382);
lean_ctor_set_uint8(x_385, sizeof(void*)*4, x_384);
if (lean_is_scalar(x_378)) {
 x_386 = lean_alloc_ctor(1, 4, 1);
} else {
 x_386 = x_378;
}
lean_ctor_set(x_386, 0, x_377);
lean_ctor_set(x_386, 1, x_343);
lean_ctor_set(x_386, 2, x_344);
lean_ctor_set(x_386, 3, x_345);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_384);
x_387 = 0;
x_388 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_388, 0, x_385);
lean_ctor_set(x_388, 1, x_375);
lean_ctor_set(x_388, 2, x_376);
lean_ctor_set(x_388, 3, x_386);
lean_ctor_set_uint8(x_388, sizeof(void*)*4, x_387);
return x_388;
}
else
{
lean_object* x_389; 
x_389 = lean_ctor_get(x_347, 3);
lean_inc(x_389);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; uint8_t x_391; lean_object* x_392; 
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_390 = x_349;
} else {
 lean_dec_ref(x_349);
 x_390 = lean_box(0);
}
x_391 = 1;
if (lean_is_scalar(x_390)) {
 x_392 = lean_alloc_ctor(1, 4, 1);
} else {
 x_392 = x_390;
}
lean_ctor_set(x_392, 0, x_347);
lean_ctor_set(x_392, 1, x_343);
lean_ctor_set(x_392, 2, x_344);
lean_ctor_set(x_392, 3, x_345);
lean_ctor_set_uint8(x_392, sizeof(void*)*4, x_391);
return x_392;
}
else
{
uint8_t x_393; 
x_393 = lean_ctor_get_uint8(x_389, sizeof(void*)*4);
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; lean_object* x_407; 
x_394 = lean_ctor_get(x_347, 1);
lean_inc(x_394);
x_395 = lean_ctor_get(x_347, 2);
lean_inc(x_395);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_396 = x_347;
} else {
 lean_dec_ref(x_347);
 x_396 = lean_box(0);
}
x_397 = lean_ctor_get(x_389, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_389, 1);
lean_inc(x_398);
x_399 = lean_ctor_get(x_389, 2);
lean_inc(x_399);
x_400 = lean_ctor_get(x_389, 3);
lean_inc(x_400);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 lean_ctor_release(x_389, 2);
 lean_ctor_release(x_389, 3);
 x_401 = x_389;
} else {
 lean_dec_ref(x_389);
 x_401 = lean_box(0);
}
x_402 = 1;
lean_inc(x_349);
if (lean_is_scalar(x_401)) {
 x_403 = lean_alloc_ctor(1, 4, 1);
} else {
 x_403 = x_401;
}
lean_ctor_set(x_403, 0, x_349);
lean_ctor_set(x_403, 1, x_394);
lean_ctor_set(x_403, 2, x_395);
lean_ctor_set(x_403, 3, x_397);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_404 = x_349;
} else {
 lean_dec_ref(x_349);
 x_404 = lean_box(0);
}
lean_ctor_set_uint8(x_403, sizeof(void*)*4, x_402);
if (lean_is_scalar(x_404)) {
 x_405 = lean_alloc_ctor(1, 4, 1);
} else {
 x_405 = x_404;
}
lean_ctor_set(x_405, 0, x_400);
lean_ctor_set(x_405, 1, x_343);
lean_ctor_set(x_405, 2, x_344);
lean_ctor_set(x_405, 3, x_345);
lean_ctor_set_uint8(x_405, sizeof(void*)*4, x_402);
x_406 = 0;
if (lean_is_scalar(x_396)) {
 x_407 = lean_alloc_ctor(1, 4, 1);
} else {
 x_407 = x_396;
}
lean_ctor_set(x_407, 0, x_403);
lean_ctor_set(x_407, 1, x_398);
lean_ctor_set(x_407, 2, x_399);
lean_ctor_set(x_407, 3, x_405);
lean_ctor_set_uint8(x_407, sizeof(void*)*4, x_406);
return x_407;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; lean_object* x_419; 
x_408 = lean_ctor_get(x_347, 1);
lean_inc(x_408);
x_409 = lean_ctor_get(x_347, 2);
lean_inc(x_409);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_410 = x_347;
} else {
 lean_dec_ref(x_347);
 x_410 = lean_box(0);
}
x_411 = lean_ctor_get(x_349, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_349, 1);
lean_inc(x_412);
x_413 = lean_ctor_get(x_349, 2);
lean_inc(x_413);
x_414 = lean_ctor_get(x_349, 3);
lean_inc(x_414);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_415 = x_349;
} else {
 lean_dec_ref(x_349);
 x_415 = lean_box(0);
}
if (lean_is_scalar(x_415)) {
 x_416 = lean_alloc_ctor(1, 4, 1);
} else {
 x_416 = x_415;
}
lean_ctor_set(x_416, 0, x_411);
lean_ctor_set(x_416, 1, x_412);
lean_ctor_set(x_416, 2, x_413);
lean_ctor_set(x_416, 3, x_414);
lean_ctor_set_uint8(x_416, sizeof(void*)*4, x_393);
if (lean_is_scalar(x_410)) {
 x_417 = lean_alloc_ctor(1, 4, 1);
} else {
 x_417 = x_410;
}
lean_ctor_set(x_417, 0, x_416);
lean_ctor_set(x_417, 1, x_408);
lean_ctor_set(x_417, 2, x_409);
lean_ctor_set(x_417, 3, x_389);
lean_ctor_set_uint8(x_417, sizeof(void*)*4, x_348);
x_418 = 1;
x_419 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_419, 0, x_417);
lean_ctor_set(x_419, 1, x_343);
lean_ctor_set(x_419, 2, x_344);
lean_ctor_set(x_419, 3, x_345);
lean_ctor_set_uint8(x_419, sizeof(void*)*4, x_418);
return x_419;
}
}
}
}
}
else
{
uint8_t x_420; lean_object* x_421; 
x_420 = 1;
x_421 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_421, 0, x_347);
lean_ctor_set(x_421, 1, x_343);
lean_ctor_set(x_421, 2, x_344);
lean_ctor_set(x_421, 3, x_345);
lean_ctor_set_uint8(x_421, sizeof(void*)*4, x_420);
return x_421;
}
}
case 1:
{
uint8_t x_422; lean_object* x_423; 
lean_dec(x_344);
lean_dec(x_343);
x_422 = 1;
x_423 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_423, 0, x_342);
lean_ctor_set(x_423, 1, x_2);
lean_ctor_set(x_423, 2, x_3);
lean_ctor_set(x_423, 3, x_345);
lean_ctor_set_uint8(x_423, sizeof(void*)*4, x_422);
return x_423;
}
default: 
{
lean_object* x_424; uint8_t x_425; 
x_424 = l_Lean_RBNode_ins___at_Lean_Level_collectMVars___spec__2(x_345, x_2, x_3);
x_425 = lean_ctor_get_uint8(x_424, sizeof(void*)*4);
if (x_425 == 0)
{
lean_object* x_426; 
x_426 = lean_ctor_get(x_424, 0);
lean_inc(x_426);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; 
x_427 = lean_ctor_get(x_424, 3);
lean_inc(x_427);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; uint8_t x_432; lean_object* x_433; 
x_428 = lean_ctor_get(x_424, 1);
lean_inc(x_428);
x_429 = lean_ctor_get(x_424, 2);
lean_inc(x_429);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_430 = x_424;
} else {
 lean_dec_ref(x_424);
 x_430 = lean_box(0);
}
if (lean_is_scalar(x_430)) {
 x_431 = lean_alloc_ctor(1, 4, 1);
} else {
 x_431 = x_430;
}
lean_ctor_set(x_431, 0, x_427);
lean_ctor_set(x_431, 1, x_428);
lean_ctor_set(x_431, 2, x_429);
lean_ctor_set(x_431, 3, x_427);
lean_ctor_set_uint8(x_431, sizeof(void*)*4, x_425);
x_432 = 1;
x_433 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_433, 0, x_342);
lean_ctor_set(x_433, 1, x_343);
lean_ctor_set(x_433, 2, x_344);
lean_ctor_set(x_433, 3, x_431);
lean_ctor_set_uint8(x_433, sizeof(void*)*4, x_432);
return x_433;
}
else
{
uint8_t x_434; 
x_434 = lean_ctor_get_uint8(x_427, sizeof(void*)*4);
if (x_434 == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; uint8_t x_443; lean_object* x_444; lean_object* x_445; uint8_t x_446; lean_object* x_447; 
x_435 = lean_ctor_get(x_424, 1);
lean_inc(x_435);
x_436 = lean_ctor_get(x_424, 2);
lean_inc(x_436);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_437 = x_424;
} else {
 lean_dec_ref(x_424);
 x_437 = lean_box(0);
}
x_438 = lean_ctor_get(x_427, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_427, 1);
lean_inc(x_439);
x_440 = lean_ctor_get(x_427, 2);
lean_inc(x_440);
x_441 = lean_ctor_get(x_427, 3);
lean_inc(x_441);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_442 = x_427;
} else {
 lean_dec_ref(x_427);
 x_442 = lean_box(0);
}
x_443 = 1;
if (lean_is_scalar(x_442)) {
 x_444 = lean_alloc_ctor(1, 4, 1);
} else {
 x_444 = x_442;
}
lean_ctor_set(x_444, 0, x_342);
lean_ctor_set(x_444, 1, x_343);
lean_ctor_set(x_444, 2, x_344);
lean_ctor_set(x_444, 3, x_426);
lean_ctor_set_uint8(x_444, sizeof(void*)*4, x_443);
if (lean_is_scalar(x_437)) {
 x_445 = lean_alloc_ctor(1, 4, 1);
} else {
 x_445 = x_437;
}
lean_ctor_set(x_445, 0, x_438);
lean_ctor_set(x_445, 1, x_439);
lean_ctor_set(x_445, 2, x_440);
lean_ctor_set(x_445, 3, x_441);
lean_ctor_set_uint8(x_445, sizeof(void*)*4, x_443);
x_446 = 0;
x_447 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_447, 0, x_444);
lean_ctor_set(x_447, 1, x_435);
lean_ctor_set(x_447, 2, x_436);
lean_ctor_set(x_447, 3, x_445);
lean_ctor_set_uint8(x_447, sizeof(void*)*4, x_446);
return x_447;
}
else
{
lean_object* x_448; uint8_t x_449; lean_object* x_450; 
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_448 = x_427;
} else {
 lean_dec_ref(x_427);
 x_448 = lean_box(0);
}
x_449 = 1;
if (lean_is_scalar(x_448)) {
 x_450 = lean_alloc_ctor(1, 4, 1);
} else {
 x_450 = x_448;
}
lean_ctor_set(x_450, 0, x_342);
lean_ctor_set(x_450, 1, x_343);
lean_ctor_set(x_450, 2, x_344);
lean_ctor_set(x_450, 3, x_424);
lean_ctor_set_uint8(x_450, sizeof(void*)*4, x_449);
return x_450;
}
}
}
else
{
uint8_t x_451; 
x_451 = lean_ctor_get_uint8(x_426, sizeof(void*)*4);
if (x_451 == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; uint8_t x_461; lean_object* x_462; lean_object* x_463; uint8_t x_464; lean_object* x_465; 
x_452 = lean_ctor_get(x_424, 1);
lean_inc(x_452);
x_453 = lean_ctor_get(x_424, 2);
lean_inc(x_453);
x_454 = lean_ctor_get(x_424, 3);
lean_inc(x_454);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_455 = x_424;
} else {
 lean_dec_ref(x_424);
 x_455 = lean_box(0);
}
x_456 = lean_ctor_get(x_426, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_426, 1);
lean_inc(x_457);
x_458 = lean_ctor_get(x_426, 2);
lean_inc(x_458);
x_459 = lean_ctor_get(x_426, 3);
lean_inc(x_459);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_460 = x_426;
} else {
 lean_dec_ref(x_426);
 x_460 = lean_box(0);
}
x_461 = 1;
if (lean_is_scalar(x_460)) {
 x_462 = lean_alloc_ctor(1, 4, 1);
} else {
 x_462 = x_460;
}
lean_ctor_set(x_462, 0, x_342);
lean_ctor_set(x_462, 1, x_343);
lean_ctor_set(x_462, 2, x_344);
lean_ctor_set(x_462, 3, x_456);
lean_ctor_set_uint8(x_462, sizeof(void*)*4, x_461);
if (lean_is_scalar(x_455)) {
 x_463 = lean_alloc_ctor(1, 4, 1);
} else {
 x_463 = x_455;
}
lean_ctor_set(x_463, 0, x_459);
lean_ctor_set(x_463, 1, x_452);
lean_ctor_set(x_463, 2, x_453);
lean_ctor_set(x_463, 3, x_454);
lean_ctor_set_uint8(x_463, sizeof(void*)*4, x_461);
x_464 = 0;
x_465 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_465, 0, x_462);
lean_ctor_set(x_465, 1, x_457);
lean_ctor_set(x_465, 2, x_458);
lean_ctor_set(x_465, 3, x_463);
lean_ctor_set_uint8(x_465, sizeof(void*)*4, x_464);
return x_465;
}
else
{
lean_object* x_466; 
x_466 = lean_ctor_get(x_424, 3);
lean_inc(x_466);
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_467; uint8_t x_468; lean_object* x_469; 
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_467 = x_426;
} else {
 lean_dec_ref(x_426);
 x_467 = lean_box(0);
}
x_468 = 1;
if (lean_is_scalar(x_467)) {
 x_469 = lean_alloc_ctor(1, 4, 1);
} else {
 x_469 = x_467;
}
lean_ctor_set(x_469, 0, x_342);
lean_ctor_set(x_469, 1, x_343);
lean_ctor_set(x_469, 2, x_344);
lean_ctor_set(x_469, 3, x_424);
lean_ctor_set_uint8(x_469, sizeof(void*)*4, x_468);
return x_469;
}
else
{
uint8_t x_470; 
x_470 = lean_ctor_get_uint8(x_466, sizeof(void*)*4);
if (x_470 == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; uint8_t x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; uint8_t x_483; lean_object* x_484; 
x_471 = lean_ctor_get(x_424, 1);
lean_inc(x_471);
x_472 = lean_ctor_get(x_424, 2);
lean_inc(x_472);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_473 = x_424;
} else {
 lean_dec_ref(x_424);
 x_473 = lean_box(0);
}
x_474 = lean_ctor_get(x_466, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_466, 1);
lean_inc(x_475);
x_476 = lean_ctor_get(x_466, 2);
lean_inc(x_476);
x_477 = lean_ctor_get(x_466, 3);
lean_inc(x_477);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 lean_ctor_release(x_466, 2);
 lean_ctor_release(x_466, 3);
 x_478 = x_466;
} else {
 lean_dec_ref(x_466);
 x_478 = lean_box(0);
}
x_479 = 1;
lean_inc(x_426);
if (lean_is_scalar(x_478)) {
 x_480 = lean_alloc_ctor(1, 4, 1);
} else {
 x_480 = x_478;
}
lean_ctor_set(x_480, 0, x_342);
lean_ctor_set(x_480, 1, x_343);
lean_ctor_set(x_480, 2, x_344);
lean_ctor_set(x_480, 3, x_426);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_481 = x_426;
} else {
 lean_dec_ref(x_426);
 x_481 = lean_box(0);
}
lean_ctor_set_uint8(x_480, sizeof(void*)*4, x_479);
if (lean_is_scalar(x_481)) {
 x_482 = lean_alloc_ctor(1, 4, 1);
} else {
 x_482 = x_481;
}
lean_ctor_set(x_482, 0, x_474);
lean_ctor_set(x_482, 1, x_475);
lean_ctor_set(x_482, 2, x_476);
lean_ctor_set(x_482, 3, x_477);
lean_ctor_set_uint8(x_482, sizeof(void*)*4, x_479);
x_483 = 0;
if (lean_is_scalar(x_473)) {
 x_484 = lean_alloc_ctor(1, 4, 1);
} else {
 x_484 = x_473;
}
lean_ctor_set(x_484, 0, x_480);
lean_ctor_set(x_484, 1, x_471);
lean_ctor_set(x_484, 2, x_472);
lean_ctor_set(x_484, 3, x_482);
lean_ctor_set_uint8(x_484, sizeof(void*)*4, x_483);
return x_484;
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; uint8_t x_495; lean_object* x_496; 
x_485 = lean_ctor_get(x_424, 1);
lean_inc(x_485);
x_486 = lean_ctor_get(x_424, 2);
lean_inc(x_486);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_487 = x_424;
} else {
 lean_dec_ref(x_424);
 x_487 = lean_box(0);
}
x_488 = lean_ctor_get(x_426, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_426, 1);
lean_inc(x_489);
x_490 = lean_ctor_get(x_426, 2);
lean_inc(x_490);
x_491 = lean_ctor_get(x_426, 3);
lean_inc(x_491);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_492 = x_426;
} else {
 lean_dec_ref(x_426);
 x_492 = lean_box(0);
}
if (lean_is_scalar(x_492)) {
 x_493 = lean_alloc_ctor(1, 4, 1);
} else {
 x_493 = x_492;
}
lean_ctor_set(x_493, 0, x_488);
lean_ctor_set(x_493, 1, x_489);
lean_ctor_set(x_493, 2, x_490);
lean_ctor_set(x_493, 3, x_491);
lean_ctor_set_uint8(x_493, sizeof(void*)*4, x_470);
if (lean_is_scalar(x_487)) {
 x_494 = lean_alloc_ctor(1, 4, 1);
} else {
 x_494 = x_487;
}
lean_ctor_set(x_494, 0, x_493);
lean_ctor_set(x_494, 1, x_485);
lean_ctor_set(x_494, 2, x_486);
lean_ctor_set(x_494, 3, x_466);
lean_ctor_set_uint8(x_494, sizeof(void*)*4, x_425);
x_495 = 1;
x_496 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_496, 0, x_342);
lean_ctor_set(x_496, 1, x_343);
lean_ctor_set(x_496, 2, x_344);
lean_ctor_set(x_496, 3, x_494);
lean_ctor_set_uint8(x_496, sizeof(void*)*4, x_495);
return x_496;
}
}
}
}
}
else
{
uint8_t x_497; lean_object* x_498; 
x_497 = 1;
x_498 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_498, 0, x_342);
lean_ctor_set(x_498, 1, x_343);
lean_ctor_set(x_498, 2, x_344);
lean_ctor_set(x_498, 3, x_424);
lean_ctor_set_uint8(x_498, sizeof(void*)*4, x_497);
return x_498;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lean_Level_collectMVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at_Lean_Level_collectMVars___spec__2(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_RBNode_ins___at_Lean_Level_collectMVars___spec__2(x_1, x_2, x_3);
x_7 = l_Lean_RBNode_setBlack___rarg(x_6);
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
x_15 = l_Lean_RBNode_insert___at_Lean_Level_collectMVars___spec__1(x_2, x_13, x_14);
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_HashMap(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_HashSet(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_PersistentHashMap(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_PersistentHashSet(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Hygiene(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Name(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Format(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Level(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_HashMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_HashSet(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_PersistentHashMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_PersistentHashSet(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Hygiene(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Name(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Format(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedData = _init_l_Lean_instInhabitedData();
l_panic___at_Lean_Level_mkData___spec__1___boxed__const__1 = _init_l_panic___at_Lean_Level_mkData___spec__1___boxed__const__1();
lean_mark_persistent(l_panic___at_Lean_Level_mkData___spec__1___boxed__const__1);
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
l_Lean_instReprData___lambda__2___closed__1 = _init_l_Lean_instReprData___lambda__2___closed__1();
lean_mark_persistent(l_Lean_instReprData___lambda__2___closed__1);
l_Lean_instReprData___lambda__2___closed__2 = _init_l_Lean_instReprData___lambda__2___closed__2();
lean_mark_persistent(l_Lean_instReprData___lambda__2___closed__2);
l_Lean_instReprData___lambda__2___closed__3 = _init_l_Lean_instReprData___lambda__2___closed__3();
lean_mark_persistent(l_Lean_instReprData___lambda__2___closed__3);
l_Lean_instReprData___lambda__3___closed__1 = _init_l_Lean_instReprData___lambda__3___closed__1();
lean_mark_persistent(l_Lean_instReprData___lambda__3___closed__1);
l_Lean_instReprData___closed__1 = _init_l_Lean_instReprData___closed__1();
lean_mark_persistent(l_Lean_instReprData___closed__1);
l_Lean_instReprData___closed__2 = _init_l_Lean_instReprData___closed__2();
lean_mark_persistent(l_Lean_instReprData___closed__2);
l_Lean_instInhabitedLevelMVarId = _init_l_Lean_instInhabitedLevelMVarId();
lean_mark_persistent(l_Lean_instInhabitedLevelMVarId);
l_Lean_instBEqLevelMVarId___closed__1 = _init_l_Lean_instBEqLevelMVarId___closed__1();
lean_mark_persistent(l_Lean_instBEqLevelMVarId___closed__1);
l_Lean_instBEqLevelMVarId = _init_l_Lean_instBEqLevelMVarId();
lean_mark_persistent(l_Lean_instBEqLevelMVarId);
l_Lean_instHashableLevelMVarId___closed__1 = _init_l_Lean_instHashableLevelMVarId___closed__1();
lean_mark_persistent(l_Lean_instHashableLevelMVarId___closed__1);
l_Lean_instHashableLevelMVarId = _init_l_Lean_instHashableLevelMVarId();
lean_mark_persistent(l_Lean_instHashableLevelMVarId);
l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__1 = _init_l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__1();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__1);
l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__2 = _init_l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__2();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__2);
l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__3 = _init_l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__3();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__3);
l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__4 = _init_l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__4();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__4);
l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__5 = _init_l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__5();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__5);
l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__6 = _init_l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__6();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__6);
l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__7 = _init_l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__7();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__7);
l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__8 = _init_l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__8();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__8);
l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__9 = _init_l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__9();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__9);
l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__10 = _init_l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__10();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__10);
l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__11 = _init_l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__11();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__11);
l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__12 = _init_l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__12();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__12);
l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__13 = _init_l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__13();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevelMVarId____x40_Lean_Level___hyg_627____closed__13);
l_Lean_instReprLevelMVarId___closed__1 = _init_l_Lean_instReprLevelMVarId___closed__1();
lean_mark_persistent(l_Lean_instReprLevelMVarId___closed__1);
l_Lean_instReprLevelMVarId = _init_l_Lean_instReprLevelMVarId();
lean_mark_persistent(l_Lean_instReprLevelMVarId);
l_Lean_instLMVarIdSetInhabited = _init_l_Lean_instLMVarIdSetInhabited();
lean_mark_persistent(l_Lean_instLMVarIdSetInhabited);
l_Lean_instLMVarIdSetEmptyCollection = _init_l_Lean_instLMVarIdSetEmptyCollection();
lean_mark_persistent(l_Lean_instLMVarIdSetEmptyCollection);
l_Lean_instForInLMVarIdSetLMVarId___closed__1 = _init_l_Lean_instForInLMVarIdSetLMVarId___closed__1();
lean_mark_persistent(l_Lean_instForInLMVarIdSetLMVarId___closed__1);
l_Lean_instForInLMVarIdSetLMVarId___closed__2 = _init_l_Lean_instForInLMVarIdSetLMVarId___closed__2();
lean_mark_persistent(l_Lean_instForInLMVarIdSetLMVarId___closed__2);
l_Lean_instForInLMVarIdMapProdLMVarId___closed__1 = _init_l_Lean_instForInLMVarIdMapProdLMVarId___closed__1();
lean_mark_persistent(l_Lean_instForInLMVarIdMapProdLMVarId___closed__1);
l_Lean_Level_zero___override = _init_l_Lean_Level_zero___override();
lean_mark_persistent(l_Lean_Level_zero___override);
l_Lean_Level_data___override___closed__1 = _init_l_Lean_Level_data___override___closed__1();
lean_mark_persistent(l_Lean_Level_data___override___closed__1);
l_Lean_instInhabitedLevel = _init_l_Lean_instInhabitedLevel();
lean_mark_persistent(l_Lean_instInhabitedLevel);
l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__1 = _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__1();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__1);
l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__2 = _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__2();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__2);
l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__3 = _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__3();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__3);
l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__4 = _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__4();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__4);
l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__5 = _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__5();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__5);
l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__6 = _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__6();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__6);
l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__7 = _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__7();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__7);
l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__8 = _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__8();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__8);
l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__9 = _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__9();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__9);
l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__10 = _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__10();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__10);
l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__11 = _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__11();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__11);
l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__12 = _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__12();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__12);
l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__13 = _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__13();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__13);
l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__14 = _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__14();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__14);
l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__15 = _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__15();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__15);
l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__16 = _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__16();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__16);
l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__17 = _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__17();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__17);
l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__18 = _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__18();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__18);
l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__19 = _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__19();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__19);
l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__20 = _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__20();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__20);
l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__21 = _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__21();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__21);
l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__22 = _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__22();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__22);
l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__23 = _init_l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__23();
lean_mark_persistent(l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_1222____closed__23);
l_Lean_instReprLevel___closed__1 = _init_l_Lean_instReprLevel___closed__1();
lean_mark_persistent(l_Lean_instReprLevel___closed__1);
l_Lean_instReprLevel = _init_l_Lean_instReprLevel();
lean_mark_persistent(l_Lean_instReprLevel);
l_Lean_Level_instHashableLevel___closed__1 = _init_l_Lean_Level_instHashableLevel___closed__1();
lean_mark_persistent(l_Lean_Level_instHashableLevel___closed__1);
l_Lean_Level_instHashableLevel = _init_l_Lean_Level_instHashableLevel();
lean_mark_persistent(l_Lean_Level_instHashableLevel);
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
l_Array_qsort_sort___at_Lean_Level_normalize___spec__3___closed__1 = _init_l_Array_qsort_sort___at_Lean_Level_normalize___spec__3___closed__1();
lean_mark_persistent(l_Array_qsort_sort___at_Lean_Level_normalize___spec__3___closed__1);
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
l_Lean_Level_PP_Result_quote___closed__1 = _init_l_Lean_Level_PP_Result_quote___closed__1();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___closed__1);
l_Lean_Level_PP_Result_quote___closed__2 = _init_l_Lean_Level_PP_Result_quote___closed__2();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___closed__2);
l_Lean_Level_PP_Result_quote___closed__3 = _init_l_Lean_Level_PP_Result_quote___closed__3();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___closed__3);
l_Lean_Level_PP_Result_quote___closed__4 = _init_l_Lean_Level_PP_Result_quote___closed__4();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___closed__4);
l_Lean_Level_PP_Result_quote___closed__5 = _init_l_Lean_Level_PP_Result_quote___closed__5();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___closed__5);
l_Lean_Level_PP_Result_quote___closed__6 = _init_l_Lean_Level_PP_Result_quote___closed__6();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___closed__6);
l_Lean_Level_PP_Result_quote___closed__7 = _init_l_Lean_Level_PP_Result_quote___closed__7();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___closed__7);
l_Lean_Level_PP_Result_quote___closed__8 = _init_l_Lean_Level_PP_Result_quote___closed__8();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___closed__8);
l_Lean_Level_PP_Result_quote___closed__9 = _init_l_Lean_Level_PP_Result_quote___closed__9();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___closed__9);
l_Lean_Level_PP_Result_quote___closed__10 = _init_l_Lean_Level_PP_Result_quote___closed__10();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___closed__10);
l_Lean_Level_PP_Result_quote___closed__11 = _init_l_Lean_Level_PP_Result_quote___closed__11();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___closed__11);
l_Lean_Level_PP_Result_quote___closed__12 = _init_l_Lean_Level_PP_Result_quote___closed__12();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___closed__12);
l_Lean_Level_PP_Result_quote___closed__13 = _init_l_Lean_Level_PP_Result_quote___closed__13();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___closed__13);
l_Lean_Level_PP_Result_quote___closed__14 = _init_l_Lean_Level_PP_Result_quote___closed__14();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___closed__14);
l_Lean_Level_PP_Result_quote___closed__15 = _init_l_Lean_Level_PP_Result_quote___closed__15();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___closed__15);
l_Lean_Level_PP_Result_quote___closed__16 = _init_l_Lean_Level_PP_Result_quote___closed__16();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___closed__16);
l_Lean_Level_PP_Result_quote___closed__17 = _init_l_Lean_Level_PP_Result_quote___closed__17();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___closed__17);
l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__1 = _init_l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__1();
lean_mark_persistent(l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__1);
l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2 = _init_l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2();
lean_mark_persistent(l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2);
l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__3 = _init_l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__3();
lean_mark_persistent(l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__3);
l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__1 = _init_l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__1();
lean_mark_persistent(l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__1);
l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2 = _init_l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2();
lean_mark_persistent(l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2);
l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__3 = _init_l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__3();
lean_mark_persistent(l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__3);
l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__1 = _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__1();
lean_mark_persistent(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__1);
l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2 = _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2();
lean_mark_persistent(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2);
l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__3 = _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__3();
lean_mark_persistent(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

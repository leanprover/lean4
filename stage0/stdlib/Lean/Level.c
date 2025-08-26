// Lean compiler output
// Module: Lean.Level
// Imports: Init.Data.Array.QSort Lean.Data.PersistentHashMap Lean.Data.PersistentHashSet Lean.Hygiene Lean.Data.Name Lean.Data.Format Init.Data.Option.Coe Std.Data.TreeSet.Basic
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
lean_object* l_Std_TreeMap_instForInProd___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_toLevel___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_normalize___boxed(lean_object*);
LEAN_EXPORT lean_object* lean_level_mk_param(lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reprLevelMVarId___redArg____x40_Lean_Level_3927547624____hygCtx___hyg_44_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___Lean_Level_collectMVars_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Level_collectMVars_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Level_collectMVars_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___Lean_reprLevelMVarId____x40_Lean_Level_3927547624____hygCtx___hyg_44__spec__0(lean_object*);
static lean_object* l_Lean_reprLevelMVarId___redArg___closed__8____x40_Lean_Level_3927547624____hygCtx___hyg_44_;
LEAN_EXPORT lean_object* l_Lean_Level_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_beqLevelMVarId____x40_Lean_Level_3927547624____hygCtx___hyg_18____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_find_x3f_visit(lean_object*, lean_object*);
static lean_object* l_Lean_Level_PP_Result_quote___closed__10;
LEAN_EXPORT lean_object* l_Lean_instReprData___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
static lean_object* l_Lean_Level_PP_toResult___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkIMaxAux(lean_object*, lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__0;
LEAN_EXPORT uint8_t lean_level_has_mvar(lean_object*);
LEAN_EXPORT lean_object* lean_level_mk_succ(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Level_mvarId_x21_spec__0(lean_object*);
static lean_object* l_Lean_Level_PP_toResult___closed__6;
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isIMax_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_reprLevelMVarId___redArg___closed__6____x40_Lean_Level_3927547624____hygCtx___hyg_44_;
LEAN_EXPORT lean_object* l_Lean_instBEqData;
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Level_instHashable___closed__0;
static lean_object* l_Lean_Level_PP_Result_quote___closed__7;
LEAN_EXPORT lean_object* l_Nat_toLevel(lean_object*);
static lean_object* l_Lean_Level_PP_toResult___closed__5;
LEAN_EXPORT lean_object* l_Lean_reprLevel____x40_Lean_Level_2248933020____hygCtx___hyg_98____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_isMaxIMax___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_hasParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprData___lam__0(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_addOffsetAux(lean_object*, lean_object*);
static lean_object* l_Lean_reprLevelMVarId___redArg___closed__11____x40_Lean_Level_3927547624____hygCtx___hyg_44_;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_normLtAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_succ___override(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Level_Data_hash(uint64_t);
static lean_object* l_Lean_instReprData___lam__0___closed__3;
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instToFormat;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
static lean_object* l_Lean_Level_PP_Result_format___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_mkData___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t lean_level_depth(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Level_addOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_isMVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_zero___override;
static lean_object* l_Lean_Level_PP_Result_quote___closed__16;
LEAN_EXPORT lean_object* l_Lean_Level_Data_hasMVar___boxed(lean_object*);
lean_object* l_Std_TreeSet_instForIn___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isExplicit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_max___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_level_mk_zero(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isZero(lean_object*);
LEAN_EXPORT uint32_t lean_level_hash(lean_object*);
static lean_object* l_Lean_reprLevel___closed__3____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
static lean_object* l_Lean_reprLevel___closed__17____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
static lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0;
LEAN_EXPORT lean_object* l_Lean_Level_instQuoteMkStr1;
LEAN_EXPORT lean_object* l_Lean_Level_Data_depth___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_hashEx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Data_hash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprData;
LEAN_EXPORT lean_object* lean_level_mk_imax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_isParam___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isSucc(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_toResult___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Level_PP_Result_quote___closed__11;
LEAN_EXPORT lean_object* l_Lean_Level_substParams(lean_object*, lean_object*);
static lean_object* l_Lean_reprLevelMVarId___redArg___closed__1____x40_Lean_Level_3927547624____hygCtx___hyg_44_;
lean_object* l_panic___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Level_PP_Result_format___closed__5;
static lean_object* l_Lean_Level_PP_Result_quote___closed__12;
LEAN_EXPORT lean_object* l_Lean_instReprLMVarId;
LEAN_EXPORT lean_object* l_Lean_instInhabitedLevel;
LEAN_EXPORT lean_object* l_Lean_Level_normLtAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_reprLevel___closed__0____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
lean_object* l_Array_mkArray0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_ofNat(lean_object*);
uint64_t lean_uint64_land(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLevelMVar(lean_object*);
LEAN_EXPORT lean_object* lean_level_mk_mvar(lean_object*);
static lean_object* l_Lean_instReprData___lam__0___closed__2;
static lean_object* l_Lean_reprLevelMVarId___redArg___closed__3____x40_Lean_Level_3927547624____hygCtx___hyg_44_;
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_Lean_Level_data___override___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___Lean_Level_normalize_spec__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isEquiv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_format___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_hasParam___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_data___override___boxed(lean_object*);
static lean_object* l_Lean_reprLevel___closed__10____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_depthEx___boxed(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Level_normalize_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorIdx(lean_object*);
static lean_object* l_Lean_Level_PP_Result_quote___closed__15;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Level_normalize_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint64_t lean_level_mk_data(uint64_t, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Level_hasParamEx___boxed(lean_object*);
static lean_object* l_Lean_Level_PP_Result_quote___closed__4;
static lean_object* l_Lean_Level_PP_Result_quote___closed__8;
LEAN_EXPORT lean_object* l_Lean_instReprLMVarId___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instQuoteMkStr1___lam__0(lean_object*);
static lean_object* l_Lean_reprLevelMVarId___redArg___closed__9____x40_Lean_Level_3927547624____hygCtx___hyg_44_;
static lean_object* l_Lean_reprLevel___closed__15____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
LEAN_EXPORT lean_object* l_Lean_mkLevelSucc(lean_object*);
static lean_object* l_Lean_reprLevelMVarId___redArg___closed__7____x40_Lean_Level_3927547624____hygCtx___hyg_44_;
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Level_PP_Result_format___closed__2;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Level_quote(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_reprLevelMVarId___redArg___closed__5____x40_Lean_Level_3927547624____hygCtx___hyg_44_;
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_any___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_instReprLevelMVarId___closed__0;
LEAN_EXPORT uint8_t l_Lean_instBEqData___lam__0(uint64_t, uint64_t);
static lean_object* l_Lean_reprLevel___closed__13____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_toNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprLevel;
LEAN_EXPORT lean_object* l_Lean_Level_mvarId_x21___boxed(lean_object*);
static lean_object* l_Lean_Level_mvarId_x21___closed__2;
LEAN_EXPORT uint8_t l_Lean_Level_occurs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Level_normalize_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_ctorIdx___boxed(lean_object*);
static lean_object* l_Lean_levelOne___closed__0;
extern uint64_t l_instInhabitedUInt64;
static lean_object* l_Lean_reprLevelMVarId___redArg___closed__4____x40_Lean_Level_3927547624____hygCtx___hyg_44_;
static lean_object* l_Lean_instReprData___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_imax___boxed(lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
static lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkLevelMax(lean_object*, lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Level_normLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(lean_object*, uint8_t);
static lean_object* l_Lean_Level_PP_Result_quote___closed__14;
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Level_PP_Result_quote___closed__6;
LEAN_EXPORT lean_object* l_Lean_Level_ofNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_toResult(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instReprLevelMVarId;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Level_PP_Result_quote_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_geq_go___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_reprLevel___closed__12____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__0;
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Lean_Level_isNeverZero___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_simpLevelIMax_x27___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Level_PP_Result_format___closed__4;
LEAN_EXPORT lean_object* l_Lean_Level_instOfNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_isEquiv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_hasMVarEx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_isIMax___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_normLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_getParamSubst___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Level_PP_Result_quote_spec__0(size_t, size_t, lean_object*);
uint32_t lean_uint64_to_uint32(uint64_t);
static lean_object* l_Lean_instReprData___lam__0___closed__6;
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isAlreadyNormalizedCheap(lean_object*);
uint64_t lean_uint32_to_uint64(uint32_t);
LEAN_EXPORT lean_object* l_Lean_simpLevelIMax_x27(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_reprLevel___closed__2____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_succ(lean_object*);
static lean_object* l_Lean_Level_normalize___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Level_PP_Result_quote___closed__9;
LEAN_EXPORT lean_object* l_Lean_Level_mvarId_x21(lean_object*);
LEAN_EXPORT uint8_t l_Lean_beqLevelMVarId____x40_Lean_Level_3927547624____hygCtx___hyg_18_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedLMVarIdSet;
static lean_object* l_Lean_reprLevel___closed__1____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
lean_object* lean_mk_syntax_ident(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_hasMVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_geq___boxed(lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
LEAN_EXPORT lean_object* l_Lean_Level_isZero___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_depth___boxed(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instReprLevel___closed__0;
static lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Level_normalize_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Level_normalize_spec__2(lean_object*);
static lean_object* l_Lean_reprLevel___closed__8____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
LEAN_EXPORT lean_object* l_Lean_Level_dec___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_geq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_collectMVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Level_collectMVars_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_substParams_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprLMVarId___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqData___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2;
static lean_object* l_Lean_Level_PP_Result_quote___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___Lean_Level_normalize_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Level_PP_Result_quote___closed__2;
static lean_object* l_Lean_Level_PP_Result_quote___closed__3;
LEAN_EXPORT lean_object* l_Lean_reprLevelMVarId____x40_Lean_Level_3927547624____hygCtx___hyg_44_(lean_object*, lean_object*);
static lean_object* l_Lean_instForInLMVarIdSetLMVarId___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___Lean_Level_collectMVars_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Level_PP_toResult___closed__3;
static lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__1;
static lean_object* l_Lean_Level_mvarId_x21___closed__0;
static lean_object* l_Lean_reprLevelMVarId___redArg___closed__10____x40_Lean_Level_3927547624____hygCtx___hyg_44_;
LEAN_EXPORT lean_object* l_Lean_Level_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_getOffset(lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Level_isMax___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_instInhabitedData;
LEAN_EXPORT lean_object* l_Lean_Level_instToString___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_Data_hasParam(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Level_getLevelOffset(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Level_instToString___lam__0___closed__0;
static lean_object* l_Lean_reprLevel___closed__6____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instToString;
LEAN_EXPORT lean_object* l_Lean_instInhabitedLMVarIdMap(lean_object*);
static lean_object* l_Lean_Level_normalize___closed__2;
static lean_object* l_Lean_reprLevel___closed__11____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
static lean_object* l_Lean_reprLevel___closed__4____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
static lean_object* l_Lean_instReprData___lam__0___closed__1;
LEAN_EXPORT uint8_t l_Lean_Level_isParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_reprLevelMVarId____x40_Lean_Level_3927547624____hygCtx___hyg_44____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_instForInLMVarIdMapProdLMVarId___closed__0;
LEAN_EXPORT lean_object* l_Lean_Level_quote___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLevelIMax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_depth(lean_object*);
static lean_object* l_Lean_Level_PP_toResult___closed__7;
LEAN_EXPORT lean_object* l_Lean_Level_occurs___boxed(lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Level_normalize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_dec(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isIMax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_format(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isIMax_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_instBEqLevelMVarId___closed__0;
LEAN_EXPORT lean_object* l_Lean_hashLevelMVarId____x40_Lean_Level_3927547624____hygCtx___hyg_35____boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_geq_go(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Level_PP_Result_quote___closed__13;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_levelOne;
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Lean_Level_instBEq___closed__0;
static lean_object* l_Lean_reprLevelMVarId___redArg___closed__2____x40_Lean_Level_3927547624____hygCtx___hyg_44_;
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_accMax(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_reprLevel___closed__5____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
LEAN_EXPORT uint8_t l_Lean_Level_isMax(lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__0;
static lean_object* l_Lean_Level_PP_toResult___closed__0;
static lean_object* l_Lean_Level_PP_Result_quote___closed__0;
static lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2;
static lean_object* l_Lean_reprLevel___closed__16____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
static lean_object* l_Lean_Level_PP_toResult___closed__4;
LEAN_EXPORT lean_object* lean_level_mk_max(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Level_Data_depth(uint64_t);
LEAN_EXPORT lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instOfNat(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Level_hash(lean_object*);
static lean_object* l_Lean_Level_PP_toResult___closed__2;
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorIdx___boxed(lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
static lean_object* l_Lean_Level_PP_Result_quote___closed__5;
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_getOffset___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_getParamSubst(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Level_PP_Result_format___closed__1;
LEAN_EXPORT lean_object* l_Lean_instBEqLevelMVarId;
LEAN_EXPORT lean_object* l_Lean_Level_mkNaryMax(lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_param___override(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instToFormat___lam__0(lean_object*);
static lean_object* l_Lean_Level_PP_Result_format___closed__3;
LEAN_EXPORT uint8_t l_Lean_Level_any(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isMVar(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_reprLevel___closed__7____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Level_isAlreadyNormalizedCheap___boxed(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instHashable;
static lean_object* l_Lean_Level_normalize___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_imax(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_hashLevelMVarId____x40_Lean_Level_3927547624____hygCtx___hyg_35_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_getLevelOffset___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedLevelMVarId;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isNeverZero(lean_object*);
static lean_object* l_Lean_instReprData___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Level_isExplicit___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Level_data___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_reprLevel____x40_Lean_Level_2248933020____hygCtx___hyg_98_(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_reprLevel___closed__9____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
LEAN_EXPORT lean_object* l_Lean_Level_format___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Level_mvarId_x21___closed__3;
LEAN_EXPORT lean_object* l_Lean_Level_instBEq;
LEAN_EXPORT lean_object* l_Lean_simpLevelMax_x27(lean_object*, lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Level_collectMVars_spec__0___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelIMaxCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_Data_hasMVar(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_format(lean_object*, uint8_t);
static lean_object* l_Lean_instHashableLevelMVarId___closed__0;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_reprLevel___closed__14____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
LEAN_EXPORT lean_object* l_Lean_simpLevelMax_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_max(lean_object*, lean_object*);
static lean_object* l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1;
LEAN_EXPORT uint8_t l_Lean_Level_normLtAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_normalize(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Level_normalize___closed__0;
LEAN_EXPORT lean_object* l_Lean_Level_hash___boxed(lean_object*);
static lean_object* l_Lean_reprLevelMVarId___redArg___closed__0____x40_Lean_Level_3927547624____hygCtx___hyg_44_;
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_imax(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_instReprData___lam__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_normLtAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_skipExplicit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdSet;
static lean_object* l_Lean_Level_mvarId_x21___closed__1;
uint8_t l_Lean_Name_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_ctorToNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLevelParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_ctorToNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_getOffsetAux___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_level_has_param(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashableLevelMVarId;
LEAN_EXPORT uint8_t l_Lean_Level_isMaxIMax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_imax___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkMaxAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_toNat(lean_object*);
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
return x_3;
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
LEAN_EXPORT uint8_t l_Lean_instBEqData___lam__0(uint64_t x_1, uint64_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_uint64_dec_eq(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instBEqData() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instBEqData___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqData___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Lean_instBEqData___lam__0(x_3, x_4);
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
LEAN_EXPORT lean_object* l_Lean_Level_mkData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; uint8_t x_6; uint8_t x_7; uint64_t x_8; lean_object* x_9; 
x_5 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_6 = lean_unbox(x_3);
x_7 = lean_unbox(x_4);
x_8 = lean_level_mk_data(x_5, x_2, x_6, x_7);
x_9 = lean_box_uint64(x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_instReprData___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_instReprData___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" (hasParam := ", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_instReprData___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_instReprData___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_instReprData___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" (hasMVar := ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_instReprData___lam__0___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Level.mkData ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_instReprData___lam__0___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" (depth := ", 11, 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData___lam__0(uint64_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_7; lean_object* x_8; lean_object* x_13; lean_object* x_20; lean_object* x_21; lean_object* x_26; lean_object* x_33; uint64_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint32_t x_38; uint32_t x_39; uint8_t x_40; 
x_33 = l_Lean_instReprData___lam__0___closed__5;
x_34 = l_Lean_Level_Data_hash(x_1);
x_35 = lean_uint64_to_nat(x_34);
x_36 = l_Nat_reprFast(x_35);
x_37 = lean_string_append(x_33, x_36);
lean_dec_ref(x_36);
x_38 = l_Lean_Level_Data_depth(x_1);
x_39 = 0;
x_40 = lean_uint32_dec_eq(x_38, x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = l_Lean_instReprData___lam__0___closed__6;
x_42 = lean_string_append(x_37, x_41);
x_43 = lean_uint32_to_nat(x_38);
x_44 = l_Nat_reprFast(x_43);
x_45 = lean_string_append(x_42, x_44);
lean_dec_ref(x_44);
x_46 = l_Lean_instReprData___lam__0___closed__0;
x_47 = lean_string_append(x_45, x_46);
x_26 = x_47;
goto block_32;
}
else
{
x_26 = x_37;
goto block_32;
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l_Repr_addAppParen(x_4, x_2);
return x_5;
}
block_12:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_string_append(x_7, x_8);
lean_dec_ref(x_8);
x_10 = l_Lean_instReprData___lam__0___closed__0;
x_11 = lean_string_append(x_9, x_10);
x_3 = x_11;
goto block_6;
}
block_19:
{
uint8_t x_14; 
x_14 = l_Lean_Level_Data_hasParam(x_1);
if (x_14 == 0)
{
x_3 = x_13;
goto block_6;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_instReprData___lam__0___closed__1;
x_16 = lean_string_append(x_13, x_15);
if (x_14 == 0)
{
lean_object* x_17; 
x_17 = l_Lean_instReprData___lam__0___closed__2;
x_7 = x_16;
x_8 = x_17;
goto block_12;
}
else
{
lean_object* x_18; 
x_18 = l_Lean_instReprData___lam__0___closed__3;
x_7 = x_16;
x_8 = x_18;
goto block_12;
}
}
}
block_25:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_string_append(x_20, x_21);
lean_dec_ref(x_21);
x_23 = l_Lean_instReprData___lam__0___closed__0;
x_24 = lean_string_append(x_22, x_23);
x_13 = x_24;
goto block_19;
}
block_32:
{
uint8_t x_27; 
x_27 = l_Lean_Level_Data_hasMVar(x_1);
if (x_27 == 0)
{
x_13 = x_26;
goto block_19;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Lean_instReprData___lam__0___closed__4;
x_29 = lean_string_append(x_26, x_28);
if (x_27 == 0)
{
lean_object* x_30; 
x_30 = l_Lean_instReprData___lam__0___closed__2;
x_20 = x_29;
x_21 = x_30;
goto block_25;
}
else
{
lean_object* x_31; 
x_31 = l_Lean_instReprData___lam__0___closed__3;
x_20 = x_29;
x_21 = x_31;
goto block_25;
}
}
}
}
}
static lean_object* _init_l_Lean_instReprData() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instReprData___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Lean_instReprData___lam__0(x_3, x_2);
lean_dec(x_2);
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
LEAN_EXPORT uint8_t l_Lean_beqLevelMVarId____x40_Lean_Level_3927547624____hygCtx___hyg_18_(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_name_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_beqLevelMVarId____x40_Lean_Level_3927547624____hygCtx___hyg_18____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_beqLevelMVarId____x40_Lean_Level_3927547624____hygCtx___hyg_18_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instBEqLevelMVarId___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_beqLevelMVarId____x40_Lean_Level_3927547624____hygCtx___hyg_18____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instBEqLevelMVarId() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instBEqLevelMVarId___closed__0;
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lean_hashLevelMVarId____x40_Lean_Level_3927547624____hygCtx___hyg_35_(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; 
x_2 = 0;
x_3 = l_Lean_Name_hash___override(x_1);
x_4 = lean_uint64_mix_hash(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_hashLevelMVarId____x40_Lean_Level_3927547624____hygCtx___hyg_35____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_hashLevelMVarId____x40_Lean_Level_3927547624____hygCtx___hyg_35_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instHashableLevelMVarId___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_hashLevelMVarId____x40_Lean_Level_3927547624____hygCtx___hyg_35____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instHashableLevelMVarId() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instHashableLevelMVarId___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___Lean_reprLevelMVarId____x40_Lean_Level_3927547624____hygCtx___hyg_44__spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_reprLevelMVarId___redArg___closed__0____x40_Lean_Level_3927547624____hygCtx___hyg_44_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{ ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_reprLevelMVarId___redArg___closed__1____x40_Lean_Level_3927547624____hygCtx___hyg_44_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("name", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_reprLevelMVarId___redArg___closed__2____x40_Lean_Level_3927547624____hygCtx___hyg_44_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_reprLevelMVarId___redArg___closed__1____x40_Lean_Level_3927547624____hygCtx___hyg_44_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_reprLevelMVarId___redArg___closed__3____x40_Lean_Level_3927547624____hygCtx___hyg_44_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_reprLevelMVarId___redArg___closed__2____x40_Lean_Level_3927547624____hygCtx___hyg_44_;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_reprLevelMVarId___redArg___closed__4____x40_Lean_Level_3927547624____hygCtx___hyg_44_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" := ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_reprLevelMVarId___redArg___closed__5____x40_Lean_Level_3927547624____hygCtx___hyg_44_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_reprLevelMVarId___redArg___closed__4____x40_Lean_Level_3927547624____hygCtx___hyg_44_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_reprLevelMVarId___redArg___closed__6____x40_Lean_Level_3927547624____hygCtx___hyg_44_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_reprLevelMVarId___redArg___closed__5____x40_Lean_Level_3927547624____hygCtx___hyg_44_;
x_2 = l_Lean_reprLevelMVarId___redArg___closed__3____x40_Lean_Level_3927547624____hygCtx___hyg_44_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_reprLevelMVarId___redArg___closed__7____x40_Lean_Level_3927547624____hygCtx___hyg_44_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_reprLevelMVarId___redArg___closed__8____x40_Lean_Level_3927547624____hygCtx___hyg_44_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" }", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_reprLevelMVarId___redArg___closed__9____x40_Lean_Level_3927547624____hygCtx___hyg_44_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_reprLevelMVarId___redArg___closed__10____x40_Lean_Level_3927547624____hygCtx___hyg_44_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_reprLevelMVarId___redArg___closed__0____x40_Lean_Level_3927547624____hygCtx___hyg_44_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_reprLevelMVarId___redArg___closed__11____x40_Lean_Level_3927547624____hygCtx___hyg_44_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_reprLevelMVarId___redArg___closed__8____x40_Lean_Level_3927547624____hygCtx___hyg_44_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_reprLevelMVarId___redArg____x40_Lean_Level_3927547624____hygCtx___hyg_44_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_2 = l_Lean_reprLevelMVarId___redArg___closed__6____x40_Lean_Level_3927547624____hygCtx___hyg_44_;
x_3 = l_Lean_reprLevelMVarId___redArg___closed__7____x40_Lean_Level_3927547624____hygCtx___hyg_44_;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Name_reprPrec(x_1, x_4);
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = 0;
x_8 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_reprLevelMVarId___redArg___closed__9____x40_Lean_Level_3927547624____hygCtx___hyg_44_;
x_11 = l_Lean_reprLevelMVarId___redArg___closed__10____x40_Lean_Level_3927547624____hygCtx___hyg_44_;
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
x_13 = l_Lean_reprLevelMVarId___redArg___closed__11____x40_Lean_Level_3927547624____hygCtx___hyg_44_;
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_7);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_reprLevelMVarId____x40_Lean_Level_3927547624____hygCtx___hyg_44_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_reprLevelMVarId___redArg____x40_Lean_Level_3927547624____hygCtx___hyg_44_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_reprLevelMVarId____x40_Lean_Level_3927547624____hygCtx___hyg_44____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_reprLevelMVarId____x40_Lean_Level_3927547624____hygCtx___hyg_44_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instReprLevelMVarId___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_reprLevelMVarId____x40_Lean_Level_3927547624____hygCtx___hyg_44____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instReprLevelMVarId() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instReprLevelMVarId___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLMVarId___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Name_reprPrec(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instReprLMVarId() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instReprLMVarId___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLMVarId___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instReprLMVarId___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instInhabitedLMVarIdSet() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(1);
return x_1;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionLMVarIdSet() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(1);
return x_1;
}
}
static lean_object* _init_l_Lean_instForInLMVarIdSetLMVarId___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_TreeSet_instForIn___lam__2), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdSetLMVarId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instForInLMVarIdSetLMVarId___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionLMVarIdMap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(1);
return x_2;
}
}
static lean_object* _init_l_Lean_instForInLMVarIdMapProdLMVarId___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_TreeMap_instForInProd___lam__2), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLMVarIdMapProdLMVarId(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instForInLMVarIdMapProdLMVarId___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedLMVarIdMap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorIdx(lean_object* x_1) {
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
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
default: 
{
lean_object* x_7; 
x_7 = lean_unsigned_to_nat(5u);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_dec_ref(x_1);
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
lean_dec_ref(x_1);
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
lean_dec_ref(x_1);
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
lean_dec_ref(x_1);
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
lean_dec_ref(x_1);
x_19 = lean_apply_1(x_7, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_inc(x_3);
return x_3;
}
case 1:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = lean_apply_1(x_4, x_9);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec_ref(x_2);
x_13 = lean_apply_2(x_5, x_11, x_12);
return x_13;
}
case 3:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec_ref(x_2);
x_16 = lean_apply_2(x_6, x_14, x_15);
return x_16;
}
case 4:
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec_ref(x_2);
x_18 = lean_apply_1(x_7, x_17);
return x_18;
}
default: 
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec_ref(x_2);
x_20 = lean_apply_1(x_8, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Level_casesOn___override___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_casesOn___override___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Level_casesOn___override(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
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
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; uint32_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; uint64_t x_12; lean_object* x_13; 
x_2 = 2243;
x_3 = l_Lean_Level_data___override(x_1);
x_4 = l_Lean_Level_Data_hash(x_3);
x_5 = lean_uint64_mix_hash(x_2, x_4);
x_6 = l_Lean_Level_Data_depth(x_3);
x_7 = lean_uint32_to_nat(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_7, x_8);
lean_dec(x_7);
x_10 = l_Lean_Level_Data_hasMVar(x_3);
x_11 = l_Lean_Level_Data_hasParam(x_3);
x_12 = lean_level_mk_data(x_5, x_9, x_10, x_11);
x_13 = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set_uint64(x_13, sizeof(void*)*1, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_max___override(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_16; uint8_t x_17; lean_object* x_21; uint32_t x_27; lean_object* x_28; uint32_t x_29; lean_object* x_30; uint8_t x_31; 
x_3 = 2251;
x_4 = l_Lean_Level_data___override(x_1);
x_5 = l_Lean_Level_Data_hash(x_4);
x_6 = l_Lean_Level_data___override(x_2);
x_7 = l_Lean_Level_Data_hash(x_6);
x_8 = lean_uint64_mix_hash(x_5, x_7);
x_9 = lean_uint64_mix_hash(x_3, x_8);
x_27 = l_Lean_Level_Data_depth(x_4);
x_28 = lean_uint32_to_nat(x_27);
x_29 = l_Lean_Level_Data_depth(x_6);
x_30 = lean_uint32_to_nat(x_29);
x_31 = lean_nat_dec_le(x_28, x_30);
if (x_31 == 0)
{
lean_dec(x_30);
x_21 = x_28;
goto block_26;
}
else
{
lean_dec(x_28);
x_21 = x_30;
goto block_26;
}
block_15:
{
uint64_t x_13; lean_object* x_14; 
x_13 = lean_level_mk_data(x_9, x_10, x_11, x_12);
x_14 = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set_uint64(x_14, sizeof(void*)*2, x_13);
return x_14;
}
block_20:
{
uint8_t x_18; 
x_18 = l_Lean_Level_Data_hasParam(x_4);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Level_Data_hasParam(x_6);
x_10 = x_16;
x_11 = x_17;
x_12 = x_19;
goto block_15;
}
else
{
x_10 = x_16;
x_11 = x_17;
x_12 = x_18;
goto block_15;
}
}
block_26:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_21, x_22);
lean_dec(x_21);
x_24 = l_Lean_Level_Data_hasMVar(x_4);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = l_Lean_Level_Data_hasMVar(x_6);
x_16 = x_23;
x_17 = x_25;
goto block_20;
}
else
{
x_16 = x_23;
x_17 = x_24;
goto block_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_imax___override(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_16; uint8_t x_17; lean_object* x_21; uint32_t x_27; lean_object* x_28; uint32_t x_29; lean_object* x_30; uint8_t x_31; 
x_3 = 2267;
x_4 = l_Lean_Level_data___override(x_1);
x_5 = l_Lean_Level_Data_hash(x_4);
x_6 = l_Lean_Level_data___override(x_2);
x_7 = l_Lean_Level_Data_hash(x_6);
x_8 = lean_uint64_mix_hash(x_5, x_7);
x_9 = lean_uint64_mix_hash(x_3, x_8);
x_27 = l_Lean_Level_Data_depth(x_4);
x_28 = lean_uint32_to_nat(x_27);
x_29 = l_Lean_Level_Data_depth(x_6);
x_30 = lean_uint32_to_nat(x_29);
x_31 = lean_nat_dec_le(x_28, x_30);
if (x_31 == 0)
{
lean_dec(x_30);
x_21 = x_28;
goto block_26;
}
else
{
lean_dec(x_28);
x_21 = x_30;
goto block_26;
}
block_15:
{
uint64_t x_13; lean_object* x_14; 
x_13 = lean_level_mk_data(x_9, x_10, x_11, x_12);
x_14 = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set_uint64(x_14, sizeof(void*)*2, x_13);
return x_14;
}
block_20:
{
uint8_t x_18; 
x_18 = l_Lean_Level_Data_hasParam(x_4);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Level_Data_hasParam(x_6);
x_10 = x_16;
x_11 = x_17;
x_12 = x_19;
goto block_15;
}
else
{
x_10 = x_16;
x_11 = x_17;
x_12 = x_18;
goto block_15;
}
}
block_26:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_21, x_22);
lean_dec(x_21);
x_24 = l_Lean_Level_Data_hasMVar(x_4);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = l_Lean_Level_Data_hasMVar(x_6);
x_16 = x_23;
x_17 = x_25;
goto block_20;
}
else
{
x_16 = x_23;
x_17 = x_24;
goto block_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_param___override(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint64_t x_8; lean_object* x_9; 
x_2 = 2239;
x_3 = l_Lean_Name_hash___override(x_1);
x_4 = lean_uint64_mix_hash(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = 0;
x_7 = 1;
x_8 = lean_level_mk_data(x_4, x_5, x_6, x_7);
x_9 = lean_alloc_ctor(4, 1, 8);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set_uint64(x_9, sizeof(void*)*1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_mvar___override(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint64_t x_8; lean_object* x_9; 
x_2 = 2237;
x_3 = l_Lean_hashLevelMVarId____x40_Lean_Level_3927547624____hygCtx___hyg_35_(x_1);
x_4 = lean_uint64_mix_hash(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = 1;
x_7 = 0;
x_8 = lean_level_mk_data(x_4, x_5, x_6, x_7);
x_9 = lean_alloc_ctor(5, 1, 8);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set_uint64(x_9, sizeof(void*)*1, x_8);
return x_9;
}
}
static uint64_t _init_l_Lean_Level_data___override___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; uint64_t x_3; uint64_t x_4; 
x_1 = 0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = 2221;
x_4 = lean_level_mk_data(x_3, x_2, x_1, x_1);
return x_4;
}
}
LEAN_EXPORT uint64_t l_Lean_Level_data___override(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint64_t x_2; 
x_2 = l_Lean_Level_data___override___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_Level_data___override___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Level_data___override(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
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
static lean_object* _init_l_Lean_reprLevel___closed__0____x40_Lean_Level_2248933020____hygCtx___hyg_98_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Level.zero", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_reprLevel___closed__1____x40_Lean_Level_2248933020____hygCtx___hyg_98_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_reprLevel___closed__0____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_reprLevel___closed__2____x40_Lean_Level_2248933020____hygCtx___hyg_98_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_reprLevel___closed__3____x40_Lean_Level_2248933020____hygCtx___hyg_98_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Level.succ", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_reprLevel___closed__4____x40_Lean_Level_2248933020____hygCtx___hyg_98_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_reprLevel___closed__3____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_reprLevel___closed__5____x40_Lean_Level_2248933020____hygCtx___hyg_98_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_reprLevel___closed__4____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_reprLevel___closed__6____x40_Lean_Level_2248933020____hygCtx___hyg_98_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Level.max", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_reprLevel___closed__7____x40_Lean_Level_2248933020____hygCtx___hyg_98_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_reprLevel___closed__6____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_reprLevel___closed__8____x40_Lean_Level_2248933020____hygCtx___hyg_98_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_reprLevel___closed__7____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_reprLevel___closed__9____x40_Lean_Level_2248933020____hygCtx___hyg_98_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Level.imax", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_reprLevel___closed__10____x40_Lean_Level_2248933020____hygCtx___hyg_98_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_reprLevel___closed__9____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_reprLevel___closed__11____x40_Lean_Level_2248933020____hygCtx___hyg_98_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_reprLevel___closed__10____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_reprLevel___closed__12____x40_Lean_Level_2248933020____hygCtx___hyg_98_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Level.param", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_reprLevel___closed__13____x40_Lean_Level_2248933020____hygCtx___hyg_98_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_reprLevel___closed__12____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_reprLevel___closed__14____x40_Lean_Level_2248933020____hygCtx___hyg_98_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_reprLevel___closed__13____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_reprLevel___closed__15____x40_Lean_Level_2248933020____hygCtx___hyg_98_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Level.mvar", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_reprLevel___closed__16____x40_Lean_Level_2248933020____hygCtx___hyg_98_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_reprLevel___closed__15____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_reprLevel___closed__17____x40_Lean_Level_2248933020____hygCtx___hyg_98_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_reprLevel___closed__16____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_reprLevel____x40_Lean_Level_2248933020____hygCtx___hyg_98_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(1024u);
x_11 = lean_nat_dec_le(x_10, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_reprLevelMVarId___redArg___closed__9____x40_Lean_Level_3927547624____hygCtx___hyg_44_;
x_3 = x_12;
goto block_9;
}
else
{
lean_object* x_13; 
x_13 = l_Lean_reprLevel___closed__2____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
x_3 = x_13;
goto block_9;
}
}
case 1:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_25; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec_ref(x_1);
x_15 = lean_unsigned_to_nat(1024u);
x_25 = lean_nat_dec_le(x_15, x_2);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = l_Lean_reprLevelMVarId___redArg___closed__9____x40_Lean_Level_3927547624____hygCtx___hyg_44_;
x_16 = x_26;
goto block_24;
}
else
{
lean_object* x_27; 
x_27 = l_Lean_reprLevel___closed__2____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
x_16 = x_27;
goto block_24;
}
block_24:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_17 = l_Lean_reprLevel___closed__5____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
x_18 = l_Lean_reprLevel____x40_Lean_Level_2248933020____hygCtx___hyg_98_(x_14, x_15);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = 0;
x_22 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_21);
x_23 = l_Repr_addAppParen(x_22, x_2);
return x_23;
}
}
case 2:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_44; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_dec_ref(x_1);
x_30 = lean_unsigned_to_nat(1024u);
x_44 = lean_nat_dec_le(x_30, x_2);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = l_Lean_reprLevelMVarId___redArg___closed__9____x40_Lean_Level_3927547624____hygCtx___hyg_44_;
x_31 = x_45;
goto block_43;
}
else
{
lean_object* x_46; 
x_46 = l_Lean_reprLevel___closed__2____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
x_31 = x_46;
goto block_43;
}
block_43:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_32 = lean_box(1);
x_33 = l_Lean_reprLevel___closed__8____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
x_34 = l_Lean_reprLevel____x40_Lean_Level_2248933020____hygCtx___hyg_98_(x_28, x_30);
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
x_37 = l_Lean_reprLevel____x40_Lean_Level_2248933020____hygCtx___hyg_98_(x_29, x_30);
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_38);
x_40 = 0;
x_41 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_40);
x_42 = l_Repr_addAppParen(x_41, x_2);
return x_42;
}
}
case 3:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_63; 
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_1, 1);
lean_inc(x_48);
lean_dec_ref(x_1);
x_49 = lean_unsigned_to_nat(1024u);
x_63 = lean_nat_dec_le(x_49, x_2);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = l_Lean_reprLevelMVarId___redArg___closed__9____x40_Lean_Level_3927547624____hygCtx___hyg_44_;
x_50 = x_64;
goto block_62;
}
else
{
lean_object* x_65; 
x_65 = l_Lean_reprLevel___closed__2____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
x_50 = x_65;
goto block_62;
}
block_62:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
x_51 = lean_box(1);
x_52 = l_Lean_reprLevel___closed__11____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
x_53 = l_Lean_reprLevel____x40_Lean_Level_2248933020____hygCtx___hyg_98_(x_47, x_49);
x_54 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
x_56 = l_Lean_reprLevel____x40_Lean_Level_2248933020____hygCtx___hyg_98_(x_48, x_49);
x_57 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_58, 0, x_50);
lean_ctor_set(x_58, 1, x_57);
x_59 = 0;
x_60 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_59);
x_61 = l_Repr_addAppParen(x_60, x_2);
return x_61;
}
}
case 4:
{
lean_object* x_66; lean_object* x_67; lean_object* x_77; uint8_t x_78; 
x_66 = lean_ctor_get(x_1, 0);
lean_inc(x_66);
lean_dec_ref(x_1);
x_77 = lean_unsigned_to_nat(1024u);
x_78 = lean_nat_dec_le(x_77, x_2);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = l_Lean_reprLevelMVarId___redArg___closed__9____x40_Lean_Level_3927547624____hygCtx___hyg_44_;
x_67 = x_79;
goto block_76;
}
else
{
lean_object* x_80; 
x_80 = l_Lean_reprLevel___closed__2____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
x_67 = x_80;
goto block_76;
}
block_76:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; 
x_68 = l_Lean_reprLevel___closed__14____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
x_69 = lean_unsigned_to_nat(1024u);
x_70 = l_Lean_Name_reprPrec(x_66, x_69);
x_71 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_72, 0, x_67);
lean_ctor_set(x_72, 1, x_71);
x_73 = 0;
x_74 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set_uint8(x_74, sizeof(void*)*1, x_73);
x_75 = l_Repr_addAppParen(x_74, x_2);
return x_75;
}
}
default: 
{
lean_object* x_81; lean_object* x_82; lean_object* x_92; uint8_t x_93; 
x_81 = lean_ctor_get(x_1, 0);
lean_inc(x_81);
lean_dec_ref(x_1);
x_92 = lean_unsigned_to_nat(1024u);
x_93 = lean_nat_dec_le(x_92, x_2);
if (x_93 == 0)
{
lean_object* x_94; 
x_94 = l_Lean_reprLevelMVarId___redArg___closed__9____x40_Lean_Level_3927547624____hygCtx___hyg_44_;
x_82 = x_94;
goto block_91;
}
else
{
lean_object* x_95; 
x_95 = l_Lean_reprLevel___closed__2____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
x_82 = x_95;
goto block_91;
}
block_91:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; 
x_83 = l_Lean_reprLevel___closed__17____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
x_84 = lean_unsigned_to_nat(1024u);
x_85 = l_Lean_Name_reprPrec(x_81, x_84);
x_86 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_87, 0, x_82);
lean_ctor_set(x_87, 1, x_86);
x_88 = 0;
x_89 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_88);
x_90 = l_Repr_addAppParen(x_89, x_2);
return x_90;
}
}
}
block_9:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_reprLevel___closed__1____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = 0;
x_7 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_reprLevel____x40_Lean_Level_2248933020____hygCtx___hyg_98____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_reprLevel____x40_Lean_Level_2248933020____hygCtx___hyg_98_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instReprLevel___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_reprLevel____x40_Lean_Level_2248933020____hygCtx___hyg_98____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instReprLevel() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instReprLevel___closed__0;
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lean_Level_hash(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; 
x_2 = l_Lean_Level_data___override(x_1);
x_3 = l_Lean_Level_Data_hash(x_2);
return x_3;
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
static lean_object* _init_l_Lean_Level_instHashable___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Level_hash___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_instHashable() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Level_instHashable___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_depth(lean_object* x_1) {
_start:
{
uint64_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = l_Lean_Level_data___override(x_1);
x_3 = l_Lean_Level_Data_depth(x_2);
x_4 = lean_uint32_to_nat(x_3);
return x_4;
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
uint64_t x_2; uint8_t x_3; 
x_2 = l_Lean_Level_data___override(x_1);
x_3 = l_Lean_Level_Data_hasMVar(x_2);
return x_3;
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
uint64_t x_2; uint8_t x_3; 
x_2 = l_Lean_Level_data___override(x_1);
x_3 = l_Lean_Level_Data_hasParam(x_2);
return x_3;
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
uint64_t x_2; uint32_t x_3; 
x_2 = l_Lean_Level_data___override(x_1);
lean_dec(x_1);
x_3 = l_Lean_Level_Data_depth(x_2);
return x_3;
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
static lean_object* _init_l_Lean_levelOne___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Level_succ___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_levelOne() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_levelOne___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* lean_level_mk_zero(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
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
LEAN_EXPORT lean_object* l_panic___at___Lean_Level_mvarId_x21_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Level_mvarId_x21___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Level", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_mvarId_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Level.mvarId!", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_mvarId_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("metavariable expected", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_mvarId_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Level_mvarId_x21___closed__2;
x_2 = lean_unsigned_to_nat(19u);
x_3 = lean_unsigned_to_nat(195u);
x_4 = l_Lean_Level_mvarId_x21___closed__1;
x_5 = l_Lean_Level_mvarId_x21___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
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
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Level_mvarId_x21___closed__3;
x_4 = l_panic___at___Lean_Level_mvarId_x21_spec__0(x_3);
return x_4;
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
case 0:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
case 1:
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
case 2:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Level_isNeverZero(x_4);
if (x_6 == 0)
{
x_1 = x_5;
goto _start;
}
else
{
return x_6;
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
if (x_3 == 1)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_1, x_5);
x_7 = l_Lean_Level_ofNat(x_6);
lean_dec(x_6);
x_8 = l_Lean_Level_succ___override(x_7);
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
LEAN_EXPORT lean_object* l_Lean_Level_instOfNat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instOfNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_instOfNat(x_1);
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
if (x_4 == 1)
{
lean_dec(x_1);
return x_2;
}
else
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
return x_4;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
default: 
{
uint8_t x_8; 
x_8 = 0;
return x_8;
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
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Level_getOffset(x_1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_box(0);
return x_5;
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
static lean_object* _init_l_Lean_Level_instBEq___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Level_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_instBEq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Level_instBEq___closed__0;
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
return x_4;
}
}
case 2:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_11; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_11 = lean_level_eq(x_1, x_2);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_Level_occurs(x_1, x_6);
x_8 = x_12;
goto block_10;
}
else
{
x_8 = x_11;
goto block_10;
}
block_10:
{
if (x_8 == 0)
{
x_2 = x_7;
goto _start;
}
else
{
return x_8;
}
}
}
case 3:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_18; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_18 = lean_level_eq(x_1, x_2);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Level_occurs(x_1, x_13);
x_15 = x_19;
goto block_17;
}
else
{
x_15 = x_18;
goto block_17;
}
block_17:
{
if (x_15 == 0)
{
x_2 = x_14;
goto _start;
}
else
{
return x_15;
}
}
}
default: 
{
uint8_t x_20; 
x_20 = lean_level_eq(x_1, x_2);
return x_20;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
switch (lean_obj_tag(x_1)) {
case 0:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
x_13 = x_3;
x_14 = x_2;
x_15 = x_3;
x_16 = x_4;
goto block_22;
}
case 1:
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_3, 0);
x_5 = x_1;
x_6 = x_2;
x_7 = x_23;
x_8 = x_4;
goto block_12;
}
default: 
{
x_13 = x_1;
x_14 = x_2;
x_15 = x_3;
x_16 = x_4;
goto block_22;
}
}
}
case 1:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_2, x_25);
lean_dec(x_2);
x_1 = x_24;
x_2 = x_26;
goto _start;
}
case 2:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_3, 0);
x_5 = x_1;
x_6 = x_2;
x_7 = x_28;
x_8 = x_4;
goto block_12;
}
case 2:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_36; 
x_29 = lean_ctor_get(x_1, 0);
x_30 = lean_ctor_get(x_1, 1);
x_31 = lean_ctor_get(x_3, 0);
x_32 = lean_ctor_get(x_3, 1);
x_36 = lean_level_eq(x_1, x_3);
if (x_36 == 0)
{
uint8_t x_37; 
lean_dec(x_4);
lean_dec(x_2);
x_37 = lean_level_eq(x_29, x_31);
if (x_37 == 0)
{
goto block_35;
}
else
{
if (x_36 == 0)
{
lean_object* x_38; 
x_38 = lean_unsigned_to_nat(0u);
x_1 = x_30;
x_2 = x_38;
x_3 = x_32;
x_4 = x_38;
goto _start;
}
else
{
goto block_35;
}
}
}
else
{
uint8_t x_40; 
x_40 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_40;
}
block_35:
{
lean_object* x_33; 
x_33 = lean_unsigned_to_nat(0u);
x_1 = x_29;
x_2 = x_33;
x_3 = x_31;
x_4 = x_33;
goto _start;
}
}
default: 
{
x_13 = x_1;
x_14 = x_2;
x_15 = x_3;
x_16 = x_4;
goto block_22;
}
}
}
case 3:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_3, 0);
x_5 = x_1;
x_6 = x_2;
x_7 = x_41;
x_8 = x_4;
goto block_12;
}
case 3:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_49; 
x_42 = lean_ctor_get(x_1, 0);
x_43 = lean_ctor_get(x_1, 1);
x_44 = lean_ctor_get(x_3, 0);
x_45 = lean_ctor_get(x_3, 1);
x_49 = lean_level_eq(x_1, x_3);
if (x_49 == 0)
{
uint8_t x_50; 
lean_dec(x_4);
lean_dec(x_2);
x_50 = lean_level_eq(x_42, x_44);
if (x_50 == 0)
{
goto block_48;
}
else
{
if (x_49 == 0)
{
lean_object* x_51; 
x_51 = lean_unsigned_to_nat(0u);
x_1 = x_43;
x_2 = x_51;
x_3 = x_45;
x_4 = x_51;
goto _start;
}
else
{
goto block_48;
}
}
}
else
{
uint8_t x_53; 
x_53 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_53;
}
block_48:
{
lean_object* x_46; 
x_46 = lean_unsigned_to_nat(0u);
x_1 = x_42;
x_2 = x_46;
x_3 = x_44;
x_4 = x_46;
goto _start;
}
}
default: 
{
x_13 = x_1;
x_14 = x_2;
x_15 = x_3;
x_16 = x_4;
goto block_22;
}
}
}
case 4:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_3, 0);
x_5 = x_1;
x_6 = x_2;
x_7 = x_54;
x_8 = x_4;
goto block_12;
}
case 4:
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_ctor_get(x_1, 0);
x_56 = lean_ctor_get(x_3, 0);
x_57 = lean_name_eq(x_55, x_56);
if (x_57 == 0)
{
uint8_t x_58; 
lean_dec(x_4);
lean_dec(x_2);
x_58 = l_Lean_Name_lt(x_55, x_56);
return x_58;
}
else
{
uint8_t x_59; 
x_59 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_59;
}
}
default: 
{
x_13 = x_1;
x_14 = x_2;
x_15 = x_3;
x_16 = x_4;
goto block_22;
}
}
}
default: 
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_3, 0);
x_5 = x_1;
x_6 = x_2;
x_7 = x_60;
x_8 = x_4;
goto block_12;
}
case 5:
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_1, 0);
x_62 = lean_ctor_get(x_3, 0);
x_63 = lean_name_eq(x_61, x_62);
if (x_63 == 0)
{
uint8_t x_64; 
lean_dec(x_4);
lean_dec(x_2);
x_64 = l_Lean_Name_lt(x_61, x_62);
return x_64;
}
else
{
uint8_t x_65; 
x_65 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_65;
}
}
default: 
{
x_13 = x_1;
x_14 = x_2;
x_15 = x_3;
x_16 = x_4;
goto block_22;
}
}
}
}
block_12:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_8, x_9);
lean_dec(x_8);
x_1 = x_5;
x_2 = x_6;
x_3 = x_7;
x_4 = x_10;
goto _start;
}
block_22:
{
uint8_t x_17; 
x_17 = lean_level_eq(x_13, x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_16);
lean_dec(x_14);
x_18 = l_Lean_Level_ctorToNat(x_13);
x_19 = l_Lean_Level_ctorToNat(x_15);
x_20 = lean_nat_dec_lt(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_lt(x_14, x_16);
lean_dec(x_16);
lean_dec(x_14);
return x_21;
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
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_normLtAux_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_12; 
lean_dec(x_6);
x_12 = lean_apply_10(x_11, x_3, x_2, x_3, x_4, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec_ref(x_3);
x_14 = lean_apply_5(x_6, x_1, x_2, x_13, x_4, lean_box(0));
return x_14;
}
default: 
{
lean_object* x_15; 
lean_dec(x_6);
x_15 = lean_apply_10(x_11, x_1, x_2, x_3, x_4, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_15;
}
}
}
case 1:
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec_ref(x_1);
x_17 = lean_apply_4(x_5, x_16, x_2, x_3, x_4);
return x_17;
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
lean_object* x_18; lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_7);
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
lean_dec_ref(x_3);
x_19 = lean_apply_5(x_6, x_1, x_2, x_18, x_4, lean_box(0));
return x_19;
}
case 2:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_11);
lean_dec(x_6);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec_ref(x_1);
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
lean_dec_ref(x_3);
x_24 = lean_apply_6(x_7, x_20, x_21, x_2, x_22, x_23, x_4);
return x_24;
}
default: 
{
lean_object* x_25; 
lean_dec(x_7);
lean_dec(x_6);
x_25 = lean_apply_10(x_11, x_1, x_2, x_3, x_4, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_25;
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
lean_object* x_26; lean_object* x_27; 
lean_dec(x_11);
lean_dec(x_8);
x_26 = lean_ctor_get(x_3, 0);
lean_inc(x_26);
lean_dec_ref(x_3);
x_27 = lean_apply_5(x_6, x_1, x_2, x_26, x_4, lean_box(0));
return x_27;
}
case 3:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_11);
lean_dec(x_6);
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_dec_ref(x_1);
x_30 = lean_ctor_get(x_3, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_3, 1);
lean_inc(x_31);
lean_dec_ref(x_3);
x_32 = lean_apply_6(x_8, x_28, x_29, x_2, x_30, x_31, x_4);
return x_32;
}
default: 
{
lean_object* x_33; 
lean_dec(x_8);
lean_dec(x_6);
x_33 = lean_apply_10(x_11, x_1, x_2, x_3, x_4, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_33;
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
lean_object* x_34; lean_object* x_35; 
lean_dec(x_11);
lean_dec(x_9);
x_34 = lean_ctor_get(x_3, 0);
lean_inc(x_34);
lean_dec_ref(x_3);
x_35 = lean_apply_5(x_6, x_1, x_2, x_34, x_4, lean_box(0));
return x_35;
}
case 4:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_11);
lean_dec(x_6);
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
lean_dec_ref(x_1);
x_37 = lean_ctor_get(x_3, 0);
lean_inc(x_37);
lean_dec_ref(x_3);
x_38 = lean_apply_4(x_9, x_36, x_2, x_37, x_4);
return x_38;
}
default: 
{
lean_object* x_39; 
lean_dec(x_9);
lean_dec(x_6);
x_39 = lean_apply_10(x_11, x_1, x_2, x_3, x_4, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_39;
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
lean_object* x_40; lean_object* x_41; 
lean_dec(x_11);
lean_dec(x_10);
x_40 = lean_ctor_get(x_3, 0);
lean_inc(x_40);
lean_dec_ref(x_3);
x_41 = lean_apply_5(x_6, x_1, x_2, x_40, x_4, lean_box(0));
return x_41;
}
case 5:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_11);
lean_dec(x_6);
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
lean_dec_ref(x_1);
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
lean_dec_ref(x_3);
x_44 = lean_apply_4(x_10, x_42, x_2, x_43, x_4);
return x_44;
}
default: 
{
lean_object* x_45; 
lean_dec(x_10);
lean_dec(x_6);
x_45 = lean_apply_10(x_11, x_1, x_2, x_3, x_4, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_45;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_normLtAux_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Level_0__Lean_Level_normLtAux_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
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
LEAN_EXPORT uint8_t l_Lean_Level_isAlreadyNormalizedCheap(lean_object* x_1) {
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
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
x_1 = x_3;
goto _start;
}
case 4:
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
case 5:
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
default: 
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isAlreadyNormalizedCheap___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Level_isAlreadyNormalizedCheap(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_mkIMaxAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
switch (lean_obj_tag(x_1)) {
case 0:
{
return x_2;
}
case 1:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_8) == 0)
{
lean_dec_ref(x_1);
return x_2;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec_ref(x_1);
return x_2;
}
else
{
x_3 = x_1;
x_4 = x_2;
goto block_7;
}
}
}
default: 
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
x_3 = x_1;
x_4 = x_2;
goto block_7;
}
}
}
block_7:
{
uint8_t x_5; 
x_5 = lean_level_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_Lean_Level_imax___override(x_3, x_4);
return x_6;
}
else
{
lean_dec(x_4);
return x_3;
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
lean_dec_ref(x_2);
lean_inc_ref(x_1);
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
lean_inc_ref(x_1);
x_9 = lean_apply_1(x_1, x_2);
x_10 = 1;
x_2 = x_9;
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; 
lean_dec_ref(x_1);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_array_fget_borrowed(x_1, x_3);
x_12 = l_Lean_Level_getLevelOffset(x_11);
x_13 = l_Lean_Level_getOffset(x_11);
x_14 = lean_level_eq(x_12, x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_3, x_15);
lean_dec(x_3);
x_17 = lean_nat_add(x_2, x_5);
lean_dec(x_5);
x_18 = l___private_Lean_Level_0__Lean_Level_accMax(x_6, x_4, x_17);
x_3 = x_16;
x_4 = x_12;
x_5 = x_13;
x_6 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
lean_dec(x_4);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_3, x_20);
lean_dec(x_3);
x_3 = x_21;
x_4 = x_12;
x_5 = x_13;
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
lean_dec_ref(x_1);
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
x_5 = lean_array_fget_borrowed(x_1, x_2);
x_6 = l_Lean_Level_getLevelOffset(x_5);
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
lean_dec_ref(x_1);
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
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_fget_borrowed(x_1, x_3);
x_7 = l_Lean_Level_getOffset(x_6);
x_8 = lean_nat_dec_le(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_dec(x_3);
return x_8;
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
lean_dec_ref(x_1);
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
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = lean_array_get_borrowed(x_5, x_1, x_7);
lean_dec(x_7);
x_9 = l_Lean_Level_getOffset(x_8);
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
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___Lean_Level_normalize_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___Lean_Level_normalize_spec__0(x_4, x_2, x_3);
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
static lean_object* _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Level_normalize_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Level_normLt___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Level_normalize_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_5 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Level_normalize_spec__1___redArg___closed__0;
lean_inc(x_2);
x_6 = l_Array_qpartition___redArg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Level_normalize_spec__1___redArg(x_8, x_2, x_7);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Level_normalize_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Level_normalize_spec__1___redArg(x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Level_normalize_spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Level_normalize___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Level_normalize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Level.normalize", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_normalize___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_normalize___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Level_normalize___closed__2;
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_unsigned_to_nat(389u);
x_4 = l_Lean_Level_normalize___closed__1;
x_5 = l_Lean_Level_mvarId_x21___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normalize(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Level_isAlreadyNormalizedCheap(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Level_getOffset(x_1);
x_4 = l_Lean_Level_getLevelOffset(x_1);
switch (lean_obj_tag(x_4)) {
case 2:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_21; lean_object* x_26; lean_object* x_27; lean_object* x_30; uint8_t x_31; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Level_normalize___closed__0;
x_9 = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___Lean_Level_normalize_spec__0(x_5, x_2, x_8);
x_10 = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___Lean_Level_normalize_spec__0(x_6, x_2, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_30 = lean_array_get_size(x_10);
x_31 = lean_nat_dec_eq(x_30, x_7);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_36; 
x_32 = lean_nat_sub(x_30, x_11);
lean_dec(x_30);
x_36 = lean_nat_dec_le(x_7, x_32);
if (x_36 == 0)
{
lean_inc(x_32);
x_33 = x_32;
goto block_35;
}
else
{
x_33 = x_7;
goto block_35;
}
block_35:
{
uint8_t x_34; 
x_34 = lean_nat_dec_le(x_33, x_32);
if (x_34 == 0)
{
lean_dec(x_32);
lean_inc(x_33);
x_26 = x_33;
x_27 = x_33;
goto block_29;
}
else
{
x_26 = x_33;
x_27 = x_32;
goto block_29;
}
}
}
else
{
lean_dec(x_30);
x_21 = x_10;
goto block_25;
}
block_20:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_box(0);
x_15 = lean_array_get_borrowed(x_14, x_12, x_13);
x_16 = l_Lean_Level_getLevelOffset(x_15);
x_17 = l_Lean_Level_getOffset(x_15);
x_18 = lean_nat_add(x_13, x_11);
lean_dec(x_13);
x_19 = l___private_Lean_Level_0__Lean_Level_mkMaxAux(x_12, x_3, x_18, x_16, x_17, x_14);
lean_dec(x_3);
lean_dec_ref(x_12);
return x_19;
}
block_25:
{
lean_object* x_22; uint8_t x_23; 
x_22 = l___private_Lean_Level_0__Lean_Level_skipExplicit(x_21, x_7);
lean_inc(x_22);
x_23 = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_nat_sub(x_22, x_11);
lean_dec(x_22);
x_12 = x_21;
x_13 = x_24;
goto block_20;
}
else
{
x_12 = x_21;
x_13 = x_22;
goto block_20;
}
}
block_29:
{
lean_object* x_28; 
x_28 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Level_normalize_spec__1___redArg(x_10, x_26, x_27);
lean_dec(x_27);
x_21 = x_28;
goto block_25;
}
}
case 3:
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_4, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_4, 1);
lean_inc(x_38);
lean_dec_ref(x_4);
x_39 = l_Lean_Level_isNeverZero(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = l_Lean_Level_normalize(x_37);
lean_dec(x_37);
x_41 = l_Lean_Level_normalize(x_38);
lean_dec(x_38);
x_42 = l___private_Lean_Level_0__Lean_Level_mkIMaxAux(x_40, x_41);
x_43 = l_Lean_Level_addOffsetAux(x_3, x_42);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = l_Lean_Level_max___override(x_37, x_38);
x_45 = l_Lean_Level_normalize(x_44);
lean_dec(x_44);
x_46 = l_Lean_Level_addOffsetAux(x_3, x_45);
return x_46;
}
}
default: 
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_4);
lean_dec(x_3);
x_47 = l_Lean_Level_normalize___closed__3;
x_48 = l_panic___at___Lean_Level_normalize_spec__2(x_47);
return x_48;
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
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___Lean_Level_normalize_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___Lean_Level_normalize_spec__0(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Level_normalize_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Level_normalize_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Level_normalize_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Level_normalize_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
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
return x_3;
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
lean_object* x_2; lean_object* x_3; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_14; 
x_14 = lean_box(0);
return x_14;
}
case 1:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
case 2:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
x_2 = x_17;
x_3 = x_18;
goto block_13;
}
case 3:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_2 = x_19;
x_3 = x_20;
goto block_13;
}
default: 
{
lean_object* x_21; 
x_21 = lean_box(0);
return x_21;
}
}
block_13:
{
lean_object* x_4; 
x_4 = l_Lean_Level_dec(x_2);
if (lean_obj_tag(x_4) == 0)
{
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = l_Lean_Level_dec(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l_Lean_Level_max___override(x_5, x_8);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_Level_max___override(x_5, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
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
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorIdx(lean_object* x_1) {
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
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
default: 
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_PP_Result_ctorIdx(x_1);
lean_dec_ref(x_1);
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
static lean_object* _init_l_Lean_Level_PP_toResult___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Level_PP_toResult___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_toResult___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Level_PP_toResult___closed__1;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Level_PP_toResult___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Level_PP_toResult___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Level_PP_toResult___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_uniq", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_toResult___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Level_PP_toResult___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Level_PP_toResult___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\?u", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_toResult___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Level_PP_toResult___closed__6;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_toResult(lean_object* x_1, uint8_t x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; 
x_3 = l_Lean_Level_PP_toResult___closed__0;
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = l_Lean_Level_PP_toResult(x_4, x_2);
x_6 = l_Lean_Level_PP_Result_succ(x_5);
return x_6;
}
case 2:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = l_Lean_Level_PP_toResult(x_7, x_2);
x_10 = l_Lean_Level_PP_toResult(x_8, x_2);
x_11 = l_Lean_Level_PP_Result_max(x_9, x_10);
return x_11;
}
case 3:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec_ref(x_1);
x_14 = l_Lean_Level_PP_toResult(x_12, x_2);
x_15 = l_Lean_Level_PP_toResult(x_13, x_2);
x_16 = l_Lean_Level_PP_Result_imax(x_14, x_15);
return x_16;
}
case 4:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec_ref(x_1);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
default: 
{
if (x_2 == 0)
{
lean_object* x_19; 
lean_dec_ref(x_1);
x_19 = l_Lean_Level_PP_toResult___closed__3;
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec_ref(x_1);
x_21 = l_Lean_Level_PP_toResult___closed__5;
x_22 = l_Lean_Level_PP_toResult___closed__7;
x_23 = l_Lean_Name_replacePrefix(x_20, x_21, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_toResult___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
x_4 = l_Lean_Level_PP_toResult(x_1, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instReprData___lam__0___closed__0;
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
x_3 = l_Lean_reprLevel___closed__2____x40_Lean_Level_2248933020____hygCtx___hyg_98_;
x_4 = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1;
x_5 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
x_6 = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2;
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
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
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_box(1);
x_7 = 0;
x_8 = l_Lean_Level_PP_Result_format(x_4, x_7);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_6);
x_9 = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(x_5);
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_13 = lean_box(1);
x_14 = 0;
x_15 = l_Lean_Level_PP_Result_format(x_11, x_14);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(x_12);
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
static lean_object* _init_l_Lean_Level_PP_Result_format___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("+", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_format___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Level_PP_Result_format___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_format___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("max", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_format___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Level_PP_Result_format___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_format___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("imax", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_format___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Level_PP_Result_format___closed__4;
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
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = 1;
x_6 = l_Lean_Name_toString(x_4, x_5);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = 1;
x_9 = l_Lean_Name_toString(x_7, x_8);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
case 1:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = l_Nat_reprFast(x_12);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Nat_reprFast(x_14);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
case 2:
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_19, x_20);
if (x_21 == 1)
{
lean_free_object(x_1);
lean_dec(x_19);
x_1 = x_18;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_19, x_23);
lean_dec(x_19);
x_25 = l_Lean_Level_PP_Result_format(x_18, x_21);
x_26 = l_Lean_Level_PP_Result_format___closed__1;
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
x_27 = lean_nat_add(x_24, x_23);
lean_dec(x_24);
x_28 = l_Nat_reprFast(x_27);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
x_31 = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(x_30, x_2);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_1);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_nat_dec_eq(x_33, x_34);
if (x_35 == 1)
{
lean_dec(x_33);
x_1 = x_32;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_sub(x_33, x_37);
lean_dec(x_33);
x_39 = l_Lean_Level_PP_Result_format(x_32, x_35);
x_40 = l_Lean_Level_PP_Result_format___closed__1;
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_nat_add(x_38, x_37);
lean_dec(x_38);
x_43 = l_Nat_reprFast(x_42);
x_44 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_44);
x_46 = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(x_45, x_2);
return x_46;
}
}
}
case 3:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
lean_dec_ref(x_1);
x_48 = l_Lean_Level_PP_Result_format___closed__3;
x_49 = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(x_47);
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = 0;
x_52 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_51);
x_53 = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(x_52, x_2);
return x_53;
}
default: 
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
lean_dec_ref(x_1);
x_55 = l_Lean_Level_PP_Result_format___closed__5;
x_56 = l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(x_54);
x_57 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = 0;
x_59 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_58);
x_60 = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(x_59, x_2);
return x_60;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_format___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
x_4 = l_Lean_Level_PP_Result_format(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Level_PP_Result_quote_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(0);
x_3 = l_Lean_SourceInfo_fromRef(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Level", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("paren", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Level_PP_Result_quote___closed__4;
x_2 = l_Lean_Level_PP_Result_quote___closed__3;
x_3 = l_Lean_Level_PP_Result_quote___closed__2;
x_4 = l_Lean_Level_PP_Result_quote___closed__1;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0;
x_2 = l_Lean_Level_PP_Result_quote___closed__0;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instReprData___lam__0___closed__0;
x_2 = l_Lean_Level_PP_Result_quote___closed__0;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("addLit", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Level_PP_Result_quote___closed__8;
x_2 = l_Lean_Level_PP_Result_quote___closed__3;
x_3 = l_Lean_Level_PP_Result_quote___closed__2;
x_4 = l_Lean_Level_PP_Result_quote___closed__1;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Level_PP_Result_format___closed__2;
x_2 = l_Lean_Level_PP_Result_quote___closed__3;
x_3 = l_Lean_Level_PP_Result_quote___closed__2;
x_4 = l_Lean_Level_PP_Result_quote___closed__1;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Level_PP_Result_format___closed__2;
x_2 = l_Lean_Level_PP_Result_quote___closed__0;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Level_PP_Result_quote___closed__12;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Level_PP_Result_format___closed__4;
x_2 = l_Lean_Level_PP_Result_quote___closed__3;
x_3 = l_Lean_Level_PP_Result_quote___closed__2;
x_4 = l_Lean_Level_PP_Result_quote___closed__1;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Level_PP_Result_quote___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Level_PP_Result_format___closed__4;
x_2 = l_Lean_Level_PP_Result_quote___closed__0;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_PP_Result_quote(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec_ref(x_1);
x_13 = lean_mk_syntax_ident(x_12);
return x_13;
}
case 1:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec_ref(x_1);
x_15 = l_Nat_reprFast(x_14);
x_16 = lean_box(2);
x_17 = l_Lean_Syntax_mkNumLit(x_15, x_16);
return x_17;
}
case 2:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_20, x_21);
if (x_22 == 1)
{
lean_free_object(x_1);
lean_dec(x_20);
x_1 = x_19;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_20, x_24);
lean_dec(x_20);
x_26 = lean_box(0);
x_27 = l_Lean_SourceInfo_fromRef(x_26, x_22);
x_28 = l_Lean_Level_PP_Result_quote___closed__9;
x_29 = lean_unsigned_to_nat(65u);
x_30 = l_Lean_Level_PP_Result_quote(x_19, x_29);
x_31 = l_Lean_Level_PP_Result_format___closed__0;
lean_inc(x_27);
lean_ctor_set(x_1, 1, x_31);
lean_ctor_set(x_1, 0, x_27);
x_32 = lean_nat_add(x_25, x_24);
lean_dec(x_25);
x_33 = l_Nat_reprFast(x_32);
x_34 = lean_box(2);
x_35 = l_Lean_Syntax_mkNumLit(x_33, x_34);
x_36 = l_Lean_Syntax_node3(x_27, x_28, x_30, x_1, x_35);
x_3 = x_36;
goto block_11;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_1);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_nat_dec_eq(x_38, x_39);
if (x_40 == 1)
{
lean_dec(x_38);
x_1 = x_37;
goto _start;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_sub(x_38, x_42);
lean_dec(x_38);
x_44 = lean_box(0);
x_45 = l_Lean_SourceInfo_fromRef(x_44, x_40);
x_46 = l_Lean_Level_PP_Result_quote___closed__9;
x_47 = lean_unsigned_to_nat(65u);
x_48 = l_Lean_Level_PP_Result_quote(x_37, x_47);
x_49 = l_Lean_Level_PP_Result_format___closed__0;
lean_inc(x_45);
x_50 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_nat_add(x_43, x_42);
lean_dec(x_43);
x_52 = l_Nat_reprFast(x_51);
x_53 = lean_box(2);
x_54 = l_Lean_Syntax_mkNumLit(x_52, x_53);
x_55 = l_Lean_Syntax_node3(x_45, x_46, x_48, x_50, x_54);
x_3 = x_55;
goto block_11;
}
}
}
case 3:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; size_t x_63; size_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_56 = lean_ctor_get(x_1, 0);
lean_inc(x_56);
lean_dec_ref(x_1);
x_57 = l_Lean_Level_PP_Result_quote___closed__0;
x_58 = l_Lean_Level_PP_Result_quote___closed__10;
x_59 = l_Lean_Level_PP_Result_quote___closed__11;
x_60 = l_Lean_Level_PP_Result_quote___closed__13;
x_61 = l_Lean_Level_PP_Result_quote___closed__14;
x_62 = lean_array_mk(x_56);
x_63 = lean_array_size(x_62);
x_64 = 0;
x_65 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Level_PP_Result_quote_spec__0(x_63, x_64, x_62);
x_66 = l_Array_append___redArg(x_61, x_65);
lean_dec_ref(x_65);
x_67 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_67, 0, x_57);
lean_ctor_set(x_67, 1, x_60);
lean_ctor_set(x_67, 2, x_66);
x_68 = l_Lean_Syntax_node2(x_57, x_58, x_59, x_67);
x_3 = x_68;
goto block_11;
}
default: 
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; size_t x_76; size_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_69 = lean_ctor_get(x_1, 0);
lean_inc(x_69);
lean_dec_ref(x_1);
x_70 = l_Lean_Level_PP_Result_quote___closed__0;
x_71 = l_Lean_Level_PP_Result_quote___closed__15;
x_72 = l_Lean_Level_PP_Result_quote___closed__16;
x_73 = l_Lean_Level_PP_Result_quote___closed__13;
x_74 = l_Lean_Level_PP_Result_quote___closed__14;
x_75 = lean_array_mk(x_69);
x_76 = lean_array_size(x_75);
x_77 = 0;
x_78 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Level_PP_Result_quote_spec__0(x_76, x_77, x_75);
x_79 = l_Array_append___redArg(x_74, x_78);
lean_dec_ref(x_78);
x_80 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_80, 0, x_70);
lean_ctor_set(x_80, 1, x_73);
lean_ctor_set(x_80, 2, x_79);
x_81 = l_Lean_Syntax_node2(x_70, x_71, x_72, x_80);
x_3 = x_81;
goto block_11;
}
}
block_11:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_2);
if (x_5 == 0)
{
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l_Lean_Level_PP_Result_quote___closed__0;
x_7 = l_Lean_Level_PP_Result_quote___closed__5;
x_8 = l_Lean_Level_PP_Result_quote___closed__6;
x_9 = l_Lean_Level_PP_Result_quote___closed__7;
x_10 = l_Lean_Syntax_node3(x_6, x_7, x_8, x_3, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Level_PP_Result_quote_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Level_PP_Result_quote_spec__0(x_4, x_5, x_3);
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
LEAN_EXPORT lean_object* l_Lean_Level_format(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_3 = l_Lean_Level_PP_toResult(x_1, x_2);
x_4 = 1;
x_5 = l_Lean_Level_PP_Result_format(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_format___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
x_4 = l_Lean_Level_format(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToFormat___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = 1;
x_3 = l_Lean_Level_format(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Level_instToFormat() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Level_instToFormat___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_instToString___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Format_defWidth;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instToString___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = 1;
x_3 = l_Lean_Level_format(x_1, x_2);
x_4 = l_Lean_Level_instToString___lam__0___closed__0;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_format_pretty(x_3, x_4, x_5, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Level_instToString() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Level_instToString___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_quote(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Level_PP_toResult(x_1, x_3);
x_5 = l_Lean_Level_PP_Result_quote(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_quote___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Level_quote(x_1, x_2, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instQuoteMkStr1___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = 1;
x_4 = l_Lean_Level_quote(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Level_instQuoteMkStr1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Level_instQuoteMkStr1___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_10; 
x_10 = l_Lean_Level_isExplicit(x_2);
if (x_10 == 0)
{
x_3 = x_10;
goto block_9;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_Level_getOffset(x_2);
x_12 = l_Lean_Level_getOffset(x_1);
x_13 = lean_nat_dec_le(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
x_3 = x_13;
goto block_9;
}
block_9:
{
uint8_t x_4; 
x_4 = 1;
if (x_3 == 0)
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_level_eq(x_2, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_level_eq(x_2, x_6);
return x_8;
}
else
{
return x_4;
}
}
else
{
return x_3;
}
}
else
{
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_level_eq(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Lean_Level_isZero(x_1);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_Lean_Level_isZero(x_2);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(x_1, x_2);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(x_2, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_Level_getLevelOffset(x_1);
x_10 = l_Lean_Level_getLevelOffset(x_2);
x_11 = lean_level_eq(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_apply_1(x_3, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec_ref(x_3);
x_14 = l_Lean_Level_getOffset(x_2);
x_15 = l_Lean_Level_getOffset(x_1);
x_16 = lean_nat_dec_le(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
if (x_16 == 0)
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
else
{
lean_dec_ref(x_3);
lean_inc(x_2);
return x_2;
}
}
else
{
lean_dec_ref(x_3);
lean_inc(x_1);
return x_1;
}
}
else
{
lean_dec_ref(x_3);
lean_inc(x_1);
return x_1;
}
}
else
{
lean_dec_ref(x_3);
lean_inc(x_2);
return x_2;
}
}
else
{
lean_dec_ref(x_3);
lean_inc(x_1);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
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
uint8_t x_3; 
x_3 = lean_level_eq(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = l_Lean_Level_isZero(x_1);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Lean_Level_isZero(x_2);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(x_1, x_2);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Level_getLevelOffset(x_1);
x_9 = l_Lean_Level_getLevelOffset(x_2);
x_10 = lean_level_eq(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_Lean_Level_max___override(x_1, x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Level_getOffset(x_2);
x_13 = l_Lean_Level_getOffset(x_1);
x_14 = lean_nat_dec_le(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
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
}
}
LEAN_EXPORT lean_object* l_Lean_simpLevelMax_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_level_eq(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Lean_Level_isZero(x_1);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_Lean_Level_isZero(x_2);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(x_1, x_2);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(x_2, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_Level_getLevelOffset(x_1);
x_10 = l_Lean_Level_getLevelOffset(x_2);
x_11 = lean_level_eq(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Level_getOffset(x_2);
x_13 = l_Lean_Level_getOffset(x_1);
x_14 = lean_nat_dec_le(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
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
lean_dec_ref(x_3);
return x_1;
}
}
else
{
lean_dec_ref(x_3);
lean_dec(x_1);
return x_2;
}
}
else
{
lean_dec_ref(x_3);
lean_dec(x_1);
return x_2;
}
}
else
{
lean_object* x_10; 
lean_dec_ref(x_3);
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
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Level.0.Lean.Level.updateSucc!Impl", 48, 48);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("succ level expected", 19, 19);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__1;
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(543u);
x_4 = l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__0;
x_5 = l_Lean_Level_mvarId_x21___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
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
lean_inc_ref(x_1);
return x_1;
}
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2;
x_10 = l_panic___redArg(x_8, x_9);
return x_10;
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
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Level.0.Lean.Level.updateMax!Impl", 47, 47);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("max level expected", 18, 18);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__1;
x_2 = lean_unsigned_to_nat(19u);
x_3 = lean_unsigned_to_nat(554u);
x_4 = l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__0;
x_5 = l_Lean_Level_mvarId_x21___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ptr_addr(x_8);
x_11 = lean_ptr_addr(x_2);
x_12 = lean_usize_dec_eq(x_10, x_11);
if (x_12 == 0)
{
x_4 = x_12;
goto block_7;
}
else
{
size_t x_13; size_t x_14; uint8_t x_15; 
x_13 = lean_ptr_addr(x_9);
x_14 = lean_ptr_addr(x_3);
x_15 = lean_usize_dec_eq(x_13, x_14);
x_4 = x_15;
goto block_7;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_box(0);
x_17 = l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2;
x_18 = l_panic___redArg(x_16, x_17);
return x_18;
}
block_7:
{
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_mkLevelMax_x27(x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = l_Lean_simpLevelMax_x27(x_2, x_3, x_1);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
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
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Level.0.Lean.Level.updateIMax!Impl", 48, 48);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("imax level expected", 19, 19);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__1;
x_2 = lean_unsigned_to_nat(20u);
x_3 = lean_unsigned_to_nat(565u);
x_4 = l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__0;
x_5 = l_Lean_Level_mvarId_x21___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ptr_addr(x_8);
x_11 = lean_ptr_addr(x_2);
x_12 = lean_usize_dec_eq(x_10, x_11);
if (x_12 == 0)
{
x_4 = x_12;
goto block_7;
}
else
{
size_t x_13; size_t x_14; uint8_t x_15; 
x_13 = lean_ptr_addr(x_9);
x_14 = lean_ptr_addr(x_3);
x_15 = lean_usize_dec_eq(x_13, x_14);
x_4 = x_15;
goto block_7;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_box(0);
x_17 = l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2;
x_18 = l_panic___redArg(x_16, x_17);
return x_18;
}
block_7:
{
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_mkLevelIMax_x27(x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = l_Lean_simpLevelIMax_x27(x_2, x_3, x_1);
return x_6;
}
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
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc_ref(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l_Lean_Level_mkNaryMax(x_3);
x_7 = l_Lean_mkLevelMax_x27(x_5, x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_substParams_go(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Lean_Level_hasParam(x_2);
if (x_4 == 0)
{
lean_dec_ref(x_1);
return x_2;
}
else
{
lean_object* x_5; size_t x_6; size_t x_7; uint8_t x_8; 
lean_inc(x_3);
x_5 = l___private_Lean_Level_0__Lean_Level_substParams_go(x_1, x_3);
x_6 = lean_ptr_addr(x_3);
x_7 = lean_ptr_addr(x_5);
x_8 = lean_usize_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_2);
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
x_11 = lean_ctor_get(x_2, 1);
x_12 = l_Lean_Level_hasParam(x_2);
if (x_12 == 0)
{
lean_dec_ref(x_1);
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; size_t x_19; size_t x_20; uint8_t x_21; 
lean_inc(x_10);
lean_inc_ref(x_1);
x_13 = l___private_Lean_Level_0__Lean_Level_substParams_go(x_1, x_10);
lean_inc(x_11);
x_14 = l___private_Lean_Level_0__Lean_Level_substParams_go(x_1, x_11);
x_19 = lean_ptr_addr(x_10);
x_20 = lean_ptr_addr(x_13);
x_21 = lean_usize_dec_eq(x_19, x_20);
if (x_21 == 0)
{
x_15 = x_21;
goto block_18;
}
else
{
size_t x_22; size_t x_23; uint8_t x_24; 
x_22 = lean_ptr_addr(x_11);
x_23 = lean_ptr_addr(x_14);
x_24 = lean_usize_dec_eq(x_22, x_23);
x_15 = x_24;
goto block_18;
}
block_18:
{
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec_ref(x_2);
x_16 = l_Lean_mkLevelMax_x27(x_13, x_14);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = l_Lean_simpLevelMax_x27(x_13, x_14, x_2);
lean_dec_ref(x_2);
lean_dec(x_14);
lean_dec(x_13);
return x_17;
}
}
}
}
case 3:
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = l_Lean_Level_hasParam(x_2);
if (x_27 == 0)
{
lean_dec_ref(x_1);
return x_2;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; size_t x_34; size_t x_35; uint8_t x_36; 
lean_inc(x_25);
lean_inc_ref(x_1);
x_28 = l___private_Lean_Level_0__Lean_Level_substParams_go(x_1, x_25);
lean_inc(x_26);
x_29 = l___private_Lean_Level_0__Lean_Level_substParams_go(x_1, x_26);
x_34 = lean_ptr_addr(x_25);
x_35 = lean_ptr_addr(x_28);
x_36 = lean_usize_dec_eq(x_34, x_35);
if (x_36 == 0)
{
x_30 = x_36;
goto block_33;
}
else
{
size_t x_37; size_t x_38; uint8_t x_39; 
x_37 = lean_ptr_addr(x_26);
x_38 = lean_ptr_addr(x_29);
x_39 = lean_usize_dec_eq(x_37, x_38);
x_30 = x_39;
goto block_33;
}
block_33:
{
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec_ref(x_2);
x_31 = l_Lean_mkLevelIMax_x27(x_28, x_29);
return x_31;
}
else
{
lean_object* x_32; 
x_32 = l_Lean_simpLevelIMax_x27(x_28, x_29, x_2);
lean_dec_ref(x_2);
return x_32;
}
}
}
}
case 4:
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_2, 0);
lean_inc(x_40);
x_41 = lean_apply_1(x_1, x_40);
if (lean_obj_tag(x_41) == 0)
{
return x_2;
}
else
{
lean_object* x_42; 
lean_dec_ref(x_2);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
return x_42;
}
}
default: 
{
lean_dec_ref(x_1);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_substParams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Level_0__Lean_Level_substParams_go(x_2, x_1);
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
x_5 = l___private_Lean_Level_0__Lean_Level_substParams_go(x_4, x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_geq_go___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = l___private_Lean_Level_0__Lean_Level_geq_go(x_2, x_9);
if (x_11 == 0)
{
return x_11;
}
else
{
uint8_t x_12; 
x_12 = l___private_Lean_Level_0__Lean_Level_geq_go(x_2, x_10);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = l_Lean_Level_getLevelOffset(x_1);
x_14 = l_Lean_Level_getLevelOffset(x_2);
x_15 = lean_level_eq(x_14, x_13);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_Lean_Level_isZero(x_13);
lean_dec(x_13);
x_4 = x_16;
goto block_8;
}
else
{
lean_dec(x_13);
x_4 = x_15;
goto block_8;
}
}
block_8:
{
if (x_4 == 0)
{
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_Level_getOffset(x_1);
x_6 = l_Lean_Level_getOffset(x_2);
x_7 = lean_nat_dec_le(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
return x_7;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Level_0__Lean_Level_geq_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_9; 
x_9 = lean_level_eq(x_1, x_2);
if (x_9 == 0)
{
uint8_t x_10; 
switch (lean_obj_tag(x_1)) {
case 1:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_17; 
x_17 = 1;
return x_17;
}
case 1:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_2, 0);
x_1 = x_18;
x_2 = x_19;
goto _start;
}
case 2:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
x_3 = x_1;
x_4 = x_21;
x_5 = x_22;
goto block_8;
}
default: 
{
goto block_16;
}
}
}
case 2:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_23; 
x_23 = 1;
return x_23;
}
case 2:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
x_3 = x_1;
x_4 = x_24;
x_5 = x_25;
goto block_8;
}
default: 
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
x_28 = l___private_Lean_Level_0__Lean_Level_geq_go(x_26, x_2);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = l___private_Lean_Level_0__Lean_Level_geq_go(x_27, x_2);
x_10 = x_29;
goto block_13;
}
else
{
x_10 = x_28;
goto block_13;
}
}
}
}
case 3:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_30; 
x_30 = 1;
return x_30;
}
case 2:
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_2, 0);
x_32 = lean_ctor_get(x_2, 1);
x_3 = x_1;
x_4 = x_31;
x_5 = x_32;
goto block_8;
}
default: 
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_1, 1);
x_1 = x_33;
goto _start;
}
}
}
default: 
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_35; 
x_35 = 1;
return x_35;
}
case 2:
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_2, 0);
x_37 = lean_ctor_get(x_2, 1);
x_3 = x_1;
x_4 = x_36;
x_5 = x_37;
goto block_8;
}
default: 
{
goto block_16;
}
}
}
}
block_13:
{
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_box(0);
x_12 = l___private_Lean_Level_0__Lean_Level_geq_go___lam__0(x_2, x_1, x_11);
return x_12;
}
else
{
return x_10;
}
}
block_16:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_box(0);
x_15 = l___private_Lean_Level_0__Lean_Level_geq_go___lam__0(x_2, x_1, x_14);
return x_15;
}
}
else
{
return x_9;
}
block_8:
{
uint8_t x_6; 
x_6 = l___private_Lean_Level_0__Lean_Level_geq_go(x_3, x_4);
if (x_6 == 0)
{
return x_6;
}
else
{
x_1 = x_3;
x_2 = x_5;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Level_0__Lean_Level_geq_go___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Level_0__Lean_Level_geq_go(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_9; 
lean_dec(x_8);
lean_dec(x_4);
x_9 = lean_apply_1(x_3, x_2);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_3);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec_ref(x_2);
x_12 = lean_apply_3(x_4, x_1, x_10, x_11);
return x_12;
}
default: 
{
lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_apply_7(x_8, x_1, x_2, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_13;
}
}
}
case 1:
{
lean_dec(x_6);
lean_dec(x_5);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_14 = lean_apply_1(x_3, x_1);
return x_14;
}
case 1:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec_ref(x_1);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_dec_ref(x_2);
x_17 = lean_apply_2(x_7, x_15, x_16);
return x_17;
}
case 2:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_dec_ref(x_2);
x_20 = lean_apply_3(x_4, x_1, x_18, x_19);
return x_20;
}
default: 
{
lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_21 = lean_apply_7(x_8, x_1, x_2, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_21;
}
}
}
case 2:
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_4);
x_22 = lean_apply_1(x_3, x_1);
return x_22;
}
case 2:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_5);
lean_dec(x_3);
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
lean_dec_ref(x_2);
x_25 = lean_apply_3(x_4, x_1, x_23, x_24);
return x_25;
}
default: 
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_4);
lean_dec(x_3);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_dec_ref(x_1);
x_28 = lean_apply_5(x_5, x_26, x_27, x_2, lean_box(0), lean_box(0));
return x_28;
}
}
}
case 3:
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_29; 
lean_dec(x_6);
lean_dec(x_4);
x_29 = lean_apply_1(x_3, x_1);
return x_29;
}
case 2:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_6);
lean_dec(x_3);
x_30 = lean_ctor_get(x_2, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 1);
lean_inc(x_31);
lean_dec_ref(x_2);
x_32 = lean_apply_3(x_4, x_1, x_30, x_31);
return x_32;
}
default: 
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_4);
lean_dec(x_3);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
lean_dec_ref(x_1);
x_35 = lean_apply_5(x_6, x_33, x_34, x_2, lean_box(0), lean_box(0));
return x_35;
}
}
}
default: 
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_36; 
lean_dec(x_8);
lean_dec(x_4);
x_36 = lean_apply_1(x_3, x_1);
return x_36;
}
case 2:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_8);
lean_dec(x_3);
x_37 = lean_ctor_get(x_2, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_2, 1);
lean_inc(x_38);
lean_dec_ref(x_2);
x_39 = lean_apply_3(x_4, x_1, x_37, x_38);
return x_39;
}
default: 
{
lean_object* x_40; 
lean_dec(x_4);
lean_dec(x_3);
x_40 = lean_apply_7(x_8, x_1, x_2, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_40;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_geq_go_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Level_0__Lean_Level_geq_go_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isIMax_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_2(x_3, x_1, lean_box(0));
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_isIMax_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Level_0__Lean_Level_isIMax_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_geq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Level_normalize(x_1);
x_4 = l_Lean_Level_normalize(x_2);
x_5 = l___private_Lean_Level_0__Lean_Level_geq_go(x_3, x_4);
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
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Level_collectMVars_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 4);
x_6 = l_Lean_Name_quickCmp(x_1, x_3);
switch (x_6) {
case 0:
{
x_2 = x_4;
goto _start;
}
case 1:
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
default: 
{
x_2 = x_5;
goto _start;
}
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Level_collectMVars_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Level_collectMVars_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___Lean_Level_collectMVars_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 4);
lean_inc(x_8);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 x_9 = x_3;
} else {
 lean_dec_ref(x_3);
 x_9 = lean_box(0);
}
x_10 = l_Lean_Name_quickCmp(x_1, x_5);
switch (x_10) {
case 0:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_11 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_Level_collectMVars_spec__1___redArg(x_1, x_2, x_7);
x_12 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_11, 4);
lean_inc(x_18);
x_19 = lean_unsigned_to_nat(3u);
x_20 = lean_nat_mul(x_19, x_13);
x_21 = lean_nat_dec_lt(x_20, x_14);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_22 = lean_nat_add(x_12, x_14);
lean_dec(x_14);
x_23 = lean_nat_add(x_22, x_13);
lean_dec(x_22);
if (lean_is_scalar(x_9)) {
 x_24 = lean_alloc_ctor(0, 5, 0);
} else {
 x_24 = x_9;
}
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
lean_ctor_set(x_24, 2, x_6);
lean_ctor_set(x_24, 3, x_11);
lean_ctor_set(x_24, 4, x_8);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 x_25 = x_11;
} else {
 lean_dec_ref(x_11);
 x_25 = lean_box(0);
}
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
x_29 = lean_ctor_get(x_18, 2);
x_30 = lean_ctor_get(x_18, 3);
x_31 = lean_ctor_get(x_18, 4);
x_32 = lean_unsigned_to_nat(2u);
x_33 = lean_nat_mul(x_32, x_26);
x_34 = lean_nat_dec_lt(x_27, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_45; lean_object* x_46; 
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 x_35 = x_18;
} else {
 lean_dec_ref(x_18);
 x_35 = lean_box(0);
}
x_36 = lean_nat_add(x_12, x_14);
lean_dec(x_14);
x_37 = lean_nat_add(x_36, x_13);
lean_dec(x_36);
x_45 = lean_nat_add(x_12, x_26);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_30, 0);
lean_inc(x_53);
x_46 = x_53;
goto block_52;
}
else
{
lean_object* x_54; 
x_54 = lean_unsigned_to_nat(0u);
x_46 = x_54;
goto block_52;
}
block_44:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_nat_add(x_39, x_40);
lean_dec(x_40);
lean_dec(x_39);
if (lean_is_scalar(x_35)) {
 x_42 = lean_alloc_ctor(0, 5, 0);
} else {
 x_42 = x_35;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_5);
lean_ctor_set(x_42, 2, x_6);
lean_ctor_set(x_42, 3, x_31);
lean_ctor_set(x_42, 4, x_8);
if (lean_is_scalar(x_25)) {
 x_43 = lean_alloc_ctor(0, 5, 0);
} else {
 x_43 = x_25;
}
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_28);
lean_ctor_set(x_43, 2, x_29);
lean_ctor_set(x_43, 3, x_38);
lean_ctor_set(x_43, 4, x_42);
return x_43;
}
block_52:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_nat_add(x_45, x_46);
lean_dec(x_46);
lean_dec(x_45);
if (lean_is_scalar(x_9)) {
 x_48 = lean_alloc_ctor(0, 5, 0);
} else {
 x_48 = x_9;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_15);
lean_ctor_set(x_48, 2, x_16);
lean_ctor_set(x_48, 3, x_17);
lean_ctor_set(x_48, 4, x_30);
x_49 = lean_nat_add(x_12, x_13);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_31, 0);
lean_inc(x_50);
x_38 = x_48;
x_39 = x_49;
x_40 = x_50;
goto block_44;
}
else
{
lean_object* x_51; 
x_51 = lean_unsigned_to_nat(0u);
x_38 = x_48;
x_39 = x_49;
x_40 = x_51;
goto block_44;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_9);
x_55 = lean_nat_add(x_12, x_14);
lean_dec(x_14);
x_56 = lean_nat_add(x_55, x_13);
lean_dec(x_55);
x_57 = lean_nat_add(x_12, x_13);
x_58 = lean_nat_add(x_57, x_27);
lean_dec(x_57);
lean_inc_ref(x_8);
if (lean_is_scalar(x_25)) {
 x_59 = lean_alloc_ctor(0, 5, 0);
} else {
 x_59 = x_25;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_5);
lean_ctor_set(x_59, 2, x_6);
lean_ctor_set(x_59, 3, x_18);
lean_ctor_set(x_59, 4, x_8);
x_60 = !lean_is_exclusive(x_8);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_8, 4);
lean_dec(x_61);
x_62 = lean_ctor_get(x_8, 3);
lean_dec(x_62);
x_63 = lean_ctor_get(x_8, 2);
lean_dec(x_63);
x_64 = lean_ctor_get(x_8, 1);
lean_dec(x_64);
x_65 = lean_ctor_get(x_8, 0);
lean_dec(x_65);
lean_ctor_set(x_8, 4, x_59);
lean_ctor_set(x_8, 3, x_17);
lean_ctor_set(x_8, 2, x_16);
lean_ctor_set(x_8, 1, x_15);
lean_ctor_set(x_8, 0, x_56);
return x_8;
}
else
{
lean_object* x_66; 
lean_dec(x_8);
x_66 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_66, 0, x_56);
lean_ctor_set(x_66, 1, x_15);
lean_ctor_set(x_66, 2, x_16);
lean_ctor_set(x_66, 3, x_17);
lean_ctor_set(x_66, 4, x_59);
return x_66;
}
}
}
}
else
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_11, 3);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_11);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_ctor_get(x_11, 4);
x_70 = lean_ctor_get(x_11, 1);
x_71 = lean_ctor_get(x_11, 2);
x_72 = lean_ctor_get(x_11, 3);
lean_dec(x_72);
x_73 = lean_ctor_get(x_11, 0);
lean_dec(x_73);
x_74 = lean_unsigned_to_nat(3u);
lean_inc(x_69);
lean_ctor_set(x_11, 3, x_69);
lean_ctor_set(x_11, 2, x_6);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 0, x_12);
if (lean_is_scalar(x_9)) {
 x_75 = lean_alloc_ctor(0, 5, 0);
} else {
 x_75 = x_9;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_70);
lean_ctor_set(x_75, 2, x_71);
lean_ctor_set(x_75, 3, x_67);
lean_ctor_set(x_75, 4, x_11);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_11, 4);
x_77 = lean_ctor_get(x_11, 1);
x_78 = lean_ctor_get(x_11, 2);
lean_inc(x_76);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_11);
x_79 = lean_unsigned_to_nat(3u);
lean_inc(x_76);
x_80 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_80, 0, x_12);
lean_ctor_set(x_80, 1, x_5);
lean_ctor_set(x_80, 2, x_6);
lean_ctor_set(x_80, 3, x_76);
lean_ctor_set(x_80, 4, x_76);
if (lean_is_scalar(x_9)) {
 x_81 = lean_alloc_ctor(0, 5, 0);
} else {
 x_81 = x_9;
}
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_77);
lean_ctor_set(x_81, 2, x_78);
lean_ctor_set(x_81, 3, x_67);
lean_ctor_set(x_81, 4, x_80);
return x_81;
}
}
else
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_11, 4);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_11);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_84 = lean_ctor_get(x_11, 1);
x_85 = lean_ctor_get(x_11, 2);
x_86 = lean_ctor_get(x_11, 4);
lean_dec(x_86);
x_87 = lean_ctor_get(x_11, 3);
lean_dec(x_87);
x_88 = lean_ctor_get(x_11, 0);
lean_dec(x_88);
x_89 = !lean_is_exclusive(x_82);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_90 = lean_ctor_get(x_82, 1);
x_91 = lean_ctor_get(x_82, 2);
x_92 = lean_ctor_get(x_82, 4);
lean_dec(x_92);
x_93 = lean_ctor_get(x_82, 3);
lean_dec(x_93);
x_94 = lean_ctor_get(x_82, 0);
lean_dec(x_94);
x_95 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_82, 4, x_67);
lean_ctor_set(x_82, 3, x_67);
lean_ctor_set(x_82, 2, x_85);
lean_ctor_set(x_82, 1, x_84);
lean_ctor_set(x_82, 0, x_12);
lean_ctor_set(x_11, 4, x_67);
lean_ctor_set(x_11, 2, x_6);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 0, x_12);
if (lean_is_scalar(x_9)) {
 x_96 = lean_alloc_ctor(0, 5, 0);
} else {
 x_96 = x_9;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_90);
lean_ctor_set(x_96, 2, x_91);
lean_ctor_set(x_96, 3, x_82);
lean_ctor_set(x_96, 4, x_11);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_82, 1);
x_98 = lean_ctor_get(x_82, 2);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_82);
x_99 = lean_unsigned_to_nat(3u);
x_100 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_100, 0, x_12);
lean_ctor_set(x_100, 1, x_84);
lean_ctor_set(x_100, 2, x_85);
lean_ctor_set(x_100, 3, x_67);
lean_ctor_set(x_100, 4, x_67);
lean_ctor_set(x_11, 4, x_67);
lean_ctor_set(x_11, 2, x_6);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 0, x_12);
if (lean_is_scalar(x_9)) {
 x_101 = lean_alloc_ctor(0, 5, 0);
} else {
 x_101 = x_9;
}
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_97);
lean_ctor_set(x_101, 2, x_98);
lean_ctor_set(x_101, 3, x_100);
lean_ctor_set(x_101, 4, x_11);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_102 = lean_ctor_get(x_11, 1);
x_103 = lean_ctor_get(x_11, 2);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_11);
x_104 = lean_ctor_get(x_82, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_82, 2);
lean_inc(x_105);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 lean_ctor_release(x_82, 2);
 lean_ctor_release(x_82, 3);
 lean_ctor_release(x_82, 4);
 x_106 = x_82;
} else {
 lean_dec_ref(x_82);
 x_106 = lean_box(0);
}
x_107 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(0, 5, 0);
} else {
 x_108 = x_106;
}
lean_ctor_set(x_108, 0, x_12);
lean_ctor_set(x_108, 1, x_102);
lean_ctor_set(x_108, 2, x_103);
lean_ctor_set(x_108, 3, x_67);
lean_ctor_set(x_108, 4, x_67);
x_109 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_109, 0, x_12);
lean_ctor_set(x_109, 1, x_5);
lean_ctor_set(x_109, 2, x_6);
lean_ctor_set(x_109, 3, x_67);
lean_ctor_set(x_109, 4, x_67);
if (lean_is_scalar(x_9)) {
 x_110 = lean_alloc_ctor(0, 5, 0);
} else {
 x_110 = x_9;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_104);
lean_ctor_set(x_110, 2, x_105);
lean_ctor_set(x_110, 3, x_108);
lean_ctor_set(x_110, 4, x_109);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_9)) {
 x_112 = lean_alloc_ctor(0, 5, 0);
} else {
 x_112 = x_9;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_5);
lean_ctor_set(x_112, 2, x_6);
lean_ctor_set(x_112, 3, x_11);
lean_ctor_set(x_112, 4, x_82);
return x_112;
}
}
}
}
case 1:
{
lean_object* x_113; 
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_9)) {
 x_113 = lean_alloc_ctor(0, 5, 0);
} else {
 x_113 = x_9;
}
lean_ctor_set(x_113, 0, x_4);
lean_ctor_set(x_113, 1, x_1);
lean_ctor_set(x_113, 2, x_2);
lean_ctor_set(x_113, 3, x_7);
lean_ctor_set(x_113, 4, x_8);
return x_113;
}
default: 
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_4);
x_114 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_Level_collectMVars_spec__1___redArg(x_1, x_2, x_8);
x_115 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_116 = lean_ctor_get(x_7, 0);
x_117 = lean_ctor_get(x_114, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_114, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_114, 2);
lean_inc(x_119);
x_120 = lean_ctor_get(x_114, 3);
lean_inc(x_120);
x_121 = lean_ctor_get(x_114, 4);
lean_inc(x_121);
x_122 = lean_unsigned_to_nat(3u);
x_123 = lean_nat_mul(x_122, x_116);
x_124 = lean_nat_dec_lt(x_123, x_117);
lean_dec(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
x_125 = lean_nat_add(x_115, x_116);
x_126 = lean_nat_add(x_125, x_117);
lean_dec(x_117);
lean_dec(x_125);
if (lean_is_scalar(x_9)) {
 x_127 = lean_alloc_ctor(0, 5, 0);
} else {
 x_127 = x_9;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_5);
lean_ctor_set(x_127, 2, x_6);
lean_ctor_set(x_127, 3, x_7);
lean_ctor_set(x_127, 4, x_114);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 lean_ctor_release(x_114, 2);
 lean_ctor_release(x_114, 3);
 lean_ctor_release(x_114, 4);
 x_128 = x_114;
} else {
 lean_dec_ref(x_114);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_120, 0);
x_130 = lean_ctor_get(x_120, 1);
x_131 = lean_ctor_get(x_120, 2);
x_132 = lean_ctor_get(x_120, 3);
x_133 = lean_ctor_get(x_120, 4);
x_134 = lean_ctor_get(x_121, 0);
x_135 = lean_unsigned_to_nat(2u);
x_136 = lean_nat_mul(x_135, x_134);
x_137 = lean_nat_dec_lt(x_129, x_136);
lean_dec(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_148; 
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 lean_ctor_release(x_120, 2);
 lean_ctor_release(x_120, 3);
 lean_ctor_release(x_120, 4);
 x_138 = x_120;
} else {
 lean_dec_ref(x_120);
 x_138 = lean_box(0);
}
x_139 = lean_nat_add(x_115, x_116);
x_140 = lean_nat_add(x_139, x_117);
lean_dec(x_117);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_155; 
x_155 = lean_ctor_get(x_132, 0);
lean_inc(x_155);
x_148 = x_155;
goto block_154;
}
else
{
lean_object* x_156; 
x_156 = lean_unsigned_to_nat(0u);
x_148 = x_156;
goto block_154;
}
block_147:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_nat_add(x_141, x_143);
lean_dec(x_143);
lean_dec(x_141);
if (lean_is_scalar(x_138)) {
 x_145 = lean_alloc_ctor(0, 5, 0);
} else {
 x_145 = x_138;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_118);
lean_ctor_set(x_145, 2, x_119);
lean_ctor_set(x_145, 3, x_133);
lean_ctor_set(x_145, 4, x_121);
if (lean_is_scalar(x_128)) {
 x_146 = lean_alloc_ctor(0, 5, 0);
} else {
 x_146 = x_128;
}
lean_ctor_set(x_146, 0, x_140);
lean_ctor_set(x_146, 1, x_130);
lean_ctor_set(x_146, 2, x_131);
lean_ctor_set(x_146, 3, x_142);
lean_ctor_set(x_146, 4, x_145);
return x_146;
}
block_154:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_nat_add(x_139, x_148);
lean_dec(x_148);
lean_dec(x_139);
if (lean_is_scalar(x_9)) {
 x_150 = lean_alloc_ctor(0, 5, 0);
} else {
 x_150 = x_9;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_5);
lean_ctor_set(x_150, 2, x_6);
lean_ctor_set(x_150, 3, x_7);
lean_ctor_set(x_150, 4, x_132);
x_151 = lean_nat_add(x_115, x_134);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_152; 
x_152 = lean_ctor_get(x_133, 0);
lean_inc(x_152);
x_141 = x_151;
x_142 = x_150;
x_143 = x_152;
goto block_147;
}
else
{
lean_object* x_153; 
x_153 = lean_unsigned_to_nat(0u);
x_141 = x_151;
x_142 = x_150;
x_143 = x_153;
goto block_147;
}
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
lean_dec(x_9);
x_157 = lean_nat_add(x_115, x_116);
x_158 = lean_nat_add(x_157, x_117);
lean_dec(x_117);
x_159 = lean_nat_add(x_157, x_129);
lean_dec(x_157);
lean_inc_ref(x_7);
if (lean_is_scalar(x_128)) {
 x_160 = lean_alloc_ctor(0, 5, 0);
} else {
 x_160 = x_128;
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_5);
lean_ctor_set(x_160, 2, x_6);
lean_ctor_set(x_160, 3, x_7);
lean_ctor_set(x_160, 4, x_120);
x_161 = !lean_is_exclusive(x_7);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_162 = lean_ctor_get(x_7, 4);
lean_dec(x_162);
x_163 = lean_ctor_get(x_7, 3);
lean_dec(x_163);
x_164 = lean_ctor_get(x_7, 2);
lean_dec(x_164);
x_165 = lean_ctor_get(x_7, 1);
lean_dec(x_165);
x_166 = lean_ctor_get(x_7, 0);
lean_dec(x_166);
lean_ctor_set(x_7, 4, x_121);
lean_ctor_set(x_7, 3, x_160);
lean_ctor_set(x_7, 2, x_119);
lean_ctor_set(x_7, 1, x_118);
lean_ctor_set(x_7, 0, x_158);
return x_7;
}
else
{
lean_object* x_167; 
lean_dec(x_7);
x_167 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_167, 0, x_158);
lean_ctor_set(x_167, 1, x_118);
lean_ctor_set(x_167, 2, x_119);
lean_ctor_set(x_167, 3, x_160);
lean_ctor_set(x_167, 4, x_121);
return x_167;
}
}
}
}
else
{
lean_object* x_168; 
x_168 = lean_ctor_get(x_114, 3);
lean_inc(x_168);
if (lean_obj_tag(x_168) == 0)
{
uint8_t x_169; 
x_169 = !lean_is_exclusive(x_114);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_170 = lean_ctor_get(x_114, 4);
x_171 = lean_ctor_get(x_114, 3);
lean_dec(x_171);
x_172 = lean_ctor_get(x_114, 0);
lean_dec(x_172);
x_173 = !lean_is_exclusive(x_168);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_174 = lean_ctor_get(x_168, 1);
x_175 = lean_ctor_get(x_168, 2);
x_176 = lean_ctor_get(x_168, 4);
lean_dec(x_176);
x_177 = lean_ctor_get(x_168, 3);
lean_dec(x_177);
x_178 = lean_ctor_get(x_168, 0);
lean_dec(x_178);
x_179 = lean_unsigned_to_nat(3u);
lean_inc_n(x_170, 2);
lean_ctor_set(x_168, 4, x_170);
lean_ctor_set(x_168, 3, x_170);
lean_ctor_set(x_168, 2, x_6);
lean_ctor_set(x_168, 1, x_5);
lean_ctor_set(x_168, 0, x_115);
lean_inc(x_170);
lean_ctor_set(x_114, 3, x_170);
lean_ctor_set(x_114, 0, x_115);
if (lean_is_scalar(x_9)) {
 x_180 = lean_alloc_ctor(0, 5, 0);
} else {
 x_180 = x_9;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_174);
lean_ctor_set(x_180, 2, x_175);
lean_ctor_set(x_180, 3, x_168);
lean_ctor_set(x_180, 4, x_114);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_181 = lean_ctor_get(x_168, 1);
x_182 = lean_ctor_get(x_168, 2);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_168);
x_183 = lean_unsigned_to_nat(3u);
lean_inc_n(x_170, 2);
x_184 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_184, 0, x_115);
lean_ctor_set(x_184, 1, x_5);
lean_ctor_set(x_184, 2, x_6);
lean_ctor_set(x_184, 3, x_170);
lean_ctor_set(x_184, 4, x_170);
lean_inc(x_170);
lean_ctor_set(x_114, 3, x_170);
lean_ctor_set(x_114, 0, x_115);
if (lean_is_scalar(x_9)) {
 x_185 = lean_alloc_ctor(0, 5, 0);
} else {
 x_185 = x_9;
}
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_181);
lean_ctor_set(x_185, 2, x_182);
lean_ctor_set(x_185, 3, x_184);
lean_ctor_set(x_185, 4, x_114);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_186 = lean_ctor_get(x_114, 4);
x_187 = lean_ctor_get(x_114, 1);
x_188 = lean_ctor_get(x_114, 2);
lean_inc(x_186);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_114);
x_189 = lean_ctor_get(x_168, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_168, 2);
lean_inc(x_190);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 lean_ctor_release(x_168, 2);
 lean_ctor_release(x_168, 3);
 lean_ctor_release(x_168, 4);
 x_191 = x_168;
} else {
 lean_dec_ref(x_168);
 x_191 = lean_box(0);
}
x_192 = lean_unsigned_to_nat(3u);
lean_inc_n(x_186, 2);
if (lean_is_scalar(x_191)) {
 x_193 = lean_alloc_ctor(0, 5, 0);
} else {
 x_193 = x_191;
}
lean_ctor_set(x_193, 0, x_115);
lean_ctor_set(x_193, 1, x_5);
lean_ctor_set(x_193, 2, x_6);
lean_ctor_set(x_193, 3, x_186);
lean_ctor_set(x_193, 4, x_186);
lean_inc(x_186);
x_194 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_194, 0, x_115);
lean_ctor_set(x_194, 1, x_187);
lean_ctor_set(x_194, 2, x_188);
lean_ctor_set(x_194, 3, x_186);
lean_ctor_set(x_194, 4, x_186);
if (lean_is_scalar(x_9)) {
 x_195 = lean_alloc_ctor(0, 5, 0);
} else {
 x_195 = x_9;
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_189);
lean_ctor_set(x_195, 2, x_190);
lean_ctor_set(x_195, 3, x_193);
lean_ctor_set(x_195, 4, x_194);
return x_195;
}
}
else
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_114, 4);
lean_inc(x_196);
if (lean_obj_tag(x_196) == 0)
{
uint8_t x_197; 
x_197 = !lean_is_exclusive(x_114);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_198 = lean_ctor_get(x_114, 1);
x_199 = lean_ctor_get(x_114, 2);
x_200 = lean_ctor_get(x_114, 4);
lean_dec(x_200);
x_201 = lean_ctor_get(x_114, 3);
lean_dec(x_201);
x_202 = lean_ctor_get(x_114, 0);
lean_dec(x_202);
x_203 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_114, 4, x_168);
lean_ctor_set(x_114, 2, x_6);
lean_ctor_set(x_114, 1, x_5);
lean_ctor_set(x_114, 0, x_115);
if (lean_is_scalar(x_9)) {
 x_204 = lean_alloc_ctor(0, 5, 0);
} else {
 x_204 = x_9;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_198);
lean_ctor_set(x_204, 2, x_199);
lean_ctor_set(x_204, 3, x_114);
lean_ctor_set(x_204, 4, x_196);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_205 = lean_ctor_get(x_114, 1);
x_206 = lean_ctor_get(x_114, 2);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_114);
x_207 = lean_unsigned_to_nat(3u);
x_208 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_208, 0, x_115);
lean_ctor_set(x_208, 1, x_5);
lean_ctor_set(x_208, 2, x_6);
lean_ctor_set(x_208, 3, x_168);
lean_ctor_set(x_208, 4, x_168);
if (lean_is_scalar(x_9)) {
 x_209 = lean_alloc_ctor(0, 5, 0);
} else {
 x_209 = x_9;
}
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_205);
lean_ctor_set(x_209, 2, x_206);
lean_ctor_set(x_209, 3, x_208);
lean_ctor_set(x_209, 4, x_196);
return x_209;
}
}
else
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_9)) {
 x_211 = lean_alloc_ctor(0, 5, 0);
} else {
 x_211 = x_9;
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_5);
lean_ctor_set(x_211, 2, x_6);
lean_ctor_set(x_211, 3, x_196);
lean_ctor_set(x_211, 4, x_114);
return x_211;
}
}
}
}
}
}
else
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_unsigned_to_nat(1u);
x_213 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_1);
lean_ctor_set(x_213, 2, x_2);
lean_ctor_set(x_213, 3, x_3);
lean_ctor_set(x_213, 4, x_3);
return x_213;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___Lean_Level_collectMVars_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_Level_collectMVars_spec__1___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_collectMVars(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec_ref(x_1);
x_1 = x_8;
goto _start;
}
case 2:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec_ref(x_1);
x_3 = x_10;
x_4 = x_11;
goto block_7;
}
case 3:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec_ref(x_1);
x_3 = x_12;
x_4 = x_13;
goto block_7;
}
case 5:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec_ref(x_1);
x_15 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Level_collectMVars_spec__0___redArg(x_14, x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_Level_collectMVars_spec__1___redArg(x_14, x_16, x_2);
return x_17;
}
else
{
lean_dec(x_14);
return x_2;
}
}
default: 
{
lean_dec(x_1);
return x_2;
}
}
block_7:
{
lean_object* x_5; 
x_5 = l_Lean_Level_collectMVars(x_4, x_2);
x_1 = x_3;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Level_collectMVars_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Level_collectMVars_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Level_collectMVars_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Level_collectMVars_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Level_0__Lean_Level_find_x3f_visit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_8; uint8_t x_9; 
lean_inc_ref(x_1);
lean_inc(x_2);
x_8 = lean_apply_1(x_1, x_2);
x_9 = lean_unbox(x_8);
if (x_9 == 0)
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec_ref(x_2);
x_2 = x_10;
goto _start;
}
case 2:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec_ref(x_2);
x_3 = x_12;
x_4 = x_13;
goto block_7;
}
case 3:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec_ref(x_2);
x_3 = x_14;
x_4 = x_15;
goto block_7;
}
default: 
{
lean_object* x_16; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_16 = lean_box(0);
return x_16;
}
}
}
else
{
lean_object* x_17; 
lean_dec_ref(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_2);
return x_17;
}
block_7:
{
lean_object* x_5; 
lean_inc_ref(x_1);
x_5 = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
x_2 = x_4;
goto _start;
}
else
{
lean_dec(x_4);
lean_dec_ref(x_1);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_find_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_any(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec_ref(x_3);
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
lean_object* initialize_Init_Data_Array_QSort(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_PersistentHashMap(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_PersistentHashSet(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Hygiene(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Name(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Format(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Option_Coe(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_TreeSet_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Level(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_QSort(builtin, lean_io_mk_world());
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
res = initialize_Init_Data_Option_Coe(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeSet_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedData = _init_l_Lean_instInhabitedData();
l_Lean_instBEqData = _init_l_Lean_instBEqData();
lean_mark_persistent(l_Lean_instBEqData);
l_Lean_instReprData___lam__0___closed__0 = _init_l_Lean_instReprData___lam__0___closed__0();
lean_mark_persistent(l_Lean_instReprData___lam__0___closed__0);
l_Lean_instReprData___lam__0___closed__1 = _init_l_Lean_instReprData___lam__0___closed__1();
lean_mark_persistent(l_Lean_instReprData___lam__0___closed__1);
l_Lean_instReprData___lam__0___closed__2 = _init_l_Lean_instReprData___lam__0___closed__2();
lean_mark_persistent(l_Lean_instReprData___lam__0___closed__2);
l_Lean_instReprData___lam__0___closed__3 = _init_l_Lean_instReprData___lam__0___closed__3();
lean_mark_persistent(l_Lean_instReprData___lam__0___closed__3);
l_Lean_instReprData___lam__0___closed__4 = _init_l_Lean_instReprData___lam__0___closed__4();
lean_mark_persistent(l_Lean_instReprData___lam__0___closed__4);
l_Lean_instReprData___lam__0___closed__5 = _init_l_Lean_instReprData___lam__0___closed__5();
lean_mark_persistent(l_Lean_instReprData___lam__0___closed__5);
l_Lean_instReprData___lam__0___closed__6 = _init_l_Lean_instReprData___lam__0___closed__6();
lean_mark_persistent(l_Lean_instReprData___lam__0___closed__6);
l_Lean_instReprData = _init_l_Lean_instReprData();
lean_mark_persistent(l_Lean_instReprData);
l_Lean_instInhabitedLevelMVarId = _init_l_Lean_instInhabitedLevelMVarId();
lean_mark_persistent(l_Lean_instInhabitedLevelMVarId);
l_Lean_instBEqLevelMVarId___closed__0 = _init_l_Lean_instBEqLevelMVarId___closed__0();
lean_mark_persistent(l_Lean_instBEqLevelMVarId___closed__0);
l_Lean_instBEqLevelMVarId = _init_l_Lean_instBEqLevelMVarId();
lean_mark_persistent(l_Lean_instBEqLevelMVarId);
l_Lean_instHashableLevelMVarId___closed__0 = _init_l_Lean_instHashableLevelMVarId___closed__0();
lean_mark_persistent(l_Lean_instHashableLevelMVarId___closed__0);
l_Lean_instHashableLevelMVarId = _init_l_Lean_instHashableLevelMVarId();
lean_mark_persistent(l_Lean_instHashableLevelMVarId);
l_Lean_reprLevelMVarId___redArg___closed__0____x40_Lean_Level_3927547624____hygCtx___hyg_44_ = _init_l_Lean_reprLevelMVarId___redArg___closed__0____x40_Lean_Level_3927547624____hygCtx___hyg_44_();
lean_mark_persistent(l_Lean_reprLevelMVarId___redArg___closed__0____x40_Lean_Level_3927547624____hygCtx___hyg_44_);
l_Lean_reprLevelMVarId___redArg___closed__1____x40_Lean_Level_3927547624____hygCtx___hyg_44_ = _init_l_Lean_reprLevelMVarId___redArg___closed__1____x40_Lean_Level_3927547624____hygCtx___hyg_44_();
lean_mark_persistent(l_Lean_reprLevelMVarId___redArg___closed__1____x40_Lean_Level_3927547624____hygCtx___hyg_44_);
l_Lean_reprLevelMVarId___redArg___closed__2____x40_Lean_Level_3927547624____hygCtx___hyg_44_ = _init_l_Lean_reprLevelMVarId___redArg___closed__2____x40_Lean_Level_3927547624____hygCtx___hyg_44_();
lean_mark_persistent(l_Lean_reprLevelMVarId___redArg___closed__2____x40_Lean_Level_3927547624____hygCtx___hyg_44_);
l_Lean_reprLevelMVarId___redArg___closed__3____x40_Lean_Level_3927547624____hygCtx___hyg_44_ = _init_l_Lean_reprLevelMVarId___redArg___closed__3____x40_Lean_Level_3927547624____hygCtx___hyg_44_();
lean_mark_persistent(l_Lean_reprLevelMVarId___redArg___closed__3____x40_Lean_Level_3927547624____hygCtx___hyg_44_);
l_Lean_reprLevelMVarId___redArg___closed__4____x40_Lean_Level_3927547624____hygCtx___hyg_44_ = _init_l_Lean_reprLevelMVarId___redArg___closed__4____x40_Lean_Level_3927547624____hygCtx___hyg_44_();
lean_mark_persistent(l_Lean_reprLevelMVarId___redArg___closed__4____x40_Lean_Level_3927547624____hygCtx___hyg_44_);
l_Lean_reprLevelMVarId___redArg___closed__5____x40_Lean_Level_3927547624____hygCtx___hyg_44_ = _init_l_Lean_reprLevelMVarId___redArg___closed__5____x40_Lean_Level_3927547624____hygCtx___hyg_44_();
lean_mark_persistent(l_Lean_reprLevelMVarId___redArg___closed__5____x40_Lean_Level_3927547624____hygCtx___hyg_44_);
l_Lean_reprLevelMVarId___redArg___closed__6____x40_Lean_Level_3927547624____hygCtx___hyg_44_ = _init_l_Lean_reprLevelMVarId___redArg___closed__6____x40_Lean_Level_3927547624____hygCtx___hyg_44_();
lean_mark_persistent(l_Lean_reprLevelMVarId___redArg___closed__6____x40_Lean_Level_3927547624____hygCtx___hyg_44_);
l_Lean_reprLevelMVarId___redArg___closed__7____x40_Lean_Level_3927547624____hygCtx___hyg_44_ = _init_l_Lean_reprLevelMVarId___redArg___closed__7____x40_Lean_Level_3927547624____hygCtx___hyg_44_();
lean_mark_persistent(l_Lean_reprLevelMVarId___redArg___closed__7____x40_Lean_Level_3927547624____hygCtx___hyg_44_);
l_Lean_reprLevelMVarId___redArg___closed__8____x40_Lean_Level_3927547624____hygCtx___hyg_44_ = _init_l_Lean_reprLevelMVarId___redArg___closed__8____x40_Lean_Level_3927547624____hygCtx___hyg_44_();
lean_mark_persistent(l_Lean_reprLevelMVarId___redArg___closed__8____x40_Lean_Level_3927547624____hygCtx___hyg_44_);
l_Lean_reprLevelMVarId___redArg___closed__9____x40_Lean_Level_3927547624____hygCtx___hyg_44_ = _init_l_Lean_reprLevelMVarId___redArg___closed__9____x40_Lean_Level_3927547624____hygCtx___hyg_44_();
lean_mark_persistent(l_Lean_reprLevelMVarId___redArg___closed__9____x40_Lean_Level_3927547624____hygCtx___hyg_44_);
l_Lean_reprLevelMVarId___redArg___closed__10____x40_Lean_Level_3927547624____hygCtx___hyg_44_ = _init_l_Lean_reprLevelMVarId___redArg___closed__10____x40_Lean_Level_3927547624____hygCtx___hyg_44_();
lean_mark_persistent(l_Lean_reprLevelMVarId___redArg___closed__10____x40_Lean_Level_3927547624____hygCtx___hyg_44_);
l_Lean_reprLevelMVarId___redArg___closed__11____x40_Lean_Level_3927547624____hygCtx___hyg_44_ = _init_l_Lean_reprLevelMVarId___redArg___closed__11____x40_Lean_Level_3927547624____hygCtx___hyg_44_();
lean_mark_persistent(l_Lean_reprLevelMVarId___redArg___closed__11____x40_Lean_Level_3927547624____hygCtx___hyg_44_);
l_Lean_instReprLevelMVarId___closed__0 = _init_l_Lean_instReprLevelMVarId___closed__0();
lean_mark_persistent(l_Lean_instReprLevelMVarId___closed__0);
l_Lean_instReprLevelMVarId = _init_l_Lean_instReprLevelMVarId();
lean_mark_persistent(l_Lean_instReprLevelMVarId);
l_Lean_instReprLMVarId = _init_l_Lean_instReprLMVarId();
lean_mark_persistent(l_Lean_instReprLMVarId);
l_Lean_instInhabitedLMVarIdSet = _init_l_Lean_instInhabitedLMVarIdSet();
lean_mark_persistent(l_Lean_instInhabitedLMVarIdSet);
l_Lean_instEmptyCollectionLMVarIdSet = _init_l_Lean_instEmptyCollectionLMVarIdSet();
lean_mark_persistent(l_Lean_instEmptyCollectionLMVarIdSet);
l_Lean_instForInLMVarIdSetLMVarId___closed__0 = _init_l_Lean_instForInLMVarIdSetLMVarId___closed__0();
lean_mark_persistent(l_Lean_instForInLMVarIdSetLMVarId___closed__0);
l_Lean_instForInLMVarIdMapProdLMVarId___closed__0 = _init_l_Lean_instForInLMVarIdMapProdLMVarId___closed__0();
lean_mark_persistent(l_Lean_instForInLMVarIdMapProdLMVarId___closed__0);
l_Lean_Level_zero___override = _init_l_Lean_Level_zero___override();
lean_mark_persistent(l_Lean_Level_zero___override);
l_Lean_Level_data___override___closed__0 = _init_l_Lean_Level_data___override___closed__0();
l_Lean_instInhabitedLevel = _init_l_Lean_instInhabitedLevel();
lean_mark_persistent(l_Lean_instInhabitedLevel);
l_Lean_reprLevel___closed__0____x40_Lean_Level_2248933020____hygCtx___hyg_98_ = _init_l_Lean_reprLevel___closed__0____x40_Lean_Level_2248933020____hygCtx___hyg_98_();
lean_mark_persistent(l_Lean_reprLevel___closed__0____x40_Lean_Level_2248933020____hygCtx___hyg_98_);
l_Lean_reprLevel___closed__1____x40_Lean_Level_2248933020____hygCtx___hyg_98_ = _init_l_Lean_reprLevel___closed__1____x40_Lean_Level_2248933020____hygCtx___hyg_98_();
lean_mark_persistent(l_Lean_reprLevel___closed__1____x40_Lean_Level_2248933020____hygCtx___hyg_98_);
l_Lean_reprLevel___closed__2____x40_Lean_Level_2248933020____hygCtx___hyg_98_ = _init_l_Lean_reprLevel___closed__2____x40_Lean_Level_2248933020____hygCtx___hyg_98_();
lean_mark_persistent(l_Lean_reprLevel___closed__2____x40_Lean_Level_2248933020____hygCtx___hyg_98_);
l_Lean_reprLevel___closed__3____x40_Lean_Level_2248933020____hygCtx___hyg_98_ = _init_l_Lean_reprLevel___closed__3____x40_Lean_Level_2248933020____hygCtx___hyg_98_();
lean_mark_persistent(l_Lean_reprLevel___closed__3____x40_Lean_Level_2248933020____hygCtx___hyg_98_);
l_Lean_reprLevel___closed__4____x40_Lean_Level_2248933020____hygCtx___hyg_98_ = _init_l_Lean_reprLevel___closed__4____x40_Lean_Level_2248933020____hygCtx___hyg_98_();
lean_mark_persistent(l_Lean_reprLevel___closed__4____x40_Lean_Level_2248933020____hygCtx___hyg_98_);
l_Lean_reprLevel___closed__5____x40_Lean_Level_2248933020____hygCtx___hyg_98_ = _init_l_Lean_reprLevel___closed__5____x40_Lean_Level_2248933020____hygCtx___hyg_98_();
lean_mark_persistent(l_Lean_reprLevel___closed__5____x40_Lean_Level_2248933020____hygCtx___hyg_98_);
l_Lean_reprLevel___closed__6____x40_Lean_Level_2248933020____hygCtx___hyg_98_ = _init_l_Lean_reprLevel___closed__6____x40_Lean_Level_2248933020____hygCtx___hyg_98_();
lean_mark_persistent(l_Lean_reprLevel___closed__6____x40_Lean_Level_2248933020____hygCtx___hyg_98_);
l_Lean_reprLevel___closed__7____x40_Lean_Level_2248933020____hygCtx___hyg_98_ = _init_l_Lean_reprLevel___closed__7____x40_Lean_Level_2248933020____hygCtx___hyg_98_();
lean_mark_persistent(l_Lean_reprLevel___closed__7____x40_Lean_Level_2248933020____hygCtx___hyg_98_);
l_Lean_reprLevel___closed__8____x40_Lean_Level_2248933020____hygCtx___hyg_98_ = _init_l_Lean_reprLevel___closed__8____x40_Lean_Level_2248933020____hygCtx___hyg_98_();
lean_mark_persistent(l_Lean_reprLevel___closed__8____x40_Lean_Level_2248933020____hygCtx___hyg_98_);
l_Lean_reprLevel___closed__9____x40_Lean_Level_2248933020____hygCtx___hyg_98_ = _init_l_Lean_reprLevel___closed__9____x40_Lean_Level_2248933020____hygCtx___hyg_98_();
lean_mark_persistent(l_Lean_reprLevel___closed__9____x40_Lean_Level_2248933020____hygCtx___hyg_98_);
l_Lean_reprLevel___closed__10____x40_Lean_Level_2248933020____hygCtx___hyg_98_ = _init_l_Lean_reprLevel___closed__10____x40_Lean_Level_2248933020____hygCtx___hyg_98_();
lean_mark_persistent(l_Lean_reprLevel___closed__10____x40_Lean_Level_2248933020____hygCtx___hyg_98_);
l_Lean_reprLevel___closed__11____x40_Lean_Level_2248933020____hygCtx___hyg_98_ = _init_l_Lean_reprLevel___closed__11____x40_Lean_Level_2248933020____hygCtx___hyg_98_();
lean_mark_persistent(l_Lean_reprLevel___closed__11____x40_Lean_Level_2248933020____hygCtx___hyg_98_);
l_Lean_reprLevel___closed__12____x40_Lean_Level_2248933020____hygCtx___hyg_98_ = _init_l_Lean_reprLevel___closed__12____x40_Lean_Level_2248933020____hygCtx___hyg_98_();
lean_mark_persistent(l_Lean_reprLevel___closed__12____x40_Lean_Level_2248933020____hygCtx___hyg_98_);
l_Lean_reprLevel___closed__13____x40_Lean_Level_2248933020____hygCtx___hyg_98_ = _init_l_Lean_reprLevel___closed__13____x40_Lean_Level_2248933020____hygCtx___hyg_98_();
lean_mark_persistent(l_Lean_reprLevel___closed__13____x40_Lean_Level_2248933020____hygCtx___hyg_98_);
l_Lean_reprLevel___closed__14____x40_Lean_Level_2248933020____hygCtx___hyg_98_ = _init_l_Lean_reprLevel___closed__14____x40_Lean_Level_2248933020____hygCtx___hyg_98_();
lean_mark_persistent(l_Lean_reprLevel___closed__14____x40_Lean_Level_2248933020____hygCtx___hyg_98_);
l_Lean_reprLevel___closed__15____x40_Lean_Level_2248933020____hygCtx___hyg_98_ = _init_l_Lean_reprLevel___closed__15____x40_Lean_Level_2248933020____hygCtx___hyg_98_();
lean_mark_persistent(l_Lean_reprLevel___closed__15____x40_Lean_Level_2248933020____hygCtx___hyg_98_);
l_Lean_reprLevel___closed__16____x40_Lean_Level_2248933020____hygCtx___hyg_98_ = _init_l_Lean_reprLevel___closed__16____x40_Lean_Level_2248933020____hygCtx___hyg_98_();
lean_mark_persistent(l_Lean_reprLevel___closed__16____x40_Lean_Level_2248933020____hygCtx___hyg_98_);
l_Lean_reprLevel___closed__17____x40_Lean_Level_2248933020____hygCtx___hyg_98_ = _init_l_Lean_reprLevel___closed__17____x40_Lean_Level_2248933020____hygCtx___hyg_98_();
lean_mark_persistent(l_Lean_reprLevel___closed__17____x40_Lean_Level_2248933020____hygCtx___hyg_98_);
l_Lean_instReprLevel___closed__0 = _init_l_Lean_instReprLevel___closed__0();
lean_mark_persistent(l_Lean_instReprLevel___closed__0);
l_Lean_instReprLevel = _init_l_Lean_instReprLevel();
lean_mark_persistent(l_Lean_instReprLevel);
l_Lean_Level_instHashable___closed__0 = _init_l_Lean_Level_instHashable___closed__0();
lean_mark_persistent(l_Lean_Level_instHashable___closed__0);
l_Lean_Level_instHashable = _init_l_Lean_Level_instHashable();
lean_mark_persistent(l_Lean_Level_instHashable);
l_Lean_levelZero = _init_l_Lean_levelZero();
lean_mark_persistent(l_Lean_levelZero);
l_Lean_levelOne___closed__0 = _init_l_Lean_levelOne___closed__0();
lean_mark_persistent(l_Lean_levelOne___closed__0);
l_Lean_levelOne = _init_l_Lean_levelOne();
lean_mark_persistent(l_Lean_levelOne);
l_Lean_Level_mvarId_x21___closed__0 = _init_l_Lean_Level_mvarId_x21___closed__0();
lean_mark_persistent(l_Lean_Level_mvarId_x21___closed__0);
l_Lean_Level_mvarId_x21___closed__1 = _init_l_Lean_Level_mvarId_x21___closed__1();
lean_mark_persistent(l_Lean_Level_mvarId_x21___closed__1);
l_Lean_Level_mvarId_x21___closed__2 = _init_l_Lean_Level_mvarId_x21___closed__2();
lean_mark_persistent(l_Lean_Level_mvarId_x21___closed__2);
l_Lean_Level_mvarId_x21___closed__3 = _init_l_Lean_Level_mvarId_x21___closed__3();
lean_mark_persistent(l_Lean_Level_mvarId_x21___closed__3);
l_Lean_Level_instBEq___closed__0 = _init_l_Lean_Level_instBEq___closed__0();
lean_mark_persistent(l_Lean_Level_instBEq___closed__0);
l_Lean_Level_instBEq = _init_l_Lean_Level_instBEq();
lean_mark_persistent(l_Lean_Level_instBEq);
l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Level_normalize_spec__1___redArg___closed__0 = _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Level_normalize_spec__1___redArg___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Level_normalize_spec__1___redArg___closed__0);
l_Lean_Level_normalize___closed__0 = _init_l_Lean_Level_normalize___closed__0();
lean_mark_persistent(l_Lean_Level_normalize___closed__0);
l_Lean_Level_normalize___closed__1 = _init_l_Lean_Level_normalize___closed__1();
lean_mark_persistent(l_Lean_Level_normalize___closed__1);
l_Lean_Level_normalize___closed__2 = _init_l_Lean_Level_normalize___closed__2();
lean_mark_persistent(l_Lean_Level_normalize___closed__2);
l_Lean_Level_normalize___closed__3 = _init_l_Lean_Level_normalize___closed__3();
lean_mark_persistent(l_Lean_Level_normalize___closed__3);
l_Lean_Level_PP_toResult___closed__0 = _init_l_Lean_Level_PP_toResult___closed__0();
lean_mark_persistent(l_Lean_Level_PP_toResult___closed__0);
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
l_Lean_Level_PP_toResult___closed__6 = _init_l_Lean_Level_PP_toResult___closed__6();
lean_mark_persistent(l_Lean_Level_PP_toResult___closed__6);
l_Lean_Level_PP_toResult___closed__7 = _init_l_Lean_Level_PP_toResult___closed__7();
lean_mark_persistent(l_Lean_Level_PP_toResult___closed__7);
l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0 = _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0();
lean_mark_persistent(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0);
l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1 = _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1();
lean_mark_persistent(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1);
l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2 = _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2();
lean_mark_persistent(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2);
l_Lean_Level_PP_Result_format___closed__0 = _init_l_Lean_Level_PP_Result_format___closed__0();
lean_mark_persistent(l_Lean_Level_PP_Result_format___closed__0);
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
l_Lean_Level_PP_Result_quote___closed__0 = _init_l_Lean_Level_PP_Result_quote___closed__0();
lean_mark_persistent(l_Lean_Level_PP_Result_quote___closed__0);
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
l_Lean_Level_instToFormat = _init_l_Lean_Level_instToFormat();
lean_mark_persistent(l_Lean_Level_instToFormat);
l_Lean_Level_instToString___lam__0___closed__0 = _init_l_Lean_Level_instToString___lam__0___closed__0();
lean_mark_persistent(l_Lean_Level_instToString___lam__0___closed__0);
l_Lean_Level_instToString = _init_l_Lean_Level_instToString();
lean_mark_persistent(l_Lean_Level_instToString);
l_Lean_Level_instQuoteMkStr1 = _init_l_Lean_Level_instQuoteMkStr1();
lean_mark_persistent(l_Lean_Level_instQuoteMkStr1);
l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__0 = _init_l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__0();
lean_mark_persistent(l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__0);
l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__1 = _init_l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__1();
lean_mark_persistent(l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__1);
l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2 = _init_l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2();
lean_mark_persistent(l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2);
l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__0 = _init_l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__0();
lean_mark_persistent(l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__0);
l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__1 = _init_l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__1();
lean_mark_persistent(l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__1);
l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2 = _init_l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2();
lean_mark_persistent(l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2);
l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__0 = _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__0();
lean_mark_persistent(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__0);
l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__1 = _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__1();
lean_mark_persistent(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__1);
l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2 = _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2();
lean_mark_persistent(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
